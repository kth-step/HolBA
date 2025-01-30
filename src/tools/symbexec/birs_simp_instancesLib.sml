structure birs_simp_instancesLib =
struct

local

  open HolKernel Parse boolLib bossLib;
  open bir_exp_typecheckLib;
  open birs_simpLib;
  
  open bir_symb_simpTheory;

  (* error handling *)
  val libname = "bir_simp_instancesLib"
  val ERR = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname

in (* local *)

  val birs_storeelim_oracle_speed = ref true;

(*
val (mexp1, stores1) = dest_BExp_Store_list bexp_stores [];
val bexp_stores_ = mk_BExp_Store_list (mexp1, stores1);
identical bexp_stores bexp_stores_;
*)
 local
  open bir_expSyntax;
 in
  fun dest_BExp_Store_list bexp acc =
    if not (is_BExp_Store bexp) then
      (bexp, acc)
    else
      let
        val (expm, expad, endi, expv) = dest_BExp_Store bexp;
      in
        dest_BExp_Store_list expm ((expad, endi, expv)::acc)
      end;
  fun mk_BExp_Store_list (expm, []) = expm
    | mk_BExp_Store_list (expm, (expad, endi, expv)::l) =
      mk_BExp_Store_list (mk_BExp_Store (expm, expad, endi, expv), l);
 end

(*
val bexp_stores = ``
                  (BExp_Store
                     ^bexp_stores
                     (BExp_BinExp BIExp_Plus
                        (BExp_BinExp BIExp_Minus
                           (BExp_Den (BVar "sy_x2" (BType_Imm Bit64)))
                           (BExp_Const (Imm64 33w))) (BExp_Const (Imm64 25w)))
                     BEnd_LittleEndian
                     (BExp_Den (BVar "sy_x1" (BType_Imm Bit64))))
``;
val (mexp1, stores1) = dest_BExp_Store_list bexp_stores [];
val store_to_check = List.last stores1;
val stores2 = List.take(stores1, List.length stores1 - 1);

filter (not o stores_match pcond store_to_check) stores2

val bexp = bexp_stores;
val simp_tm = birs_simp_gen_term pcond bexp;
birs_simp_load simp_tm;
*)

  local
    open bir_expSyntax;
  in
    fun is_load_tm_fun tm = is_BExp_Load tm;
    val is_store_tm_fun = is_BExp_Store;
  end

  local
    open bir_exp_typecheckLib;
  in
  (*
  val (expad1:term, endi1:term, expv1:term) = store_to_check;
  *)
  
  fun stores_match pcond store1 store2 =
    let
      val (expad1, endi1, expv1) = store1;
      val (expad2, endi2, expv2) = store2;
      val endi_eq = identical endi1 endi2;
      val vsz_eq = identical (get_type_of_bexp expv1) (get_type_of_bexp expv2);
      
      val imp_tm = birsSyntax.mk_birs_exp_imp (pcond, bslSyntax.beq (expad1, expad2));
      val ad_is_eq = isSome (birs_utilsLib.check_imp_tm imp_tm);
    in
      endi_eq andalso
      vsz_eq andalso
      ad_is_eq
    end;
  end

  (* find single store elimination *)
  fun birs_simp_find_store_elimination_rev pcond_tm stores1 =
    let
      (*
      now operated on reversed store order
      val store_to_check = List.last stores1;
      val stores = List.take(stores1, List.length stores1 - 1);
      *)
      val store_to_check = hd stores1;
      val stores = tl stores1;

      val filtered_stores = filter (not o stores_match pcond_tm store_to_check) stores;
    in
      store_to_check::filtered_stores(*@[store_to_check]*)
    end;

  (* find store eliminations recursivly *)
  fun birs_simp_find_store_eliminations_rev pcond_tm [] = []
    | birs_simp_find_store_eliminations_rev pcond_tm stores1 =
    let
      val stores_new = birs_simp_find_store_elimination_rev pcond_tm stores1;
    in
      (hd stores_new)::(birs_simp_find_store_eliminations_rev pcond_tm (tl stores_new))
    end;

  (* store elimination *)
  fun birs_simp_try_store recurse (simp_tm, simp_thm_o) =
    if isSome simp_thm_o then simp_thm_o else
    let
      open birsSyntax;
      val (pcond_tm, symbexp_tm, _) = dest_birs_simplification simp_tm;
    in
      if not (is_store_tm_fun symbexp_tm) then NONE else
      let
        val (mexp, stores1) = dest_BExp_Store_list symbexp_tm [];

        val find_store_eliminations_fun =
          if recurse then
            birs_simp_find_store_eliminations_rev
          else
            birs_simp_find_store_elimination_rev;
        val stores_new = (List.rev o find_store_eliminations_fun pcond_tm o List.rev) stores1;
        val num_removed = List.length stores1 - List.length stores_new;
        val _ = if num_removed = 0 then () else print ("removed stores: " ^ (Int.toString num_removed) ^ "\n");
      in
        if num_removed = 0 then NONE else
        let
          val symbexp_1_tm = mk_BExp_Store_list (mexp, stores_new);
          val simp_tm_goal = mk_birs_simplification (pcond_tm, symbexp_tm, symbexp_1_tm);
          val simp_thm =
            if !birs_storeelim_oracle_speed then
              aux_moveawayLib.mk_oracle_preserve_tags [] "BIRS_MEM_STORE_SPEEDCHEAT" simp_tm_goal
            else
              let
                val simp_thm_o = birs_utilsLib.check_simplification_tm simp_tm_goal;
              in
                valOf simp_thm_o
                handle _ => (print "checking of simplification failed\n"; raise ERR "birs_simp_try_store" "check_simplification_tm failed")
              end;
        in
          SOME simp_thm
        end
      end
    end
    handle _ => raise ERR "birs_simp_try_store" "store simplification failed";
  val birs_simp_try_store = fn x => Profile.profile "birs_simp_try_store" (birs_simp_try_store x);

  fun birs_simp_try_load (bypass_thms, match_thms, subexp_thms) simp_args =
    let
      (*
      val _ = print "\nsimp_try_load::\n";
      val _ = print_term (fst simp_args);
      val _ = simp_try_fold_gen_debug_mode := true;
      *)
      (* bypass as many stores as possible, try to match the load with a store *)
      val simp_fun_mem_load = simp_try_repeat_gen (simp_try_fold_gen birs_simp_try_pcond (bypass_thms@match_thms));
      val thm_o = simp_fun_mem_load simp_args;
      (*val _ = if isSome thm_o then print_thm (valOf thm_o) else ();
      val _ = simp_try_fold_gen_debug_mode := false;*)
    in
      thm_o
    end;
  val birs_simp_try_load = fn x => Profile.profile "birs_simp_try_load" (birs_simp_try_load x);

(* ----------------------------------------------------------------------------------- *)
  (* combination function of the two kinds above (direct simplification) *)
  (* - try plain simplification *)
  (* - try implied simplification *)
(*
  val simp_inst_tm = birs_simp_gen_term pcond bexp;
*)
  fun birs_simp_try_direct (plain_thms, pcond_thms) =
    simp_try_list_gen [
      simp_try_fold_gen (birs_simp_try_plain (SOME EVAL)) plain_thms,
      simp_try_fold_gen birs_simp_try_pcond pcond_thms
    ];

(*
  val simp_tm = birs_simp_gen_term pcond bexp;
  birs_simp_regular (birs_simp_exp_plain_thms, birs_simp_exp_pcond_thms, birs_simp_exp_subexp_thms) simp_tm;
*)


(*
  4 types of simplification functions, and recursive rinse&repeat
    - plain (only basic assumptions as typing or some numbers or other basic equalities)
    - pcond (starts out with basic assumptions, justify pcond implication with smt solver)
    - direct (first try all plain, then try pcond)
    - subexp (go into subexpression and then try direct, no recusion into subexpressions of subexpressions)

  recursive rinse&repeat
    - try direct, then try subexp, one simplification = one iteration, repeat until no more possible
  special treatment of store sequences, and load operations
*)
  val birs_simp_regular_recurse_mode = ref false;
  val birs_simp_regular_recurse_depth = ref 10;
  fun birs_simp_regular (plain_thms, pcond_thms, subexp_thms) load_simp_fun store_simp_fun_o simp_arg =
    let
      val base_simp_fun = birs_simp_try_direct (plain_thms, pcond_thms);
      val store_simp_fun =
        case store_simp_fun_o of
           SOME x => x
         | NONE => base_simp_fun;
      val direct_simp_fun = 
        simp_try_apply_match
          [(is_load_tm_fun, load_simp_fun),
           (is_store_tm_fun, store_simp_fun),
           (fn _ => true, base_simp_fun)];

      (* - try direct simplification *)
      (* - try direct simplification in subexpressions *)
      (* - repeat the above until can't find anything to simplify *)

      (* only go two expressions deep *)
      fun simp_subexp_gen_fun f1 f2 =
        simp_try_list_gen
          [f1,
           simp_try_fold_gen (birs_simp_try_subexp f2) subexp_thms];
      val simp_subexp_fun =
        simp_subexp_gen_fun direct_simp_fun (simp_subexp_gen_fun direct_simp_fun direct_simp_fun);
      (* go further *)
      val simp_recurse_fun =
        birs_simp_try_recurse true (SOME (!birs_simp_regular_recurse_depth)) subexp_thms (direct_simp_fun);

      val simp_fun =
        if !birs_simp_regular_recurse_mode then
          simp_recurse_fun
        else
          simp_subexp_fun;
    in
      simp_try_repeat_gen simp_fun simp_arg
    end;
  val birs_simp_regular = fn x => fn y => fn z => Profile.profile "birs_simp_regular" (birs_simp_regular x y z);

  fun birs_simp_gen pre_simp extra_thms simp_thms_tuple load_thms_tuple recurse_o =
    let
      val load_simp_fun = birs_simp_try_load load_thms_tuple;
      val store_simp_fun_o =
        if isSome recurse_o then
          SOME (birs_simp_try_store (valOf recurse_o))
        else
          NONE;

      val simp_fun = birs_simp_regular simp_thms_tuple load_simp_fun store_simp_fun_o;
    in
      simp_try_list_cont_gen [
        simp_fun,
        simp_try_mk_gen pre_simp,
        simp_try_fold_gen (birs_simp_try_plain (SOME EVAL)) extra_thms
      ]
    end;

(* ----------------------------------------------------------------------------------- *)

  fun plain_thms include_64 include_32 extra_thms =
    (if include_64 then
       [birs_simplification_Plus_Minus_Const64_thm,
        birs_simplification_Minus_Minus_Const64_thm,
        birs_simplification_Minus_Plus_Const64_thm,
        birs_simplification_Plus_Plus_Const64_thm]
     else
       [])@
    (if include_32 then
       [birs_simplification_Plus_Minus_Const32_thm,
        birs_simplification_Minus_Minus_Const32_thm,
        birs_simplification_Minus_Plus_Const32_thm,
        birs_simplification_Plus_Plus_Const32_thm]
     else
       [])@
    (extra_thms)@
    [birs_simplification_Plus_Const64_thm,
     birs_simplification_Minus_Const64_thm,
     birs_simplification_Plus_Const32_thm,
     birs_simplification_Minus_Const32_thm,
     birs_simplification_UnsignedCast_LowCast_Twice_thm];

  fun pcond_thms mem_64 mem_32 riscv cm0 =
    (if mem_64 then
       (CONJUNCTS birs_simplification_Mem_Bypass_64_8_thm)@
       (CONJUNCTS birs_simplification_Mem_Match_64_8_thm)
     else
       [])@
    (if mem_32 then
       (CONJUNCTS birs_simplification_Mem_Bypass_32_8_thm)@
       (CONJUNCTS birs_simplification_Mem_Match_32_8_thm)
     else
       [])@
    [birs_simplification_IfThenElse_T_thm,
     birs_simplification_IfThenElse_F_thm]@
    (if riscv then
       [birs_simplification_SignedLowCast3264_RV_thm,
        birs_simplification_LSB0_And64_RV_thm]
     else
       [])@
    (if cm0 then
       [birs_simplification_And_Minus_CM0_thm]
     else
       []);

  val subexp_cast_thms =
    [birs_simplification_LowCast_thm,
     birs_simplification_SignedCast_thm,
     birs_simplification_UnsignedCast_thm];

  val subexp_thms =
    [birs_simplification_Store_addr_thm,
     birs_simplification_Load_addr_thm,
     birs_simplification_Plus_right_thm,
     birs_simplification_Plus_left_thm,
     birs_simplification_Minus_left_thm,
     birs_simplification_And_left_thm]@
    subexp_cast_thms;

(* ----------------------------------------------------------------------------------- *)

  val simp_thms_tuple_subexp_extra = ref ([]:thm list);
  fun simp_thms_tuple include_64 include_32 mem_64 mem_32 riscv cm0 extra_thms = (plain_thms include_64 include_32 extra_thms, pcond_thms mem_64 mem_32 riscv cm0, (!simp_thms_tuple_subexp_extra)@subexp_thms);

  fun load_thms_tuple mem_64 mem_32 =
      ((if mem_64 then
          CONJUNCTS birs_simplification_Mem_Bypass_64_8_thm
        else
          [])@
       (if mem_32 then
          CONJUNCTS birs_simplification_Mem_Bypass_32_8_thm
        else
          []),
       (if mem_64 then
          CONJUNCTS birs_simplification_Mem_Match_64_8_thm
        else
          [])@
       (if mem_32 then
          CONJUNCTS birs_simplification_Mem_Match_32_8_thm
        else
          []),
       subexp_cast_thms);

  val birs_simp_default_core_exp_simp =
    let
      val include_64 = true;
      val include_32 = true;
      val mem_64 = false;
      val mem_32 = false;
      val riscv = false;
      val cm0 = false;
    in
      birs_simp_gen
        birs_simp_ID_fun
        []
        (simp_thms_tuple include_64 include_32 mem_64 mem_32 riscv cm0 [])
        (load_thms_tuple mem_64 mem_32)
        NONE
    end;

  val birs_simp_default_core_exp_multistoreelim_simp =
    let
      val include_64 = true;
      val include_32 = true;
      val mem_64 = false;
      val mem_32 = false;
      val riscv = false;
      val cm0 = false;
    in
      birs_simp_gen
        birs_simp_ID_fun
        []
        (simp_thms_tuple include_64 include_32 mem_64 mem_32 riscv cm0 [])
        (load_thms_tuple mem_64 mem_32)
        (SOME true)
    end;

  fun birs_simp_default_riscv_gen use_store_cheater pre_simp extra_thms =
    let
      val include_64 = true;
      val include_32 = false;
      val mem_64 = true;
      val mem_32 = false;
      val riscv = true;
      val cm0 = false;
    in
      birs_simp_gen
        pre_simp
        extra_thms
        (simp_thms_tuple include_64 include_32 mem_64 mem_32 riscv cm0 [])
        (load_thms_tuple mem_64 mem_32)
        (if use_store_cheater then SOME false else NONE)
    end;

  fun birs_simp_default_armcm0_gen use_store_cheater pre_simp extra_thms =
    let
      val include_64 = true;
      val include_32 = true;
      val mem_64 = false;
      val mem_32 = true;
      val riscv = false;
      val cm0 = true;
    in
      birs_simp_gen
        pre_simp
        extra_thms
        (simp_thms_tuple include_64 include_32 mem_64 mem_32 riscv cm0 [])
        (load_thms_tuple mem_64 mem_32)
        (if use_store_cheater then SOME false else NONE)
    end;
  
  val birs_simp_default_riscv = birs_simp_default_riscv_gen false birs_simp_ID_fun [];
  val birs_simp_default_armcm0 = birs_simp_default_armcm0_gen false birs_simp_ID_fun [];

end (* local *)

end (* struct *)
