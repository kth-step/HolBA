structure birs_simp_instancesLib =
struct

local

  open HolKernel Parse boolLib bossLib;
  open bir_exp_typecheckLib;
  open bir_smtLib;
  open birs_simpLib;
  
  open bir_symb_simpTheory;

  (* error handling *)
  val libname = "bir_simp_instancesLib"
  val ERR = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname

in (* local *)

(* ----------------------------------------------------------------------------------- *)
(* ----------------------------------------------------------------------------------- *)
(* ----------------------------------------------------------------------------------- *)
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
  open optionSyntax;
  open bir_typing_expSyntax;
  open bslSyntax;
in
 fun get_type_of_bexp tm =
  let
    val thm = type_of_bir_exp_DIRECT_CONV (mk_type_of_bir_exp tm);
  in
    (dest_some o snd o dest_eq o concl) thm
  end
  handle _ => raise ERR "get_type_of_bexp" "not well-typed expression or other issue";

 (*
 val (expad1:term, endi1:term, expv1:term) = store_to_check;
 *)
 fun stores_match pcond store1 store2 =
  let
    val (expad1, endi1, expv1) = store1;
    val (expad2, endi2, expv2) = store2;
    val endi_eq = identical endi1 endi2;
    val vsz_eq = identical (get_type_of_bexp expv1) (get_type_of_bexp expv2);
    
    val imp_bexp_tm = bor (bnot pcond, beq (expad1, expad2));
    val ad_is_eq = bir_smt_check_taut false imp_bexp_tm;
  in
    endi_eq andalso
    vsz_eq andalso
    ad_is_eq
  end;
end

fun birs_simp_store_cheater simp_tm =
    let
      (* TODO: constant propagation on the address/value *)
      (* try to remove another store (only one) *)
      (* TODO: this implementation is only crude and not correct *)
      open birsSyntax;
      val (pcond_tm, symbexp_tm, _) = dest_birs_simplification simp_tm;
      val (mexp, stores1) = dest_BExp_Store_list symbexp_tm [];
      val store_to_check = List.last stores1;
      val stores = List.take(stores1, List.length stores1 - 1);
      val filtered_stores = filter (not o stores_match pcond_tm store_to_check) stores;
      val symbexp_1_tm = mk_BExp_Store_list (mexp, filtered_stores@[store_to_check]);
      val num_removed = List.length stores - List.length filtered_stores;
      val _ = if num_removed = 0 then () else print ("removed stores: " ^ (Int.toString num_removed) ^ "\n");
    in
      prove(mk_birs_simplification (pcond_tm, symbexp_tm, symbexp_1_tm), cheat)
    end;
(* ----------------------------------------------------------------------------------- *)
(* ----------------------------------------------------------------------------------- *)

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

  val birs_simp_exp_plain_thms = List.rev (
    [birs_simplification_UnsignedCast_LowCast_Twice_thm,

     birs_simplification_Plus_Const64_thm,

     birs_simplification_Plus_Plus_Const64_thm,
     birs_simplification_Minus_Plus_Const64_thm,
     birs_simplification_Minus_Minus_Const64_thm,
     birs_simplification_Plus_Minus_Const64_thm(*,

     birs_simplification_Plus_Plus_Const32_thm,
     birs_simplification_Minus_Plus_Const32_thm,
     birs_simplification_Minus_Minus_Const32_thm,
     birs_simplification_Plus_Minus_Const32_thm*)]
  );

  val birs_simp_exp_pcond_thms = List.rev (
    [(*birs_simplification_And_Minus_CM0_thm,*)
     birs_simplification_LSB0_And64_RV_thm,
     birs_simplification_SignedLowCast3264_RV_thm,

     birs_simplification_IfThenElse_T_thm,
     birs_simplification_IfThenElse_F_thm]@
    (CONJUNCTS birs_simplification_Mem_Match_64_8_thm)@
    (CONJUNCTS birs_simplification_Mem_Bypass_64_8_thm)(*@
    (CONJUNCTS birs_simplification_Mem_Match_32_8_thm)@
    (CONJUNCTS birs_simplification_Mem_Bypass_32_8_thm)*)
  );

  val birs_simp_exp_subexp_thms = List.rev (
    [birs_simplification_UnsignedCast_thm,
     birs_simplification_SignedCast_thm,
     birs_simplification_LowCast_thm,
     birs_simplification_Minus_left_thm,
     birs_simplification_Plus_left_thm,
     birs_simplification_Plus_right_thm,
     birs_simplification_Load_addr_thm,
     birs_simplification_Store_addr_thm]
  );

  val simp_thms_tuple = (birs_simp_exp_plain_thms, birs_simp_exp_pcond_thms, birs_simp_exp_subexp_thms);

      val cast_thms =
        [birs_simplification_UnsignedCast_thm,
         birs_simplification_SignedCast_thm,
         birs_simplification_LowCast_thm];
  val load_thms_tuple =
      (CONJUNCTS birs_simplification_Mem_Bypass_64_8_thm,
       CONJUNCTS birs_simplification_Mem_Match_64_8_thm,
       cast_thms);

(* ----------------------------------------------------------------------------------- *)

  (* combination function of the two kinds above (direct simplification) *)
  (* - try plain simplification *)
  (* - try implied simplification *)
(*
  val simp_inst_tm = birs_simp_gen_term pcond bexp;
*)
  fun birs_simp_try_direct (plain_thms, pcond_thms) =
    simp_try_list_gen [
      simp_try_fold_gen birs_simp_try_plain plain_thms,
      simp_try_fold_gen birs_simp_try_pcond pcond_thms
    ];

  (* TODO: need to keep simplifying using the three functions above repeatedly until not possible to simplify anymore *)
  (* - try direct simplification *)
  (* - try direct simplification in subexpressions *)
  (* - repeat the above until can't find anything to simplify *)
(*
  val simp_tm = birs_simp_gen_term pcond bexp;
  birs_simp_repeat (birs_simp_exp_plain_thms, birs_simp_exp_pcond_thms, birs_simp_exp_subexp_thms) simp_tm;
*)
  fun birs_simp_repeat (plain_thms, pcond_thms, subexp_thms) simp_tm =
    let
      val direct_simp_fun = birs_simp_try_direct (plain_thms, pcond_thms);
      val simp_fun = simp_try_list_gen
          [direct_simp_fun,
           simp_try_fold_gen (birs_simp_try_subexp direct_simp_fun) subexp_thms];
    in
      simp_try_apply_gen (simp_try_repeat_gen simp_fun) simp_tm
    end;

  fun birs_simp_regular simp_thms_tuple simp_tm = birs_simp_repeat simp_thms_tuple simp_tm;
  val birs_simp_regular = fn x => Profile.profile "birs_simp_regular" (birs_simp_regular x);

  fun birs_simp_load (bypass_thms, match_thms, subexp_thms) simp_tm =
    let
      (* bypass as many stores as possible, try to match the load with a store *)
      (* TODO: constant propagation on the address *)
      val simp_fun_mem_load = simp_try_repeat_gen (simp_try_fold_gen birs_simp_try_pcond (bypass_thms@match_thms));
      val simp_fun = simp_try_list_gen
        [simp_try_fold_gen (birs_simp_try_subexp simp_fun_mem_load) subexp_thms,
         simp_fun_mem_load];
      val simp_thm = simp_try_apply_gen simp_fun simp_tm;
      (*val _ = (print_term o get_rarg o concl) simp_thm;*)
    in
      simp_thm
    end;
  val birs_simp_load = fn x => Profile.profile "birs_simp_load" (birs_simp_load x);
  
  fun birs_simp_store simp_tm = birs_simp_store_cheater simp_tm;
  val birs_simp_store = Profile.profile "birs_simp_store" birs_simp_store;

  local
    open bir_expSyntax;
  in
    (* loads are more complicated, in this case we have a cast, and within there is a load *)
    fun is_load_tm_fun tm = is_BExp_Load tm orelse (is_BExp_Cast tm andalso (is_BExp_Load o (fn (_,x,_) => x) o dest_BExp_Cast) tm);
    val is_store_tm_fun = is_BExp_Store;
  end

  fun birs_simp_gen simp_tm =
    let
        val start_exp_tm = get_larg simp_tm;
        val use_store_cheater = false;

        val simp_apply_fun =
          if is_load_tm_fun start_exp_tm then (
            print "simplifying a load\n";
            birs_simp_load load_thms_tuple
          ) else if is_store_tm_fun start_exp_tm then (
            print "simplifying a store\n";
            if use_store_cheater then
              birs_simp_store
            else
              birs_simp_regular simp_thms_tuple
          ) else (
            print "it is neither a load nor a store\n";
            birs_simp_regular simp_thms_tuple
          );
    in
      simp_apply_fun simp_tm
    end;

  val birs_simp_default_riscv =
    birs_simp_gen;

end (* local *)

end (* struct *)
