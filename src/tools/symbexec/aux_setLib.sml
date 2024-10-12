structure aux_setLib =
struct

local

open HolKernel Parse boolLib bossLib;

open pred_setTheory;

open bir_symbTheory;

open birs_auxTheory;

open HolBACoreSimps;

val birs_state_ss = rewrites (type_rws ``:birs_state_t``);

  (* error handling *)
  val libname = "aux_setLib"
  val ERR = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname



in (* local *)

(* ---------------------------------------------------------------------------------- *)
(* generic fast set operations (conversions)                                          *)
(* ---------------------------------------------------------------------------------- *)
  (*
  val el_EQ_CONV = EVAL;
  *)
  fun IN_INSERT_CONV el_EQ_CONV tm =
  (
    REWRITE_CONV [pred_setTheory.NOT_IN_EMPTY] THENC
    REPEATC (CHANGED_CONV (
      (fn xyz => REWRITE_CONV [Once pred_setTheory.IN_INSERT] xyz) THENC
      IFC
        (LAND_CONV el_EQ_CONV) (* comparison of IN_INSERT (first conjunct) *)
        (REWRITE_CONV [pred_setTheory.NOT_IN_EMPTY])
        REFL))
  ) tm;

  fun INTER_INSERT_ONCE_CONV el_EQ_CONV tm =
  (
    (QCHANGED_CONV (CHANGED_CONV (fn x => REWRITE_CONV [Once pred_setTheory.INSERT_INTER, pred_setTheory.INTER_EMPTY] x))) THENC
    IFC
      (RATOR_CONV (RATOR_CONV (RAND_CONV (IN_INSERT_CONV el_EQ_CONV))))
      (REWRITE_CONV [])
      (REFL)
  ) tm;

  fun INTER_INSERT_CONV_norm el_EQ_CONV tm =
  (
    if pred_setSyntax.is_empty tm then
      REFL
    else
    IFC
      (INTER_INSERT_ONCE_CONV el_EQ_CONV)
      (fn tm =>
        (
        (if pred_setSyntax.is_empty tm then
        (REFL)
        else if pred_setSyntax.is_inter tm then
        (INTER_INSERT_CONV_norm el_EQ_CONV)
        else if pred_setSyntax.is_insert tm then
        (RAND_CONV (INTER_INSERT_CONV_norm el_EQ_CONV))
        else
        (REFL))) tm)
      (* the following causes trouble as "normal exit" if there is nothing to be done at the first call *)
      (fn tm => (print_term tm; raise Fail "unexpected here: INTER_INSERT_CONV_norm"))
  ) tm;


  (* TODO: fix this *)
  fun bvar_eq_fun_cheat tm1 tm2 = identical tm1 tm2;

  fun INTER_INSERT_CONV_cheat tm =
    let
      val (s1, s2) = pred_setSyntax.dest_inter tm
      val s1_l = pred_setSyntax.strip_set s1;
      val s2_l = pred_setSyntax.strip_set s2;
      val eq_fun = bvar_eq_fun_cheat;
      fun in_f l x = List.foldr (fn (y, b) => b orelse eq_fun x y) false l;
      val l = List.foldr (fn (x, l) => if in_f s2_l x then x::l else l) [] s1_l;
      val tm_l_set = if List.null l then pred_setSyntax.mk_empty(pred_setSyntax.eltype  tm) else pred_setSyntax.mk_set l;
    in
      mk_oracle_thm "FISHY_BIRS_FREEVARSET" ([], mk_eq (tm, tm_l_set))
    end;

  val speedcheat_INTER_INSERT_CONV = ref false;
  fun INTER_INSERT_CONV el_EQ_CONV =
    if !speedcheat_INTER_INSERT_CONV then
      INTER_INSERT_CONV_cheat
    else
      INTER_INSERT_CONV_norm el_EQ_CONV;

  (*
  fun DIFF_INSERT_CONV_cheat tm =
    let
      val (s1, s2) = pred_setSyntax.dest_diff tm
      val s1_l = pred_setSyntax.strip_set s1;
      val s2_l = pred_setSyntax.strip_set s2;
      val eq_fun = bvar_eq_fun_cheat;
      fun in_f l x = List.foldr (fn (y, b) => b orelse eq_fun x y) false l;
      val l = List.foldr (fn (x, l) => if not (in_f s2_l x) then x::l else l) [] s1_l;
      val tm_l_set = if List.null l then pred_setSyntax.mk_empty(pred_setSyntax.eltype  tm) else pred_setSyntax.mk_set l;
    in
      mk_oracle_thm "FISHY_BIRS_FREEVARSET" ([], mk_eq (tm, tm_l_set))
    end;

  val DIFF_INSERT_CONV =
    if !speedcheat then
      DIFF_INSERT_CONV_cheat
    else
      (*SIMP_CONV (std_ss++HolBACoreSimps.holBACore_ss++string_ss) [pred_setTheory.INSERT_INTER, pred_setTheory.INTER_EMPTY, pred_setTheory.IN_DIFF, pred_setTheory.IN_INSERT]*)
      EVAL;
  *)


  fun DIFF_CONV_Once el_EQ_CONV tm =
    (
      IFC
        (CHANGED_CONV (fn tm => REWRITE_CONV [Once INSERT_DIFF] tm))
        (RATOR_CONV (RATOR_CONV (RAND_CONV (pred_setLib.IN_CONV el_EQ_CONV))) THENC
        REWRITE_CONV [])
        (REFL)
    )
    tm;

  val DIFF_CONV_debug = false;
  fun DIFF_CONV el_EQ_CONV tm =
    if pred_setSyntax.is_empty tm then
      REFL tm
    else if pred_setSyntax.is_diff tm then
      if (pred_setSyntax.is_empty o fst o pred_setSyntax.dest_diff) tm then
        (if DIFF_CONV_debug then print_term tm else ();
          REWRITE_CONV [EMPTY_DIFF] tm)
      else if (pred_setSyntax.is_insert o fst o pred_setSyntax.dest_diff) tm then
        (DIFF_CONV_Once el_EQ_CONV THENC
          DIFF_CONV el_EQ_CONV) tm
      else
        raise ERR "DIFF_CONV" "unexpected1"
    else if pred_setSyntax.is_insert tm then
      RAND_CONV
        (DIFF_CONV el_EQ_CONV)
        tm
    else
      (if DIFF_CONV_debug then print_term tm else ();
      raise ERR "DIFF_CONV" "unexpected2");

  fun UNIONs_LEFT_CONV eq_EQ_CONV tm =
    (if not (pred_setSyntax.is_union tm) then 
      REFL
     else
      LAND_CONV (UNIONs_LEFT_CONV eq_EQ_CONV) THENC
      pred_setLib.UNION_CONV eq_EQ_CONV) tm;

  fun BIGUNION_CONV eq_EQ_CONV =
    REWRITE_CONV [
        BIGUNION_INSERT,
        BIGUNION_EMPTY,
        UNION_ASSOC,
        UNION_EMPTY] THENC
    (UNIONs_LEFT_CONV eq_EQ_CONV);

(* ================================================================================== *)
(* ================================================================================== *)

(* ---------------------------------------------------------------------------------- *)
(*  label set equality checker                                                      *)
(* ---------------------------------------------------------------------------------- *)
  val labelset_EQ_CONV = EVAL;

(* ---------------------------------------------------------------------------------- *)
(*  bir var set equality checker                                                      *)
(* ---------------------------------------------------------------------------------- *)
  (*
  val string_ss = rewrites (type_rws ``:string``);
  val varset_EQ_CONV = SIMP_CONV (std_ss++HolBACoreSimps.holBACore_ss++string_ss) [];
  *)
  val varset_EQ_CONV = EVAL;

(* ---------------------------------------------------------------------------------- *)
(*  birs state equality checker                                                       *)
(* ---------------------------------------------------------------------------------- *)
  val birs_state_NEQ_pc_thm = prove(``
  !bsys1 bsys2.
    (bsys1.bsst_pc <> bsys2.bsst_pc) ==>
    (bsys1 <> bsys2)
  ``,
    SIMP_TAC (std_ss++birs_state_ss) []
  );
  val birs_state_NEQ_pcond_thm = prove(``
  !bsys1 bsys2.
    (bsys1.bsst_pcond <> bsys2.bsst_pcond) ==>
    (bsys1 <> bsys2)
  ``,
    SIMP_TAC (std_ss++birs_state_ss) []
  );
  val birs_state_NEQ_status_thm = prove(``
  !bsys1 bsys2.
    (bsys1.bsst_status <> bsys2.bsst_status) ==>
    (bsys1 <> bsys2)
  ``,
    SIMP_TAC (std_ss++birs_state_ss) []
  );

  fun try_prove_birs_state_try_justify_assumptions t =
    if (is_neg o concl) t orelse
       (not o is_imp o concl) t then
      t
    else
      let
        val assmpt = (fst o dest_imp o concl) t;
        val assmpt_thm = (SIMP_CONV (std_ss++holBACore_ss++birs_state_ss) [] THENC EVAL) assmpt;

        val assmpt_new = (snd o dest_eq o concl) assmpt_thm;

        (* raise exception when the assumption turns out to be false *)
        val _ = if not (identical assmpt_new F) then () else
                raise ERR "birs_simp_try_justify_assumptions" "assumption does not hold";

        val _ = if identical assmpt_new T then () else
                raise ERR "birs_simp_try_justify_assumptions" ("failed to fix the assumption: " ^ (term_to_string assmpt));
      in
        try_prove_birs_state_try_justify_assumptions
          (REWRITE_RULE [assmpt_thm] t)
      end;

  fun try_prove_birs_state_NEQ bsys1_tm bsys2_tm =
    let
      val thms = [birs_state_NEQ_pc_thm, birs_state_NEQ_pcond_thm, birs_state_NEQ_status_thm];
      val t = hd thms;
      fun foldfun (t, r_o) =
        if isSome r_o then
          r_o
        else
          (*val t = (SPECL [bsys1_tm, bsys2_tm] t);*)
          SOME (try_prove_birs_state_try_justify_assumptions (SPECL [bsys1_tm, bsys2_tm] t))
          handle _ => NONE;
      val neq_t_o = List.foldl foldfun NONE thms;
    in
      neq_t_o
    end;

  fun birs_gen_env_check_eq env1 env2 =
    let
      val mappings1 = birs_utilsLib.get_env_mappings env1;
      val mappings2 = birs_utilsLib.get_env_mappings env2;
    in
      birs_utilsLib.list_eq_contents (fn (x,y) => pair_eq identical identical x y) mappings1 mappings2
    end;

  fun birs_state_EQ_CONV tm =
    IFC
      (CHANGED_CONV (REWRITE_CONV []))
      (fn tm => (print "syntactically equal, done!\n"; REFL tm))
      (IFC
        (fn tm =>
          let
            val (bsys1_tm, bsys2_tm) = dest_eq tm;
            val neq_t_o = try_prove_birs_state_NEQ bsys1_tm bsys2_tm;
          in
            if isSome neq_t_o then
              (*(print_thm (valOf neq_t_o);*)
              REWRITE_CONV [valOf neq_t_o] tm
            else
              (print "\ncould not show inequality of the states for pc or pcond or status, need to check the environments\n";
              NO_CONV tm)
          end)
        (fn tm => (print "unequal due to something that is not the environment, done!\n"; REFL tm))
        (fn tm =>
          let
            val (bsys1_tm, bsys2_tm) = dest_eq tm;
            val _ = if birsSyntax.birs_state_is_normform_gen false bsys1_tm andalso
                       birsSyntax.birs_state_is_normform_gen false bsys2_tm then () else
                  raise ERR "birs_state_EQ_CONV" "need two states with birs_gen_env environments";

            val get_state_env = (fn (_,env,_,_) => env) o birsSyntax.dest_birs_state;
            val is_eq = birs_gen_env_check_eq (get_state_env bsys1_tm) (get_state_env bsys2_tm);
            val _ = print (if is_eq then "states are equal\n" else "states are not equal\n");
            (* TODO: the false case might be wrong *)
            val _ = if is_eq then () else
              raise ERR "birs_state_EQ_CONV" "the states seem to be unequal, but they might be equal";
            val eq_thm = mk_oracle_thm "BIRS_STATE_EQ" ([], mk_eq (tm, if is_eq then T else F));
          in
            REWRITE_CONV [eq_thm] tm
          end))
    tm;

(* ---------------------------------------------------------------------------------- *)
(*  labelset operations                                                    *)
(* ---------------------------------------------------------------------------------- *)
  val labelset_UNION_CONV =
      (* TODO: this has to be fixed as list of address spaces that can be merged and so on...
         (can we make this only involve the block label part, not the block index?) *)
      pred_setLib.UNION_CONV labelset_EQ_CONV;

(* ---------------------------------------------------------------------------------- *)
(* faster set operations for bir variable sets (for example for: computing freevarset, symbexec composition, merging, etc) *)
(* ---------------------------------------------------------------------------------- *)
  val varset_BIGUNION_CONV =
    BIGUNION_CONV varset_EQ_CONV;

  val varset_INTER_CONV =
    INTER_INSERT_CONV varset_EQ_CONV;

  val varset_DIFF_CONV =
    DIFF_CONV varset_EQ_CONV; (* DIFF_INSERT_CONV??? *)

  (* A INTER (B DIFF C) *)
  val varset_INTER_DIFF_CONV =
    (* first DIFF *) 
    (RAND_CONV varset_DIFF_CONV) THENC
    (* then INTER *)
    varset_INTER_CONV;


(* ---------------------------------------------------------------------------------- *)
(* set operation for composition, using the state equality checker above              *)
(* ---------------------------------------------------------------------------------- *)
  (* TODO: fix this *)
  fun birs_state_eq_fun_cheat sys1 sys2 = identical sys1 sys2;

  fun DIFF_UNION_CONV_cheat tm =
    let
      val pat_tm = ``(Pi_a) DIFF {sys_b} UNION (Pi_b)``;
      val (tm_match, ty_match) = match_term pat_tm tm;

      val Pi_a  = pred_setSyntax.strip_set(subst tm_match (inst ty_match ``Pi_a:birs_state_t->bool``));
      val sys_b = subst tm_match (inst ty_match ``sys_b:birs_state_t``);
      val Pi_b  = pred_setSyntax.strip_set(subst tm_match (inst ty_match ``Pi_b:birs_state_t->bool``));

      fun in_f l x = List.foldr (fn (y, b) => b orelse birs_state_eq_fun_cheat x y) false l;
      val Pi_a_minus_b = List.filter (not o birs_state_eq_fun_cheat sys_b) Pi_a;
      fun UNION_foldfun (sys,Pi) = if in_f Pi sys then Pi else (sys::Pi);
      val Pi_c = List.foldr UNION_foldfun Pi_a_minus_b Pi_b;
      val tm_l_set = if List.null Pi_c then pred_setSyntax.mk_empty (``:birs_state_t``) else pred_setSyntax.mk_set Pi_c;
    in
      prove(``^tm = ^tm_l_set``, cheat)
    end;

  val speedcheat_stateset_diffunion = ref false;
  val birs_state_DIFF_UNION_CONV =
    if !speedcheat_stateset_diffunion then
      DIFF_UNION_CONV_cheat
    else
      REWRITE_CONV [GSYM DELETE_DEF] THENC
      LAND_CONV (pred_setLib.DELETE_CONV birs_state_EQ_CONV) THENC
      pred_setLib.UNION_CONV birs_state_EQ_CONV;

end (* local *)

end (* struct *)

(* ---------------------------------------------------------------------------------- *)
(* TEST CASE FOR: set operation for composition *)
(* ---------------------------------------------------------------------------------- *)
(*
val tm = ``
  ({^st1_tm; ^st2_tm} DIFF
    {^st1_tm})
UNION
  {^st4_tm}
``;

val tm = ``
  {<|bsst_pc := <|bpc_label := BL_Address (Imm32 2824w); bpc_index := 1|>;
     bsst_environ :=
       birs_gen_env
         [("MEM",BExp_Den (BVar "sy_MEM" (BType_Mem Bit32 Bit8)));
          ("PSR_C",BExp_Den (BVar "sy_PSR_C" (BType_Imm Bit1)));
          ("PSR_N",BExp_Den (BVar "sy_PSR_N" (BType_Imm Bit1)));
          ("PSR_V",BExp_Den (BVar "sy_PSR_V" (BType_Imm Bit1)));
          ("PSR_Z",BExp_Den (BVar "sy_PSR_Z" (BType_Imm Bit1)));
          ("R0",BExp_Den (BVar "sy_R0" (BType_Imm Bit32)));
          ("R1",BExp_Den (BVar "sy_R1" (BType_Imm Bit32)));
          ("R2",BExp_Den (BVar "sy_R2" (BType_Imm Bit32)));
          ("R3",BExp_Den (BVar "sy_R3" (BType_Imm Bit32)));
          ("R4",BExp_Den (BVar "sy_R4" (BType_Imm Bit32)));
          ("R5",BExp_Den (BVar "sy_R5" (BType_Imm Bit32)));
          ("R6",BExp_Den (BVar "sy_R6" (BType_Imm Bit32)));
          ("R7",BExp_Den (BVar "sy_R7" (BType_Imm Bit32)));
          ("R8",BExp_Den (BVar "sy_R8" (BType_Imm Bit32)));
          ("R9",BExp_Den (BVar "sy_R9" (BType_Imm Bit32)));
          ("R10",BExp_Den (BVar "sy_R10" (BType_Imm Bit32)));
          ("R11",BExp_Den (BVar "sy_R11" (BType_Imm Bit32)));
          ("R12",BExp_Den (BVar "sy_R12" (BType_Imm Bit32)));
          ("LR",BExp_Den (BVar "sy_LR" (BType_Imm Bit32)));
          ("SP_main",BExp_Den (BVar "sy_SP_main" (BType_Imm Bit32)));
          ("SP_process",BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)));
          ("ModeHandler",BExp_Den (BVar "sy_ModeHandler" (BType_Imm Bit1)));
          ("countw",BExp_Den (BVar "sy_countw" (BType_Imm Bit64)));
          ("tmp_PC",BExp_Den (BVar "sy_tmp_PC" (BType_Imm Bit32)));
          ("tmp_COND",BExp_Den (BVar "sy_tmp_COND" (BType_Imm Bit1)));
          ("tmp_MEM",BExp_Den (BVar "sy_tmp_MEM" (BType_Mem Bit32 Bit8)));
          ("tmp_PSR_C",BExp_Den (BVar "sy_tmp_PSR_C" (BType_Imm Bit1)));
          ("tmp_PSR_N",BExp_Den (BVar "sy_tmp_PSR_N" (BType_Imm Bit1)));
          ("tmp_PSR_V",BExp_Den (BVar "sy_tmp_PSR_V" (BType_Imm Bit1)));
          ("tmp_PSR_Z",BExp_Den (BVar "sy_tmp_PSR_Z" (BType_Imm Bit1)));
          ("tmp_R0",BExp_Den (BVar "sy_tmp_R0" (BType_Imm Bit32)));
          ("tmp_R1",BExp_Den (BVar "sy_tmp_R1" (BType_Imm Bit32)));
          ("tmp_R2",BExp_Den (BVar "sy_tmp_R2" (BType_Imm Bit32)));
          ("tmp_R3",BExp_Den (BVar "sy_tmp_R3" (BType_Imm Bit32)));
          ("tmp_R4",BExp_Den (BVar "sy_tmp_R4" (BType_Imm Bit32)));
          ("tmp_R5",BExp_Den (BVar "sy_tmp_R5" (BType_Imm Bit32)));
          ("tmp_R6",BExp_Den (BVar "sy_tmp_R6" (BType_Imm Bit32)));
          ("tmp_R7",BExp_Den (BVar "sy_tmp_R7" (BType_Imm Bit32)));
          ("tmp_R8",BExp_Den (BVar "sy_tmp_R8" (BType_Imm Bit32)));
          ("tmp_R9",BExp_Den (BVar "sy_tmp_R9" (BType_Imm Bit32)));
          ("tmp_R10",BExp_Den (BVar "sy_tmp_R10" (BType_Imm Bit32)));
          ("tmp_R11",BExp_Den (BVar "sy_tmp_R11" (BType_Imm Bit32)));
          ("tmp_R12",BExp_Den (BVar "sy_tmp_R12" (BType_Imm Bit32)));
          ("tmp_LR",BExp_Den (BVar "sy_tmp_LR" (BType_Imm Bit32)));
          ("tmp_SP_main",BExp_Den (BVar "sy_tmp_SP_main" (BType_Imm Bit32)));
          ("tmp_SP_process",
           BExp_Den (BVar "sy_tmp_SP_process" (BType_Imm Bit32)));
          ("tmp_ModeHandler",
           BExp_Den (BVar "sy_tmp_ModeHandler" (BType_Imm Bit1)));
          ("tmp_countw",BExp_Den (BVar "sy_tmp_countw" (BType_Imm Bit64)))];
     bsst_status := BST_Running;
     bsst_pcond :=
       BExp_BinExp BIExp_And
         (BExp_BinExp BIExp_And
            (BExp_BinPred BIExp_LessOrEqual (BExp_Const (Imm32 0xFFFFFFw))
               (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32))))
            (BExp_BinPred BIExp_Equal
               (BExp_BinExp BIExp_And
                  (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)))
                  (BExp_Const (Imm32 3w))) (BExp_Const (Imm32 0w))))
         (BExp_BinPred BIExp_LessOrEqual
            (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
            (BExp_Const (Imm64 0xFFFFFFFFFFFFFF00w)))|>} DIFF
{  <|bsst_pc := <|bpc_label := BL_Address (Imm32 2824w); bpc_index := 1|>;
     bsst_environ :=
       birs_gen_env
         [("MEM",BExp_Den (BVar "sy_MEM" (BType_Mem Bit32 Bit8)));
          ("PSR_C",BExp_Den (BVar "sy_PSR_C" (BType_Imm Bit1)));
          ("PSR_N",BExp_Den (BVar "sy_PSR_N" (BType_Imm Bit1)));
          ("PSR_V",BExp_Den (BVar "sy_PSR_V" (BType_Imm Bit1)));
          ("PSR_Z",BExp_Den (BVar "sy_PSR_Z" (BType_Imm Bit1)));
          ("R0",BExp_Den (BVar "sy_R0" (BType_Imm Bit32)));
          ("R1",BExp_Den (BVar "sy_R1" (BType_Imm Bit32)));
          ("R2",BExp_Den (BVar "sy_R2" (BType_Imm Bit32)));
          ("R3",BExp_Den (BVar "sy_R3" (BType_Imm Bit32)));
          ("R4",BExp_Den (BVar "sy_R4" (BType_Imm Bit32)));
          ("R5",BExp_Den (BVar "sy_R5" (BType_Imm Bit32)));
          ("R6",BExp_Den (BVar "sy_R6" (BType_Imm Bit32)));
          ("R7",BExp_Den (BVar "sy_R7" (BType_Imm Bit32)));
          ("R8",BExp_Den (BVar "sy_R8" (BType_Imm Bit32)));
          ("R9",BExp_Den (BVar "sy_R9" (BType_Imm Bit32)));
          ("R10",BExp_Den (BVar "sy_R10" (BType_Imm Bit32)));
          ("R11",BExp_Den (BVar "sy_R11" (BType_Imm Bit32)));
          ("R12",BExp_Den (BVar "sy_R12" (BType_Imm Bit32)));
          ("LR",BExp_Den (BVar "sy_LR" (BType_Imm Bit32)));
          ("SP_main",BExp_Den (BVar "sy_SP_main" (BType_Imm Bit32)));
          ("SP_process",BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)));
          ("ModeHandler",BExp_Den (BVar "sy_ModeHandler" (BType_Imm Bit1)));
          ("countw",BExp_Den (BVar "sy_countw" (BType_Imm Bit64)));
          ("tmp_PC",BExp_Den (BVar "sy_tmp_PC" (BType_Imm Bit32)));
          ("tmp_COND",BExp_Den (BVar "sy_tmp_COND" (BType_Imm Bit1)));
          ("tmp_MEM",BExp_Den (BVar "sy_tmp_MEM" (BType_Mem Bit32 Bit8)));
          ("tmp_PSR_C",BExp_Den (BVar "sy_tmp_PSR_C" (BType_Imm Bit1)));
          ("tmp_PSR_N",BExp_Den (BVar "sy_tmp_PSR_N" (BType_Imm Bit1)));
          ("tmp_PSR_V",BExp_Den (BVar "sy_tmp_PSR_V" (BType_Imm Bit1)));
          ("tmp_PSR_Z",BExp_Den (BVar "sy_tmp_PSR_Z" (BType_Imm Bit1)));
          ("tmp_R0",BExp_Den (BVar "sy_tmp_R0" (BType_Imm Bit32)));
          ("tmp_R1",BExp_Den (BVar "sy_tmp_R1" (BType_Imm Bit32)));
          ("tmp_R2",BExp_Den (BVar "sy_tmp_R2" (BType_Imm Bit32)));
          ("tmp_R3",BExp_Den (BVar "sy_tmp_R3" (BType_Imm Bit32)));
          ("tmp_R4",BExp_Den (BVar "sy_tmp_R4" (BType_Imm Bit32)));
          ("tmp_R5",BExp_Den (BVar "sy_tmp_R5" (BType_Imm Bit32)));
          ("tmp_R6",BExp_Den (BVar "sy_tmp_R6" (BType_Imm Bit32)));
          ("tmp_R7",BExp_Den (BVar "sy_tmp_R7" (BType_Imm Bit32)));
          ("tmp_R8",BExp_Den (BVar "sy_tmp_R8" (BType_Imm Bit32)));
          ("tmp_R9",BExp_Den (BVar "sy_tmp_R9" (BType_Imm Bit32)));
          ("tmp_R10",BExp_Den (BVar "sy_tmp_R10" (BType_Imm Bit32)));
          ("tmp_R11",BExp_Den (BVar "sy_tmp_R11" (BType_Imm Bit32)));
          ("tmp_R12",BExp_Den (BVar "sy_tmp_R12" (BType_Imm Bit32)));
          ("tmp_LR",BExp_Den (BVar "sy_tmp_LR" (BType_Imm Bit32)));
          ("tmp_SP_main",BExp_Den (BVar "sy_tmp_SP_main" (BType_Imm Bit32)));
          ("tmp_SP_process",
           BExp_Den (BVar "sy_tmp_SP_process" (BType_Imm Bit32)));
          ("tmp_ModeHandler",
           BExp_Den (BVar "sy_tmp_ModeHandler" (BType_Imm Bit1)));
          ("tmp_countw",BExp_Den (BVar "sy_tmp_countw" (BType_Imm Bit64)))];
     bsst_status := BST_Running;
     bsst_pcond :=
       BExp_BinExp BIExp_And
         (BExp_BinExp BIExp_And
            (BExp_BinPred BIExp_LessOrEqual (BExp_Const (Imm32 0xFFFFFFw))
               (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32))))
            (BExp_BinPred BIExp_Equal
               (BExp_BinExp BIExp_And
                  (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)))
                  (BExp_Const (Imm32 3w))) (BExp_Const (Imm32 0w))))
         (BExp_BinPred BIExp_LessOrEqual
            (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
            (BExp_Const (Imm64 0xFFFFFFFFFFFFFF00w)))|>} ∪
  {<|bsst_pc := <|bpc_label := BL_Address (Imm32 2824w); bpc_index := 2|>;
     bsst_environ :=
       birs_gen_env
         [("MEM",BExp_Den (BVar "sy_MEM" (BType_Mem Bit32 Bit8)));
          ("PSR_C",BExp_Den (BVar "sy_PSR_C" (BType_Imm Bit1)));
          ("PSR_N",BExp_Den (BVar "sy_PSR_N" (BType_Imm Bit1)));
          ("PSR_V",BExp_Den (BVar "sy_PSR_V" (BType_Imm Bit1)));
          ("PSR_Z",BExp_Den (BVar "sy_PSR_Z" (BType_Imm Bit1)));
          ("R0",BExp_Den (BVar "sy_R0" (BType_Imm Bit32)));
          ("R1",BExp_Den (BVar "sy_R1" (BType_Imm Bit32)));
          ("R2",BExp_Den (BVar "sy_R2" (BType_Imm Bit32)));
          ("R3",BExp_Den (BVar "sy_R3" (BType_Imm Bit32)));
          ("R4",BExp_Den (BVar "sy_R4" (BType_Imm Bit32)));
          ("R5",BExp_Den (BVar "sy_R5" (BType_Imm Bit32)));
          ("R6",BExp_Den (BVar "sy_R6" (BType_Imm Bit32)));
          ("R7",BExp_Den (BVar "sy_R7" (BType_Imm Bit32)));
          ("R8",BExp_Den (BVar "sy_R8" (BType_Imm Bit32)));
          ("R9",BExp_Den (BVar "sy_R9" (BType_Imm Bit32)));
          ("R10",BExp_Den (BVar "sy_R10" (BType_Imm Bit32)));
          ("R11",BExp_Den (BVar "sy_R11" (BType_Imm Bit32)));
          ("R12",BExp_Den (BVar "sy_R12" (BType_Imm Bit32)));
          ("LR",BExp_Den (BVar "sy_LR" (BType_Imm Bit32)));
          ("SP_main",BExp_Den (BVar "sy_SP_main" (BType_Imm Bit32)));
          ("SP_process",BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)));
          ("ModeHandler",BExp_Den (BVar "sy_ModeHandler" (BType_Imm Bit1)));
          ("countw",BExp_Den (BVar "sy_countw" (BType_Imm Bit64)));
          ("tmp_PC",BExp_Den (BVar "sy_tmp_PC" (BType_Imm Bit32)));
          ("tmp_COND",BExp_Den (BVar "sy_tmp_COND" (BType_Imm Bit1)));
          ("tmp_MEM",BExp_Den (BVar "sy_tmp_MEM" (BType_Mem Bit32 Bit8)));
          ("tmp_PSR_C",BExp_Den (BVar "sy_tmp_PSR_C" (BType_Imm Bit1)));
          ("tmp_PSR_N",BExp_Den (BVar "sy_tmp_PSR_N" (BType_Imm Bit1)));
          ("tmp_PSR_V",BExp_Den (BVar "sy_tmp_PSR_V" (BType_Imm Bit1)));
          ("tmp_PSR_Z",BExp_Den (BVar "sy_tmp_PSR_Z" (BType_Imm Bit1)));
          ("tmp_R0",BExp_Den (BVar "sy_tmp_R0" (BType_Imm Bit32)));
          ("tmp_R1",BExp_Den (BVar "sy_tmp_R1" (BType_Imm Bit32)));
          ("tmp_R2",BExp_Den (BVar "sy_tmp_R2" (BType_Imm Bit32)));
          ("tmp_R3",BExp_Den (BVar "sy_tmp_R3" (BType_Imm Bit32)));
          ("tmp_R4",BExp_Den (BVar "sy_tmp_R4" (BType_Imm Bit32)));
          ("tmp_R5",BExp_Den (BVar "sy_tmp_R5" (BType_Imm Bit32)));
          ("tmp_R6",BExp_Den (BVar "sy_tmp_R6" (BType_Imm Bit32)));
          ("tmp_R7",BExp_Den (BVar "sy_tmp_R7" (BType_Imm Bit32)));
          ("tmp_R8",BExp_Den (BVar "sy_tmp_R8" (BType_Imm Bit32)));
          ("tmp_R9",BExp_Den (BVar "sy_tmp_R9" (BType_Imm Bit32)));
          ("tmp_R10",BExp_Den (BVar "sy_tmp_R10" (BType_Imm Bit32)));
          ("tmp_R11",BExp_Den (BVar "sy_tmp_R11" (BType_Imm Bit32)));
          ("tmp_R12",BExp_Den (BVar "sy_tmp_R12" (BType_Imm Bit32)));
          ("tmp_LR",BExp_Den (BVar "sy_tmp_LR" (BType_Imm Bit32)));
          ("tmp_SP_main",BExp_Den (BVar "sy_tmp_SP_main" (BType_Imm Bit32)));
          ("tmp_SP_process",
           BExp_Den (BVar "sy_tmp_SP_process" (BType_Imm Bit32)));
          ("tmp_ModeHandler",
           BExp_Den (BVar "sy_tmp_ModeHandler" (BType_Imm Bit1)));
          ("tmp_countw",BExp_Den (BVar "sy_tmp_countw" (BType_Imm Bit64)))];
     bsst_status := BST_Running;
     bsst_pcond :=
       BExp_BinExp BIExp_And
         (BExp_BinExp BIExp_And
            (BExp_BinPred BIExp_LessOrEqual (BExp_Const (Imm32 0xFFFFFFw))
               (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32))))
            (BExp_BinPred BIExp_Equal
               (BExp_BinExp BIExp_And
                  (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)))
                  (BExp_Const (Imm32 3w))) (BExp_Const (Imm32 0w))))
         (BExp_BinPred BIExp_LessOrEqual
            (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
            (BExp_Const (Imm64 0xFFFFFFFFFFFFFF00w)))|>}``;

birs_state_DIFF_UNION_CONV tm;
*)

(* ---------------------------------------------------------------------------------- *)
(*  TEST CASE FOR: state equality checker                                             *)
(* ---------------------------------------------------------------------------------- *)
(*
fun stx_tm addr_tm index_tm symbname_tm = ``
  <|bsst_pc := <|bpc_label := BL_Address (Imm32 (^addr_tm)); bpc_index := (^index_tm)|>;
     bsst_environ :=
       birs_gen_env
         [("MEM",BExp_Den (BVar "sy_MEM" (BType_Mem Bit32 Bit8)));
          ("PSR_C",BExp_Den (BVar "sy_PSR_C" (BType_Imm Bit1)));
          ("PSR_N",BExp_Den (BVar "sy_PSR_N" (BType_Imm Bit1)));
          ("PSR_V",BExp_Den (BVar "sy_PSR_V" (BType_Imm Bit1)));
          ("PSR_Z",BExp_Den (BVar (^symbname_tm) (BType_Imm Bit1)))];
     bsst_status := BST_Running;
     bsst_pcond :=
         (BExp_BinPred BIExp_LessOrEqual
            (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
            (BExp_Const (Imm64 0xFFFFFFFFFFFFFF00w)))|>
``;
val st1_tm = stx_tm ``2824w:word32`` ``1:num`` ``"sy_PSR_Z"``;
val st2_tm = stx_tm ``2824w:word32`` ``2:num`` ``"sy_PSR_Z"``;
val st3_tm = stx_tm ``2825w:word32`` ``1:num`` ``"sy_PSR_A"``;
val st4_tm = stx_tm ``2824w:word32`` ``3:num`` ``"sy_PSR_Z"``;

val st_eq_1_tm = ``^st1_tm = ^st1_tm``;
val st_eq_2_tm = ``^st1_tm = ^st2_tm``;
val st_eq_3_tm = ``^st1_tm = ^st3_tm``;
val st_eq_4_tm = ``^st2_tm = ^st3_tm``;

val tm = st_eq_2_tm;
val tm = st_eq_3_tm;
val tm = st_eq_4_tm;

birs_state_EQ_CONV st_eq_1_tm
birs_state_EQ_CONV st_eq_2_tm
birs_state_EQ_CONV st_eq_3_tm
birs_state_EQ_CONV st_eq_4_tm
*)

(* ---------------------------------------------------------------------------------- *)
(* TEST CASE FOR:                                                                     *)
(* faster set operations for bir variable sets (for computing freevarset, symbexec composition, merging, etc) *)
(* also for sets of symbolic BIR states                                               *)
(* ---------------------------------------------------------------------------------- *)
(*
EVAL tm

           val birs_exps_of_senv_CONV = (
    debug_conv2 THENC
    REPEATC (CHANGED_CONV (
      (fn x => REWRITE_CONV [Once birs_exps_of_senv_COMP_thm] x) THENC
      (SIMP_CONV (std_ss) []) THENC
      (ONCE_DEPTH_CONV ( (PAT_CONV ``\A. if A then B else (C)`` (REWRITE_CONV [pred_setTheory.COMPONENT] THENC SIMP_CONV std_ss [pred_setTheory.IN_INSERT])))) THENC
      SIMP_CONV (std_ss) []
    ))
  );

           val birs_symb_symbols_CONV = (
    SIMP_CONV std_ss [birs_symb_symbols_thm] THENC
    SIMP_CONV (std_ss++birs_state_ss) [] THENC
    SIMP_CONV (std_ss) [birs_exps_of_senv_thm]
    (*(PAT_CONV ``\A. IMAGE bir_vars_of_exp A`` birs_exps_of_senv_CONV)*)
  );
           val conv = birs_symb_symbols_CONV (*THENC EVAL*);
           val conv_ = computeLib.RESTR_EVAL_CONV [``birs_symb_symbols``] THENC conv;
*)

(*
val tm = ``
{BVar "sy_MEM" (BType_Mem Bit32 Bit8); BVar "sy_PSR_C" (BType_Imm Bit1);
    BVar "sy_PSR_N" (BType_Imm Bit1); BVar "sy_PSR_V" (BType_Imm Bit1);
    BVar "sy_PSR_Z" (BType_Imm Bit1); BVar "sy_R0" (BType_Imm Bit32);
    BVar "sy_R1" (BType_Imm Bit32); BVar "sy_R2" (BType_Imm Bit32);
    BVar "sy_R3" (BType_Imm Bit32); BVar "sy_R4" (BType_Imm Bit32);
    BVar "sy_R5" (BType_Imm Bit32); BVar "sy_R6" (BType_Imm Bit32);
    BVar "sy_R7" (BType_Imm Bit32); BVar "sy_R8" (BType_Imm Bit32);
    BVar "sy_R9" (BType_Imm Bit32); BVar "sy_R10" (BType_Imm Bit32);
    BVar "sy_R11" (BType_Imm Bit32); BVar "sy_R12" (BType_Imm Bit32);
    BVar "sy_LR" (BType_Imm Bit32); BVar "sy_SP_main" (BType_Imm Bit32);
    BVar "sy_SP_process" (BType_Imm Bit32);
    BVar "sy_ModeHandler" (BType_Imm Bit1);
    BVar "sy_countw" (BType_Imm Bit64); BVar "sy_tmp_PC" (BType_Imm Bit32);
    BVar "sy_tmp_COND" (BType_Imm Bit1);
    BVar "sy_tmp_MEM" (BType_Mem Bit32 Bit8);
    BVar "sy_tmp_PSR_C" (BType_Imm Bit1);
    BVar "sy_tmp_PSR_N" (BType_Imm Bit1);
    BVar "sy_tmp_PSR_V" (BType_Imm Bit1);
    BVar "sy_tmp_PSR_Z" (BType_Imm Bit1); BVar "sy_tmp_R0" (BType_Imm Bit32);
    BVar "sy_tmp_R1" (BType_Imm Bit32); BVar "sy_tmp_R2" (BType_Imm Bit32);
    BVar "sy_tmp_R3" (BType_Imm Bit32); BVar "sy_tmp_R4" (BType_Imm Bit32);
    BVar "sy_tmp_R5" (BType_Imm Bit32); BVar "sy_tmp_R6" (BType_Imm Bit32);
    BVar "sy_tmp_R7" (BType_Imm Bit32); BVar "sy_tmp_R8" (BType_Imm Bit32);
    BVar "sy_tmp_R9" (BType_Imm Bit32); BVar "sy_tmp_R10" (BType_Imm Bit32);
    BVar "sy_tmp_R11" (BType_Imm Bit32); BVar "sy_tmp_R12" (BType_Imm Bit32);
    BVar "sy_tmp_LR" (BType_Imm Bit32);
    BVar "sy_tmp_SP_main" (BType_Imm Bit32);
    BVar "sy_tmp_SP_process" (BType_Imm Bit32);
    BVar "sy_tmp_ModeHandler" (BType_Imm Bit1);
    BVar "sy_tmp_countw" (BType_Imm Bit64)} ∩
   ({BVar "sy_countw" (BType_Imm Bit64);
     BVar "sy_SP_process" (BType_Imm Bit32);
     BVar "sy_MEM" (BType_Mem Bit32 Bit8); BVar "sy_PSR_C" (BType_Imm Bit1);
     BVar "sy_PSR_N" (BType_Imm Bit1); BVar "sy_PSR_V" (BType_Imm Bit1);
     BVar "sy_PSR_Z" (BType_Imm Bit1); BVar "sy_R0" (BType_Imm Bit32);
     BVar "sy_R1" (BType_Imm Bit32); BVar "sy_R2" (BType_Imm Bit32);
     BVar "sy_R3" (BType_Imm Bit32); BVar "sy_R4" (BType_Imm Bit32);
     BVar "sy_R5" (BType_Imm Bit32); BVar "sy_R6" (BType_Imm Bit32);
     BVar "sy_R7" (BType_Imm Bit32); BVar "sy_R8" (BType_Imm Bit32);
     BVar "sy_R9" (BType_Imm Bit32); BVar "sy_R10" (BType_Imm Bit32);
     BVar "sy_R11" (BType_Imm Bit32); BVar "sy_R12" (BType_Imm Bit32);
     BVar "sy_LR" (BType_Imm Bit32); BVar "sy_SP_main" (BType_Imm Bit32);
     BVar "sy_SP_process" (BType_Imm Bit32);
     BVar "sy_ModeHandler" (BType_Imm Bit1);
     BVar "sy_countw" (BType_Imm Bit64); BVar "sy_tmp_PC" (BType_Imm Bit32);
     BVar "sy_tmp_COND" (BType_Imm Bit1);
     BVar "sy_tmp_MEM" (BType_Mem Bit32 Bit8);
     BVar "sy_tmp_PSR_C" (BType_Imm Bit1);
     BVar "sy_tmp_PSR_N" (BType_Imm Bit1);
     BVar "sy_tmp_PSR_V" (BType_Imm Bit1);
     BVar "sy_tmp_PSR_Z" (BType_Imm Bit1);
     BVar "sy_tmp_R0" (BType_Imm Bit32); BVar "sy_tmp_R1" (BType_Imm Bit32);
     BVar "sy_tmp_R2" (BType_Imm Bit32); BVar "sy_tmp_R3" (BType_Imm Bit32);
     BVar "sy_tmp_R4" (BType_Imm Bit32); BVar "sy_tmp_R5" (BType_Imm Bit32);
     BVar "sy_tmp_R6" (BType_Imm Bit32); BVar "sy_tmp_R7" (BType_Imm Bit32);
     BVar "sy_tmp_R8" (BType_Imm Bit32); BVar "sy_tmp_R9" (BType_Imm Bit32);
     BVar "sy_tmp_R10" (BType_Imm Bit32);
     BVar "sy_tmp_R11" (BType_Imm Bit32);
     BVar "sy_tmp_R12" (BType_Imm Bit32); BVar "sy_tmp_LR" (BType_Imm Bit32);
     BVar "sy_tmp_SP_main" (BType_Imm Bit32);
     BVar "sy_tmp_SP_process" (BType_Imm Bit32);
     BVar "sy_tmp_ModeHandler" (BType_Imm Bit1);
     BVar "sy_tmp_countw" (BType_Imm Bit64);
     BVar "sy_countw" (BType_Imm Bit64);
     BVar "sy_SP_process" (BType_Imm Bit32);
     BVar "sy_MEM" (BType_Mem Bit32 Bit8); BVar "sy_PSR_C" (BType_Imm Bit1);
     BVar "sy_PSR_N" (BType_Imm Bit1); BVar "sy_PSR_V" (BType_Imm Bit1);
     BVar "sy_PSR_Z" (BType_Imm Bit1); BVar "sy_R0" (BType_Imm Bit32);
     BVar "sy_R1" (BType_Imm Bit32); BVar "sy_R2" (BType_Imm Bit32);
     BVar "sy_R3" (BType_Imm Bit32); BVar "sy_R4" (BType_Imm Bit32);
     BVar "sy_R5" (BType_Imm Bit32); BVar "sy_R6" (BType_Imm Bit32);
     BVar "sy_R7" (BType_Imm Bit32); BVar "sy_R8" (BType_Imm Bit32);
     BVar "sy_R9" (BType_Imm Bit32); BVar "sy_R10" (BType_Imm Bit32);
     BVar "sy_R11" (BType_Imm Bit32); BVar "sy_R12" (BType_Imm Bit32);
     BVar "sy_LR" (BType_Imm Bit32); BVar "sy_SP_main" (BType_Imm Bit32);
     BVar "sy_SP_process" (BType_Imm Bit32);
     BVar "sy_ModeHandler" (BType_Imm Bit1);
     BVar "sy_countw" (BType_Imm Bit64); BVar "sy_tmp_PC" (BType_Imm Bit32);
     BVar "sy_tmp_COND" (BType_Imm Bit1);
     BVar "sy_tmp_MEM" (BType_Mem Bit32 Bit8);
     BVar "sy_tmp_PSR_C" (BType_Imm Bit1);
     BVar "sy_tmp_PSR_N" (BType_Imm Bit1);
     BVar "sy_tmp_PSR_V" (BType_Imm Bit1);
     BVar "sy_tmp_PSR_Z" (BType_Imm Bit1);
     BVar "sy_tmp_R0" (BType_Imm Bit32); BVar "sy_tmp_R1" (BType_Imm Bit32);
     BVar "sy_tmp_R2" (BType_Imm Bit32); BVar "sy_tmp_R3" (BType_Imm Bit32);
     BVar "sy_tmp_R4" (BType_Imm Bit32); BVar "sy_tmp_R5" (BType_Imm Bit32);
     BVar "sy_tmp_R6" (BType_Imm Bit32); BVar "sy_tmp_R7" (BType_Imm Bit32);
     BVar "sy_tmp_R8" (BType_Imm Bit32); BVar "sy_tmp_R9" (BType_Imm Bit32);
     BVar "sy_tmp_R10" (BType_Imm Bit32);
     BVar "sy_tmp_R11" (BType_Imm Bit32);
     BVar "sy_tmp_R12" (BType_Imm Bit32); BVar "sy_tmp_LR" (BType_Imm Bit32);
     BVar "sy_tmp_SP_main" (BType_Imm Bit32);
     BVar "sy_tmp_SP_process" (BType_Imm Bit32);
     BVar "sy_tmp_ModeHandler" (BType_Imm Bit1);
     BVar "sy_tmp_countw" (BType_Imm Bit64)} DIFF
    {BVar "sy_countw" (BType_Imm Bit64);
     BVar "sy_MEM" (BType_Mem Bit32 Bit8); BVar "sy_PSR_C" (BType_Imm Bit1);
     BVar "sy_PSR_N" (BType_Imm Bit1); BVar "sy_PSR_V" (BType_Imm Bit1);
     BVar "sy_PSR_Z" (BType_Imm Bit1); BVar "sy_R0" (BType_Imm Bit32);
     BVar "sy_R1" (BType_Imm Bit32); BVar "sy_R2" (BType_Imm Bit32);
     BVar "sy_R3" (BType_Imm Bit32); BVar "sy_R4" (BType_Imm Bit32);
     BVar "sy_R5" (BType_Imm Bit32); BVar "sy_R6" (BType_Imm Bit32);
     BVar "sy_R7" (BType_Imm Bit32); BVar "sy_R8" (BType_Imm Bit32);
     BVar "sy_R9" (BType_Imm Bit32); BVar "sy_R10" (BType_Imm Bit32);
     BVar "sy_R11" (BType_Imm Bit32); BVar "sy_R12" (BType_Imm Bit32);
     BVar "sy_LR" (BType_Imm Bit32); BVar "sy_SP_main" (BType_Imm Bit32);
     BVar "sy_SP_process" (BType_Imm Bit32);
     BVar "sy_ModeHandler" (BType_Imm Bit1);
     BVar "sy_countw" (BType_Imm Bit64); BVar "sy_tmp_PC" (BType_Imm Bit32);
     BVar "sy_tmp_COND" (BType_Imm Bit1);
     BVar "sy_tmp_MEM" (BType_Mem Bit32 Bit8);
     BVar "sy_tmp_PSR_C" (BType_Imm Bit1);
     BVar "sy_tmp_PSR_N" (BType_Imm Bit1);
     BVar "sy_tmp_PSR_V" (BType_Imm Bit1);
     BVar "sy_tmp_PSR_Z" (BType_Imm Bit1);
     BVar "sy_tmp_R0" (BType_Imm Bit32); BVar "sy_tmp_R1" (BType_Imm Bit32);
     BVar "sy_tmp_R2" (BType_Imm Bit32); BVar "sy_tmp_R3" (BType_Imm Bit32);
     BVar "sy_tmp_R4" (BType_Imm Bit32); BVar "sy_tmp_R5" (BType_Imm Bit32);
     BVar "sy_tmp_R6" (BType_Imm Bit32); BVar "sy_tmp_R7" (BType_Imm Bit32);
     BVar "sy_tmp_R8" (BType_Imm Bit32); BVar "sy_tmp_R9" (BType_Imm Bit32);
     BVar "sy_tmp_R10" (BType_Imm Bit32);
     BVar "sy_tmp_R11" (BType_Imm Bit32);
     BVar "sy_tmp_R12" (BType_Imm Bit32); BVar "sy_tmp_LR" (BType_Imm Bit32);
     BVar "sy_tmp_SP_main" (BType_Imm Bit32);
     BVar "sy_tmp_SP_process" (BType_Imm Bit32);
     BVar "sy_tmp_ModeHandler" (BType_Imm Bit1);
     BVar "sy_tmp_countw" (BType_Imm Bit64)})
``;

val tm = ``
{BVar "sy_MEM" (BType_Mem Bit32 Bit8); BVar "sy_PSR_C" (BType_Imm Bit1);BVar "sy_countw" (BType_Imm Bit64);
    BVar "sy_PSR_N" (BType_Imm Bit1); BVar "sy_PSR_V" (BType_Imm Bit1)} ∩
   ({BVar "sy_MEM" (BType_Mem Bit32 Bit8); BVar "sy_PSR_C" (BType_Imm Bit1);BVar "sy_countw" (BType_Imm Bit64);
    BVar "sy_PSR_N" (BType_Imm Bit1); BVar "sy_PSR_V" (BType_Imm Bit1)} DIFF
    {
     BVar "sy_tmp_ModeHandler" (BType_Imm Bit1);
     BVar "sy_tmp_countw" (BType_Imm Bit64)})
``;

val tm = (snd o dest_comb o fst o dest_comb o snd o dest_eq o concl o REWRITE_CONV [REWRITE_RULE [Once pred_setTheory.INTER_COMM] pred_setTheory.DIFF_INTER]) tm;
val tm = (snd o dest_comb o snd o dest_eq o concl o REWRITE_CONV [Once (prove(``
!s t g.
g INTER (s DIFF t) =
s INTER (g DIFF t)
``,
(*REWRITE_RULE [Once pred_setTheory.INTER_COMM] pred_setTheory.DIFF_INTER*)
METIS_TAC [pred_setTheory.INTER_COMM, pred_setTheory.DIFF_INTER]
))]) tm;

++pred_setSimps.PRED_SET_ss
val char_ss = rewrites (type_rws ``:char``);



val tm = ``
BVar "sy_countw" (BType_Imm Bit64) ∈
       {BVar "sy_MEM" (BType_Mem Bit32 Bit8);
        BVar "sy_PSR_C" (BType_Imm Bit1); BVar "sy_PSR_N" (BType_Imm Bit1);
        BVar "sy_PSR_V" (BType_Imm Bit1); BVar "sy_PSR_Z" (BType_Imm Bit1);
        BVar "sy_R0" (BType_Imm Bit32); BVar "sy_R1" (BType_Imm Bit32);
        BVar "sy_R2" (BType_Imm Bit32); BVar "sy_R3" (BType_Imm Bit32);
        BVar "sy_R4" (BType_Imm Bit32); BVar "sy_R5" (BType_Imm Bit32);
        BVar "sy_R6" (BType_Imm Bit32); BVar "sy_R7" (BType_Imm Bit32);
        BVar "sy_R8" (BType_Imm Bit32); BVar "sy_R9" (BType_Imm Bit32);
        BVar "sy_R10" (BType_Imm Bit32); BVar "sy_R11" (BType_Imm Bit32);
        BVar "sy_R12" (BType_Imm Bit32); BVar "sy_LR" (BType_Imm Bit32);
        BVar "sy_SP_main" (BType_Imm Bit32);
        BVar "sy_SP_process" (BType_Imm Bit32);
        BVar "sy_ModeHandler" (BType_Imm Bit1);
        BVar "sy_countw" (BType_Imm Bit64);
        BVar "sy_tmp_PC" (BType_Imm Bit32);
        BVar "sy_tmp_COND" (BType_Imm Bit1);
        BVar "sy_tmp_MEM" (BType_Mem Bit32 Bit8);
        BVar "sy_tmp_PSR_C" (BType_Imm Bit1);
        BVar "sy_tmp_PSR_N" (BType_Imm Bit1);
        BVar "sy_tmp_PSR_V" (BType_Imm Bit1);
        BVar "sy_tmp_PSR_Z" (BType_Imm Bit1);
        BVar "sy_tmp_R0" (BType_Imm Bit32);
        BVar "sy_tmp_R1" (BType_Imm Bit32);
        BVar "sy_tmp_R2" (BType_Imm Bit32);
        BVar "sy_tmp_R3" (BType_Imm Bit32);
        BVar "sy_tmp_R4" (BType_Imm Bit32);
        BVar "sy_tmp_R5" (BType_Imm Bit32);
        BVar "sy_tmp_R6" (BType_Imm Bit32);
        BVar "sy_tmp_R7" (BType_Imm Bit32);
        BVar "sy_tmp_R8" (BType_Imm Bit32);
        BVar "sy_tmp_R9" (BType_Imm Bit32);
        BVar "sy_tmp_R10" (BType_Imm Bit32);
        BVar "sy_tmp_R11" (BType_Imm Bit32);
        BVar "sy_tmp_R12" (BType_Imm Bit32);
        BVar "sy_tmp_LR" (BType_Imm Bit32);
        BVar "sy_tmp_SP_main" (BType_Imm Bit32);
        BVar "sy_tmp_SP_process" (BType_Imm Bit32);
        BVar "sy_tmp_ModeHandler" (BType_Imm Bit1);
        BVar "sy_tmp_countw" (BType_Imm Bit64)}
``;


*)
(*
val tm = ``
  EMPTY DIFF
     {
        BVar "sy_tmp_R0" (BType_Imm Bit32);
        BVar "sy_tmp_R1" (BType_Imm Bit32);
        BVar "sy_tmp_R2" (BType_Imm Bit32)
     }
``;

val tm = ``
  {
        BVar "sy_tmp_R0" (BType_Imm Bit32);
        BVar "sy_tmp_R1" (BType_Imm Bit32);
        BVar "sy_tmp_R2" (BType_Imm Bit32);
        BVar "sy_tmp_R3" (BType_Imm Bit32);
        BVar "sy_tmp_R4" (BType_Imm Bit32);
        BVar "sy_tmp_R5" (BType_Imm Bit32)
  } DIFF
     EMPTY
``;

val tm = ``
  {
        BVar "sy_tmp_R0" (BType_Imm Bit32);
        BVar "sy_tmp_R1" (BType_Imm Bit32);
        BVar "sy_tmp_R2" (BType_Imm Bit32);
        BVar "sy_tmp_R3" (BType_Imm Bit32);
        BVar "sy_tmp_R4" (BType_Imm Bit32);
        BVar "sy_tmp_R5" (BType_Imm Bit32)
  } DIFF
     {
        BVar "sy_tmp_R0" (BType_Imm Bit32);
        BVar "sy_tmp_R1" (BType_Imm Bit32);
        BVar "sy_tmp_R2" (BType_Imm Bit32)
     }
``;

val tm = ``
{
        BVar "sy_tmp_R0" (BType_Imm Bit32);
        BVar "sy_tmp_R1" (BType_Imm Bit32);
        BVar "sy_tmp_R4" (BType_Imm Bit32);
        BVar "sy_tmp_R5" (BType_Imm Bit32);
        BVar "sy_tmp_R8" (BType_Imm Bit32)
} INTER (^tm)
``; (* R4 and R5 *)
*)
