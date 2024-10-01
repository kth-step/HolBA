structure bir_vars_ofLib =
struct

local

open HolKernel Parse boolLib bossLib;

open bir_typing_expTheory;
open bir_typing_expSyntax;
open birsSyntax;

open HolBACoreSimps;

open birs_auxTheory;
val birs_state_ss = rewrites (type_rws ``:birs_state_t``);

  (* error handling *)
  val libname = "bir_vars_ofLib"
  val ERR = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname

in (* local *)

(* ---------------------------------------------------------------------------------- *)
(*  variables of bir expressions                                                      *)
(* ---------------------------------------------------------------------------------- *)
  (* TODO: can probably speed this up by extending the caching into the evaluation of variables subexpressions, like in the function type_of_bir_exp_DIRECT_CONV,
       but only relevant for handling of bigger expressions *)
  fun bir_vars_of_exp_DIRECT_CONV tm =
    let
     val _ = if is_bir_vars_of_exp tm then () else
               raise ERR "bir_vars_of_exp_DIRECT_CONV" "cannot handle term";
    in
      (SIMP_CONV (std_ss++holBACore_ss) [] THENC EVAL) tm
    end;
  val bir_vars_of_exp_DIRECT_CONV = aux_moveawayLib.wrap_cache_result Term.compare bir_vars_of_exp_DIRECT_CONV;

  val bir_vars_of_exp_CONV =
    birs_auxLib.GEN_match_conv (is_bir_vars_of_exp) bir_vars_of_exp_DIRECT_CONV;

(* ---------------------------------------------------------------------------------- *)
(*  symbols of set of symbolic states                                                 *)
(* ---------------------------------------------------------------------------------- *)
  (*
  val debug_conv = (fn tm => (print_term tm; raise Fail "abcdE!!!"));
  val debug_conv2 = (fn tm => (if true then print ".\n" else print_term tm; REFL tm));
  *)

  (*
  REPEATC
        (SIMP_CONV (std_ss) []) THENC
        (ONCE_DEPTH_CONV ( (PAT_CONV ``\A. if A then B else (C)`` (REWRITE_CONV [pred_setTheory.COMPONENT] THENC SIMP_CONV std_ss [pred_setTheory.IN_INSERT])))) THENC
        SIMP_CONV (std_ss) []
  *)

  (* ................................................ *)

  fun string_in_set_CONV tm =
  (
    REWRITE_CONV [pred_setTheory.NOT_IN_EMPTY] THENC
    REPEATC (CHANGED_CONV ((fn xyz => REWRITE_CONV [Once pred_setTheory.IN_INSERT] xyz) THENC
      IFC
        (RATOR_CONV EVAL)
        (BETA_CONV THENC REWRITE_CONV [pred_setTheory.NOT_IN_EMPTY])
        REFL))
  ) tm;

  fun birs_exps_of_senv_COMP_ONCE_CONV tm =
  (
    (QCHANGED_CONV (CHANGED_CONV (fn x => REWRITE_CONV [Once birs_exps_of_senv_COMP_thm] x))) THENC
    IFC
      (RATOR_CONV (RATOR_CONV (RAND_CONV (string_in_set_CONV))))
      (REWRITE_CONV [])
      (REFL)
  ) tm;

  (* TODO: add proper exceptions/exception messages if the unexpected happens... *)
  fun birs_exps_of_senv_COMP_CONV_cheat tm =
    let
      val (s1, s2_l) = strip_comb tm;
      val _ = if ((fst o dest_const) s1) = "birs_exps_of_senv_COMP" then () else
              raise ERR "birs_exps_of_senv_COMP_CONV_cheat" "constant not found";
      val _ = if length s2_l = 2 then () else
              raise ERR "birs_exps_of_senv_COMP_CONV_cheat" "application not right";
      val initvarset = List.nth(s2_l, 0);
      val _ = if pred_setSyntax.is_empty initvarset then () else
              raise ERR "birs_exps_of_senv_COMP_CONV_cheat" "must start with empty set";

      val tm_map = List.nth(s2_l, 1);

      fun eq_fun tm1 tm2 = tm1 = tm2;
      fun in_f l x = List.foldr (fn (y, b) => b orelse eq_fun x y) false l;

      val base_term = ``(K NONE):string -> bir_exp_t option``;
      fun collectfun excl acc tm_map =
        if identical tm_map base_term then acc else
        if not (combinSyntax.is_update_comb tm_map) then raise ERR "birs_exps_of_senv_COMP_CONV_cheat" "should not happen" else
        let
          val ((mem_upd_k, mem_upd_v), tm_map_sub) = combinSyntax.dest_update_comb tm_map;
          val mem_upd_v_v = optionSyntax.dest_some mem_upd_v;
          val mem_upd_k_s = stringSyntax.fromHOLstring mem_upd_k;
          val k_s_is_excl = in_f excl mem_upd_k_s;
          val new_acc  = if k_s_is_excl then (acc)  else ([mem_upd_v_v]@acc);
          val new_excl = if k_s_is_excl then (excl) else ([mem_upd_k_s]@excl);
        in
          collectfun new_excl new_acc tm_map_sub
        end;

  (*
      val s1_l = pred_setSyntax.strip_set s1;
      val s2_l = pred_setSyntax.strip_set s2;
  List.foldr (fn (x, l) => if not (in_f s2_l x) then x::l else l) [] s1_l;
  *)

      val l = collectfun [] [] tm_map;
      val tm_l_set = if List.null l then pred_setSyntax.mk_empty(``:bir_exp_t``) else pred_setSyntax.mk_set l;
    in
      mk_oracle_thm "FISHY_BIRS_BIR_SENV_VARSET" ([], mk_eq (tm, tm_l_set))
    end;

  fun birs_exps_of_senv_COMP_CONV_norm tm =
  (
  (*(fn tm => (if false then print ".\n" else print_term tm; REFL tm)) THENC*)
  (* (fn tm => (if true then print ".\n" else print_term tm; REFL tm)) THENC *)
  (*
    if pred_setSyntax.is_empty tm then
      REFL
    else
  *)
    IFC
      (birs_exps_of_senv_COMP_ONCE_CONV)
      (TRY_CONV (fn tm => (
        if pred_setSyntax.is_empty tm then
          REFL
        else if pred_setSyntax.is_insert tm then
          RAND_CONV birs_exps_of_senv_COMP_CONV_norm
        else
          birs_exps_of_senv_COMP_CONV_norm
      ) tm))
      (fn tm => (print_term tm; raise Fail "unexpected here: birs_exps_of_senv_COMP_CONV_norm"))
  ) tm;

  val speedcheat_expsofenv = ref false;
  val birs_exps_of_senv_COMP_CONV =
    if !speedcheat_expsofenv then
      birs_exps_of_senv_COMP_CONV_cheat
    else
      birs_exps_of_senv_COMP_CONV_norm;


  fun birs_exps_of_senv_CONV tm =
  (
  (*
  (fn tm => (if false then print ".\n" else print_term tm; REFL tm)) THENC
  *)
    REWRITE_CONV [birs_exps_of_senv_thm] THENC
    ((*TRY_CONV*) birs_exps_of_senv_COMP_CONV)
  ) tm;

  fun birs_symb_symbols_DIRECT_CONV tm =
    if not (is_birs_symb_symbols tm) then
      raise ERR "birs_symb_symbols_DIRECT_CONV" "cannot handle term"
    else
    (
      SIMP_CONV std_ss [birs_gen_env_thm, birs_gen_env_NULL_thm] THENC
      SIMP_CONV (std_ss++birs_state_ss) [birs_symb_symbols_thm] THENC

      birs_auxLib.GEN_match_conv is_birs_exps_of_senv birs_exps_of_senv_CONV THENC

      REWRITE_CONV [pred_setTheory.IMAGE_INSERT, pred_setTheory.IMAGE_EMPTY] THENC
      bir_vars_of_exp_CONV THENC

      RATOR_CONV (RAND_CONV (REWRITE_CONV [pred_setTheory.BIGUNION_INSERT, pred_setTheory.BIGUNION_EMPTY])) THENC

      REWRITE_CONV [Once pred_setTheory.UNION_COMM] THENC
      REWRITE_CONV [pred_setTheory.UNION_ASSOC, pred_setTheory.INSERT_UNION_EQ, pred_setTheory.UNION_EMPTY]
    ) tm;
  val birs_symb_symbols_DIRECT_CONV = aux_moveawayLib.wrap_cache_result Term.compare birs_symb_symbols_DIRECT_CONV;

  val birs_symb_symbols_CONV =
    birs_auxLib.GEN_match_conv is_birs_symb_symbols birs_symb_symbols_DIRECT_CONV;


(* ---------------------------------------------------------------------------------- *)
(*  symbols of set of symbolic bir states                                             *)
(* ---------------------------------------------------------------------------------- *)
  fun birs_symb_symbols_set_DIRECT_CONV tm =
    if not (is_birs_symb_symbols_set tm) then
      raise ERR "birs_symb_symbols_set_DIRECT_CONV" "cannot handle term"
    else
    (
      REWRITE_CONV [
        birs_rulesTheory.birs_symb_symbols_set_def,
        pred_setTheory.IMAGE_INSERT,
        pred_setTheory.IMAGE_EMPTY] THENC
      birs_symb_symbols_CONV THENC
      (* now have A UNION B UNION C UNION ... *)

      aux_setLib.varset_BIGUNION_CONV
    ) tm;
  val birs_symb_symbols_set_DIRECT_CONV = aux_moveawayLib.wrap_cache_result Term.compare birs_symb_symbols_set_DIRECT_CONV;

  val birs_symb_symbols_set_CONV =
    birs_auxLib.GEN_match_conv is_birs_symb_symbols_set birs_symb_symbols_set_DIRECT_CONV;


(* ---------------------------------------------------------------------------------- *)
(*  free symbols of execution structure (sys, L, Pi)                                  *)
(* ---------------------------------------------------------------------------------- *)
  fun birs_freesymbs_DIRECT_CONV tm =
    if not (is_birs_freesymbs tm) then
      raise ERR "birs_freesymbs_DIRECT_CONV" "cannot handle term"
    else
    (
      REWRITE_CONV [birs_rulesTheory.birs_freesymbs_def] THENC
      LAND_CONV (birs_symb_symbols_set_DIRECT_CONV) THENC
      RAND_CONV (birs_symb_symbols_DIRECT_CONV) THENC
      aux_setLib.varset_DIFF_CONV
    ) tm;
  val birs_freesymbs_DIRECT_CONV = aux_moveawayLib.wrap_cache_result Term.compare birs_freesymbs_DIRECT_CONV;

  val birs_freesymbs_CONV =
    birs_auxLib.GEN_match_conv is_birs_freesymbs birs_freesymbs_DIRECT_CONV;

end (* local *)

end (* struct *)

(* ---------------------------------------------------------------------------------- *)
(* TEST CASE FOR: symbols of set of symbolic states *)
(* ---------------------------------------------------------------------------------- *)
(* COPIED FROM TRANSFER-TEST (and modified) *)
(*
val tm = ``
birs_symb_symbols
     <|bsst_pc := <|bpc_label := BL_Address (Imm32 2824w); bpc_index := 0|>;
       bsst_environ := (K NONE)⦇
             "MEM" ↦ SOME (BExp_Den (BVar "sy_MEM" (BType_Mem Bit32 Bit8)));
             "PSR_C" ↦ SOME (BExp_Den (BVar "sy_PSR_C" (BType_Imm Bit1)));
             "PSR_N" ↦ SOME (BExp_Den (BVar "sy_PSR_N" (BType_Imm Bit1)));
             "PSR_V" ↦ SOME (BExp_Den (BVar "sy_PSR_V" (BType_Imm Bit1)));
             "PSR_Z" ↦ SOME (BExp_Den (BVar "sy_PSR_Z" (BType_Imm Bit1)));
             "R0" ↦ SOME (BExp_Den (BVar "sy_R0" (BType_Imm Bit32)));
             "R1" ↦ SOME (BExp_Den (BVar "sy_R1" (BType_Imm Bit32)));
             "R2" ↦ SOME (BExp_Den (BVar "sy_R2" (BType_Imm Bit32)));
             "R3" ↦ SOME (BExp_Den (BVar "sy_R3" (BType_Imm Bit32)));
             "R4" ↦ SOME (BExp_Den (BVar "sy_R4" (BType_Imm Bit32)));
             "R5" ↦ SOME (BExp_Den (BVar "sy_R5" (BType_Imm Bit32)));
             "R6" ↦ SOME (BExp_Den (BVar "sy_R6" (BType_Imm Bit32)));
             "R7" ↦ SOME (BExp_Den (BVar "sy_R7" (BType_Imm Bit32)));
             "R8" ↦ SOME (BExp_Den (BVar "sy_R8" (BType_Imm Bit32)));
             "R9" ↦ SOME (BExp_Den (BVar "sy_R9" (BType_Imm Bit32)));
             "R10" ↦ SOME (BExp_Den (BVar "sy_R10" (BType_Imm Bit32)));
             "R11" ↦ SOME (BExp_Den (BVar "sy_R11" (BType_Imm Bit32)));
             "R12" ↦ SOME (BExp_Den (BVar "sy_R12" (BType_Imm Bit32)));
             "LR" ↦ SOME (BExp_Den (BVar "sy_LR" (BType_Imm Bit32)));
             "SP_main" ↦
               SOME (BExp_Den (BVar "sy_SP_main" (BType_Imm Bit32)));
             "SP_process" ↦
               SOME (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)));
             "ModeHandler" ↦
               SOME (BExp_Den (BVar "sy_ModeHandler" (BType_Imm Bit1)));
             "countw" ↦ SOME (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)));
             "tmp_PC" ↦ SOME (BExp_Den (BVar "sy_tmp_PC" (BType_Imm Bit32)));
             "tmp_COND" ↦
               SOME (BExp_Den (BVar "sy_tmp_COND" (BType_Imm Bit1)));
             "tmp_MEM" ↦
               SOME (BExp_Den (BVar "sy_tmp_MEM" (BType_Mem Bit32 Bit8)));
             "tmp_PSR_C" ↦
               SOME (BExp_Den (BVar "sy_tmp_PSR_C" (BType_Imm Bit1)));
             "tmp_PSR_N" ↦
               SOME (BExp_Den (BVar "sy_tmp_PSR_N" (BType_Imm Bit1)));
             "tmp_PSR_V" ↦
               SOME (BExp_Den (BVar "sy_tmp_PSR_V" (BType_Imm Bit1)));
             "tmp_PSR_Z" ↦
               SOME (BExp_Den (BVar "sy_tmp_PSR_Z" (BType_Imm Bit1)));
             "tmp_R0" ↦ SOME (BExp_Den (BVar "sy_tmp_R0" (BType_Imm Bit32)));
             "tmp_R1" ↦ SOME (BExp_Den (BVar "sy_tmp_R1" (BType_Imm Bit32)));
             "tmp_R2" ↦ SOME (BExp_Den (BVar "sy_tmp_R2" (BType_Imm Bit32)));
             "tmp_R3" ↦ SOME (BExp_Den (BVar "sy_tmp_R3" (BType_Imm Bit32)));
             "tmp_R4" ↦ SOME (BExp_Den (BVar "sy_tmp_R4" (BType_Imm Bit32)));
             "tmp_R5" ↦ SOME (BExp_Den (BVar "sy_tmp_R5" (BType_Imm Bit32)));
             "tmp_R6" ↦ SOME (BExp_Den (BVar "sy_tmp_R6" (BType_Imm Bit32)));
             "tmp_R7" ↦ SOME (BExp_Den (BVar "sy_tmp_R7" (BType_Imm Bit32)));
             "tmp_R8" ↦ SOME (BExp_Den (BVar "sy_tmp_R8" (BType_Imm Bit32)));
             "tmp_R9" ↦ SOME (BExp_Den (BVar "sy_tmp_R9" (BType_Imm Bit32)));
             "tmp_R10" ↦
               SOME (BExp_Den (BVar "sy_tmp_R10" (BType_Imm Bit32)));
             "tmp_R11" ↦
               SOME (BExp_Den (BVar "sy_tmp_R11" (BType_Imm Bit32)));
             "tmp_R12" ↦
               SOME (BExp_Den (BVar "sy_tmp_R12" (BType_Imm Bit32)));
             "tmp_LR" ↦ SOME (BExp_Den (BVar "sy_tmp_LR" (BType_Imm Bit32)));
             "tmp_SP_main" ↦
               SOME (BExp_Den (BVar "sy_tmp_SP_main" (BType_Imm Bit32)));
             "tmp_SP_process" ↦
               SOME (BExp_Den (BVar "sy_tmp_SP_process" (BType_Imm Bit32)));
             "tmp_ModeHandler" ↦
               SOME (BExp_Den (BVar "sy_tmp_ModeHandler" (BType_Imm Bit1)));
             "tmp_countw" ↦
               SOME (BExp_Den (BVar "sy_tmp_countw" (BType_Imm Bit64)))
           ⦈;
       bsst_status := BST_Running; bsst_pcond := BExp_BinExp BIExp_Plus (BExp_Den (BVar "hello" (BType_Imm Bit8))) (BExp_BinExp BIExp_Plus (BExp_Den (BVar "hello" (BType_Imm Bit8))) (BExp_Const (Imm1 1w)))|>
``;

val tm = ``
birs_exps_of_senv
  (K NONE)⦇
    "MEM" ↦ SOME (BExp_Den (BVar "sy_MEM" (BType_Mem Bit32 Bit8)));
    "PSR_C" ↦ SOME (BExp_Den (BVar "sy_PSR_C" (BType_Imm Bit1)));
    "PSR_N" ↦ SOME (BExp_Den (BVar "sy_PSR_N" (BType_Imm Bit1)));
    "PSR_V" ↦ SOME (BExp_Den (BVar "sy_PSR_V" (BType_Imm Bit1)));
    "PSR_Z" ↦ SOME (BExp_Den (BVar "sy_PSR_Z" (BType_Imm Bit1)));
    "R0" ↦ SOME (BExp_Den (BVar "sy_R0" (BType_Imm Bit32)));
    "R1" ↦ SOME (BExp_Den (BVar "sy_R1" (BType_Imm Bit32)));
    "R2" ↦ SOME (BExp_Den (BVar "sy_R2" (BType_Imm Bit32)));
    "R3" ↦ SOME (BExp_Den (BVar "sy_R3" (BType_Imm Bit32)));
    "R4" ↦ SOME (BExp_Den (BVar "sy_R4" (BType_Imm Bit32)));
    "R5" ↦ SOME (BExp_Den (BVar "sy_R5" (BType_Imm Bit32)));
    "R6" ↦ SOME (BExp_Den (BVar "sy_R6" (BType_Imm Bit32)));
    "R7" ↦ SOME (BExp_Den (BVar "sy_R7" (BType_Imm Bit32)));
    "R8" ↦ SOME (BExp_Den (BVar "sy_R8" (BType_Imm Bit32)));
    "R9" ↦ SOME (BExp_Den (BVar "sy_R9" (BType_Imm Bit32)));
    "R10" ↦ SOME (BExp_Den (BVar "sy_R10" (BType_Imm Bit32)));
    "R11" ↦ SOME (BExp_Den (BVar "sy_R11" (BType_Imm Bit32)));
    "R12" ↦ SOME (BExp_Den (BVar "sy_R12" (BType_Imm Bit32)));
    "LR" ↦ SOME (BExp_Den (BVar "sy_LR" (BType_Imm Bit32)));
    "SP_main" ↦ SOME (BExp_Den (BVar "sy_SP_main" (BType_Imm Bit32)));
    "SP_process" ↦ SOME (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)));
    "ModeHandler" ↦ SOME (BExp_Den (BVar "sy_ModeHandler" (BType_Imm Bit1)));
    "countw" ↦ SOME (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)));
    "tmp_PC" ↦ SOME (BExp_Den (BVar "sy_tmp_PC" (BType_Imm Bit32)));
    "tmp_COND" ↦ SOME (BExp_Den (BVar "sy_tmp_COND" (BType_Imm Bit1)));
    "tmp_MEM" ↦ SOME (BExp_Den (BVar "sy_tmp_MEM" (BType_Mem Bit32 Bit8)));
    "tmp_PSR_C" ↦ SOME (BExp_Den (BVar "sy_tmp_PSR_C" (BType_Imm Bit1)));
    "tmp_PSR_N" ↦ SOME (BExp_Den (BVar "sy_tmp_PSR_N" (BType_Imm Bit1)));
    "tmp_PSR_V" ↦ SOME (BExp_Den (BVar "sy_tmp_PSR_V" (BType_Imm Bit1)));
    "tmp_PSR_Z" ↦ SOME (BExp_Den (BVar "sy_tmp_PSR_Z" (BType_Imm Bit1)));
    "tmp_R0" ↦ SOME (BExp_Den (BVar "sy_tmp_R0" (BType_Imm Bit32)));
    "tmp_R1" ↦ SOME (BExp_Den (BVar "sy_tmp_R1" (BType_Imm Bit32)));
    "tmp_R2" ↦ SOME (BExp_Den (BVar "sy_tmp_R2" (BType_Imm Bit32)));
    "tmp_R3" ↦ SOME (BExp_Den (BVar "sy_tmp_R3" (BType_Imm Bit32)));
    "tmp_R4" ↦ SOME (BExp_Den (BVar "sy_tmp_R4" (BType_Imm Bit32)));
    "tmp_R5" ↦ SOME (BExp_Den (BVar "sy_tmp_R5" (BType_Imm Bit32)));
    "tmp_R6" ↦ SOME (BExp_Den (BVar "sy_tmp_R6" (BType_Imm Bit32)));
    "tmp_R7" ↦ SOME (BExp_Den (BVar "sy_tmp_R7" (BType_Imm Bit32)));
    "tmp_R8" ↦ SOME (BExp_Den (BVar "sy_tmp_R8" (BType_Imm Bit32)));
    "tmp_R9" ↦ SOME (BExp_Den (BVar "sy_tmp_R9" (BType_Imm Bit32)));
    "tmp_R10" ↦ SOME (BExp_Den (BVar "sy_tmp_R10" (BType_Imm Bit32)));
    "tmp_R11" ↦ SOME (BExp_Den (BVar "sy_tmp_R11" (BType_Imm Bit32)));
    "tmp_R12" ↦ SOME (BExp_Den (BVar "sy_tmp_R12" (BType_Imm Bit32)));
    "tmp_LR" ↦ SOME (BExp_Den (BVar "sy_tmp_LR" (BType_Imm Bit32)));
    "tmp_SP_main" ↦ SOME (BExp_Den (BVar "sy_tmp_SP_main" (BType_Imm Bit32)));
    "tmp_SP_process" ↦
      SOME (BExp_Den (BVar "sy_tmp_SP_process" (BType_Imm Bit32)));
    "tmp_ModeHandler" ↦
      SOME (BExp_Den (BVar "sy_tmp_ModeHandler" (BType_Imm Bit1)));
    "tmp_countw" ↦ SOME (BExp_Den (BVar "sy_tmp_countw" (BType_Imm Bit64)))
  ⦈
``;

val tm = ``
     birs_exps_of_senv_COMP ∅
       (K NONE)⦇
         "MEM" ↦ SOME (BExp_Den (BVar "sy_MEM" (BType_Mem Bit32 Bit8)));
         "PSR_C" ↦ SOME (BExp_Den (BVar "sy_PSR_C" (BType_Imm Bit1)));
         "PSR_N" ↦ SOME (BExp_Den (BVar "sy_PSR_N" (BType_Imm Bit1)));
         "PSR_V" ↦ SOME (BExp_Den (BVar "sy_PSR_V" (BType_Imm Bit1)));
         "PSR_Z" ↦ SOME (BExp_Den (BVar "sy_PSR_Z" (BType_Imm Bit1)));
         "R0" ↦ SOME (BExp_Den (BVar "sy_R0" (BType_Imm Bit32)));
         "R1" ↦ SOME (BExp_Den (BVar "sy_R1" (BType_Imm Bit32)));
         "R2" ↦ SOME (BExp_Den (BVar "sy_R2" (BType_Imm Bit32)));
         "R3" ↦ SOME (BExp_Den (BVar "sy_R3" (BType_Imm Bit32)));
         "R4" ↦ SOME (BExp_Den (BVar "sy_R4" (BType_Imm Bit32)));
         "R5" ↦ SOME (BExp_Den (BVar "sy_R5" (BType_Imm Bit32)));
         "R6" ↦ SOME (BExp_Den (BVar "sy_R6" (BType_Imm Bit32)));
         "R7" ↦ SOME (BExp_Den (BVar "sy_R7" (BType_Imm Bit32)));
         "R8" ↦ SOME (BExp_Den (BVar "sy_R8" (BType_Imm Bit32)));
         "R9" ↦ SOME (BExp_Den (BVar "sy_R9" (BType_Imm Bit32)));
         "R10" ↦ SOME (BExp_Den (BVar "sy_R10" (BType_Imm Bit32)));
         "R11" ↦ SOME (BExp_Den (BVar "sy_R11" (BType_Imm Bit32)));
         "R12" ↦ SOME (BExp_Den (BVar "sy_R12" (BType_Imm Bit32)));
         "LR" ↦ SOME (BExp_Den (BVar "sy_LR" (BType_Imm Bit32)));
         "SP_main" ↦ SOME (BExp_Den (BVar "sy_SP_main" (BType_Imm Bit32)));
         "SP_process" ↦
           SOME (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)));
         "ModeHandler" ↦
           SOME (BExp_Den (BVar "sy_ModeHandler" (BType_Imm Bit1)));
         "countw" ↦ SOME (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)));
         "tmp_PC" ↦ SOME (BExp_Den (BVar "sy_tmp_PC" (BType_Imm Bit32)));
         "tmp_COND" ↦ SOME (BExp_Den (BVar "sy_tmp_COND" (BType_Imm Bit1)));
         "tmp_MEM" ↦
           SOME (BExp_Den (BVar "sy_tmp_MEM" (BType_Mem Bit32 Bit8)));
         "tmp_PSR_C" ↦ SOME (BExp_Den (BVar "sy_tmp_PSR_C" (BType_Imm Bit1)));
         "tmp_PSR_N" ↦ SOME (BExp_Den (BVar "sy_tmp_PSR_N" (BType_Imm Bit1)));
         "tmp_PSR_V" ↦ SOME (BExp_Den (BVar "sy_tmp_PSR_V" (BType_Imm Bit1)));
         "tmp_PSR_Z" ↦ SOME (BExp_Den (BVar "sy_tmp_PSR_Z" (BType_Imm Bit1)));
         "tmp_R0" ↦ SOME (BExp_Den (BVar "sy_tmp_R0" (BType_Imm Bit32)));
         "tmp_R1" ↦ SOME (BExp_Den (BVar "sy_tmp_R1" (BType_Imm Bit32)));
         "tmp_R2" ↦ SOME (BExp_Den (BVar "sy_tmp_R2" (BType_Imm Bit32)));
         "tmp_R3" ↦ SOME (BExp_Den (BVar "sy_tmp_R3" (BType_Imm Bit32)));
         "tmp_R4" ↦ SOME (BExp_Den (BVar "sy_tmp_R4" (BType_Imm Bit32)));
         "tmp_R5" ↦ SOME (BExp_Den (BVar "sy_tmp_R5" (BType_Imm Bit32)));
         "tmp_R6" ↦ SOME (BExp_Den (BVar "sy_tmp_R6" (BType_Imm Bit32)));
         "tmp_R7" ↦ SOME (BExp_Den (BVar "sy_tmp_R7" (BType_Imm Bit32)));
         "tmp_R8" ↦ SOME (BExp_Den (BVar "sy_tmp_R8" (BType_Imm Bit32)));
         "tmp_R9" ↦ SOME (BExp_Den (BVar "sy_tmp_R9" (BType_Imm Bit32)));
         "tmp_R10" ↦ SOME (BExp_Den (BVar "sy_tmp_R10" (BType_Imm Bit32)));
         "tmp_R11" ↦ SOME (BExp_Den (BVar "sy_tmp_R11" (BType_Imm Bit32)));
         "tmp_R12" ↦ SOME (BExp_Den (BVar "sy_tmp_R12" (BType_Imm Bit32)));
         "tmp_LR" ↦ SOME (BExp_Den (BVar "sy_tmp_LR" (BType_Imm Bit32)));
         "tmp_SP_main" ↦
           SOME (BExp_Den (BVar "sy_tmp_SP_main" (BType_Imm Bit32)));
         "tmp_SP_process" ↦
           SOME (BExp_Den (BVar "sy_tmp_SP_process" (BType_Imm Bit32)));
         "tmp_ModeHandler" ↦
           SOME (BExp_Den (BVar "sy_tmp_ModeHandler" (BType_Imm Bit1)));
         "tmp_countw" ↦
           SOME (BExp_Den (BVar "sy_tmp_countw" (BType_Imm Bit64)))
       ⦈
``;

val tm = ``
     birs_exps_of_senv_COMP ∅
       (K NONE)⦇
         "MEM" ↦ SOME (BExp_Den (BVar "sy_MEM" (BType_Mem Bit32 Bit8)));
         "PSR_C" ↦ SOME (BExp_Den (BVar "sy_PSR_C" (BType_Imm Bit1)));
         "PSR_N" ↦ SOME (BExp_Den (BVar "sy_PSR_N" (BType_Imm Bit1)));
         "PSR_V" ↦ SOME (BExp_Den (BVar "sy_PSR_V" (BType_Imm Bit1)));
         "PSR_Z" ↦ SOME (BExp_Den (BVar "sy_PSR_Z" (BType_Imm Bit1)))
       ⦈
``;

val tm2 = ``
     birs_exps_of_senv_COMP ∅
       (K NONE)
``;

val tm = ``
birs_exps_of_senv_COMP {"PSR_Z"; "PSR_V"; "PSR_N"; "PSR_C"; "MEM"} (K NONE)
``;


val tm = ``
birs_exps_of_senv
  (K NONE)⦇
    "tmp_SP_process" ↦
      SOME
        (BExp_BinExp BIExp_Minus
           (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)))
           (BExp_Const (Imm32 8w)));
    "MEM" ↦ SOME (BExp_Den (BVar "sy_MEM" (BType_Mem Bit32 Bit8)));
    "PSR_C" ↦ SOME (BExp_Den (BVar "sy_PSR_C" (BType_Imm Bit1)));
    "PSR_N" ↦ SOME (BExp_Den (BVar "sy_PSR_N" (BType_Imm Bit1)));
    "PSR_V" ↦ SOME (BExp_Den (BVar "sy_PSR_V" (BType_Imm Bit1)));
    "PSR_Z" ↦ SOME (BExp_Den (BVar "sy_PSR_Z" (BType_Imm Bit1)));
    "R0" ↦ SOME (BExp_Den (BVar "sy_R0" (BType_Imm Bit32)));
    "R1" ↦ SOME (BExp_Den (BVar "sy_R1" (BType_Imm Bit32)));
    "R2" ↦ SOME (BExp_Den (BVar "sy_R2" (BType_Imm Bit32)));
    "R3" ↦ SOME (BExp_Den (BVar "sy_R3" (BType_Imm Bit32)));
    "R4" ↦ SOME (BExp_Den (BVar "sy_R4" (BType_Imm Bit32)));
    "R5" ↦ SOME (BExp_Den (BVar "sy_R5" (BType_Imm Bit32)));
    "R6" ↦ SOME (BExp_Den (BVar "sy_R6" (BType_Imm Bit32)));
    "R7" ↦ SOME (BExp_Den (BVar "sy_R7" (BType_Imm Bit32)));
    "R8" ↦ SOME (BExp_Den (BVar "sy_R8" (BType_Imm Bit32)));
    "R9" ↦ SOME (BExp_Den (BVar "sy_R9" (BType_Imm Bit32)));
    "R10" ↦ SOME (BExp_Den (BVar "sy_R10" (BType_Imm Bit32)));
    "R11" ↦ SOME (BExp_Den (BVar "sy_R11" (BType_Imm Bit32)));
    "R12" ↦ SOME (BExp_Den (BVar "sy_R12" (BType_Imm Bit32)));
    "LR" ↦ SOME (BExp_Den (BVar "sy_LR" (BType_Imm Bit32)));
    "SP_main" ↦ SOME (BExp_Den (BVar "sy_SP_main" (BType_Imm Bit32)));
    "SP_process" ↦ SOME (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)));
    "ModeHandler" ↦ SOME (BExp_Den (BVar "sy_ModeHandler" (BType_Imm Bit1)));
    "countw" ↦ SOME (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)));
    "tmp_PC" ↦ SOME (BExp_Den (BVar "sy_tmp_PC" (BType_Imm Bit32)));
    "tmp_COND" ↦ SOME (BExp_Den (BVar "sy_tmp_COND" (BType_Imm Bit1)));
    "tmp_MEM" ↦ SOME (BExp_Den (BVar "sy_tmp_MEM" (BType_Mem Bit32 Bit8)));
    "tmp_PSR_C" ↦ SOME (BExp_Den (BVar "sy_tmp_PSR_C" (BType_Imm Bit1)));
    "tmp_PSR_N" ↦ SOME (BExp_Den (BVar "sy_tmp_PSR_N" (BType_Imm Bit1)));
    "tmp_PSR_V" ↦ SOME (BExp_Den (BVar "sy_tmp_PSR_V" (BType_Imm Bit1)));
    "tmp_PSR_Z" ↦ SOME (BExp_Den (BVar "sy_tmp_PSR_Z" (BType_Imm Bit1)));
    "tmp_R0" ↦ SOME (BExp_Den (BVar "sy_tmp_R0" (BType_Imm Bit32)));
    "tmp_R1" ↦ SOME (BExp_Den (BVar "sy_tmp_R1" (BType_Imm Bit32)));
    "tmp_R2" ↦ SOME (BExp_Den (BVar "sy_tmp_R2" (BType_Imm Bit32)));
    "tmp_R3" ↦ SOME (BExp_Den (BVar "sy_tmp_R3" (BType_Imm Bit32)));
    "tmp_R4" ↦ SOME (BExp_Den (BVar "sy_tmp_R4" (BType_Imm Bit32)));
    "tmp_R5" ↦ SOME (BExp_Den (BVar "sy_tmp_R5" (BType_Imm Bit32)));
    "tmp_R6" ↦ SOME (BExp_Den (BVar "sy_tmp_R6" (BType_Imm Bit32)));
    "tmp_R7" ↦ SOME (BExp_Den (BVar "sy_tmp_R7" (BType_Imm Bit32)));
    "tmp_R8" ↦ SOME (BExp_Den (BVar "sy_tmp_R8" (BType_Imm Bit32)));
    "tmp_R9" ↦ SOME (BExp_Den (BVar "sy_tmp_R9" (BType_Imm Bit32)));
    "tmp_R10" ↦ SOME (BExp_Den (BVar "sy_tmp_R10" (BType_Imm Bit32)));
    "tmp_R11" ↦ SOME (BExp_Den (BVar "sy_tmp_R11" (BType_Imm Bit32)));
    "tmp_R12" ↦ SOME (BExp_Den (BVar "sy_tmp_R12" (BType_Imm Bit32)));
    "tmp_LR" ↦ SOME (BExp_Den (BVar "sy_tmp_LR" (BType_Imm Bit32)));
    "tmp_SP_main" ↦ SOME (BExp_Den (BVar "sy_tmp_SP_main" (BType_Imm Bit32)));
    "tmp_SP_process" ↦
      SOME (BExp_Den (BVar "sy_tmp_SP_process" (BType_Imm Bit32)));
    "tmp_ModeHandler" ↦
      SOME (BExp_Den (BVar "sy_tmp_ModeHandler" (BType_Imm Bit1)));
    "tmp_countw" ↦ SOME (BExp_Den (BVar "sy_tmp_countw" (BType_Imm Bit64)))
  ⦈
``;


val tm = ``
birs_exps_of_senv_COMP {"tmp_SP_process"}
       (K NONE)⦇
         "tmp_SP_process" ↦
           SOME
             (BExp_BinExp BIExp_Minus
                (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)))
                (BExp_Const (Imm32 8w)));
         "tmp_ModeHandler" ↦
           SOME (BExp_Den (BVar "sy_tmp_ModeHandler" (BType_Imm Bit1)));
         "tmp_countw" ↦
           SOME (BExp_Den (BVar "sy_tmp_countw" (BType_Imm Bit64)))
       ⦈
``;

*)
