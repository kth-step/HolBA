structure bir_vars_ofLib =
struct

local

  open HolKernel Parse boolLib bossLib;

  open bir_typing_expTheory;
  open bir_typing_expSyntax;
  open birsSyntax;
  open birs_utilsLib;

  open bir_convLib;
  open holba_convLib;
  open holba_cacheLib;

  open HolBACoreSimps;

  open birs_auxTheory;
  val birs_state_ss = rewrites (type_rws ``:birs_state_t``);

  (* error handling *)
  val libname = "bir_vars_ofLib"
  val ERR = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname

in (* local *)

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
  val birs_exps_of_senv_COMP_ONCE_CONV =
    (*
    (* this implementation of birs_exps_of_senv_COMP_ONCE_CONV works fine, but not as speedy as the one below *)
    (fn x => REWRITE_CONV [Once birs_exps_of_senv_COMP_thm] x) THENC
    (TRY_CONV (ITE_CONV (pred_setLib.IN_CONV bir_varname_EQ_CONV)))
    *)
    IFC
      (REWR_CONV ((GEN_ALL o (fn x => List.nth(x,1)) o CONJUNCTS o SPEC_ALL) birs_exps_of_senv_COMP_thm))
      (ITE_CONV (pred_setLib.IN_CONV bir_varname_EQ_CONV))
      (IFC
        (REWR_CONV ((GEN_ALL o (fn x => List.nth(x,0)) o CONJUNCTS o SPEC_ALL) birs_exps_of_senv_COMP_thm))
        (ALL_CONV)
        (REWR_CONV ((GEN_ALL o (fn x => List.nth(x,2)) o CONJUNCTS o SPEC_ALL) birs_exps_of_senv_COMP_thm)));

  fun birs_exps_of_senv_COMP_CONV tm = (
    birs_exps_of_senv_COMP_ONCE_CONV THENC
    (fn tm_ => (
      if pred_setSyntax.is_empty tm_ then
        ALL_CONV
      else if pred_setSyntax.is_insert tm_ then
        RAND_CONV birs_exps_of_senv_COMP_CONV
      else
        birs_exps_of_senv_COMP_CONV
    ) tm_)
  ) tm;

  val birs_exps_of_senv_CONV =
    REWRITE_CONV [birs_gen_env_thm, birs_gen_env_NULL_thm] THENC
    REWR_CONV birs_exps_of_senv_thm THENC
    birs_exps_of_senv_COMP_CONV;

  val birs_symb_symbols_DIRECT_CONV =
    (
      REWR_CONV birs_symb_symbols_thm THENC

      (RAND_CONV (
        REWRITE_CONV [bir_symbTheory.birs_state_t_accfupds, combinTheory.K_THM] THENC
        bir_vars_of_exp_DIRECT_CONV
      )) THENC
      RATOR_CONV (RAND_CONV (
        RAND_CONV (
          RAND_CONV (
            REWRITE_CONV [bir_symbTheory.birs_state_t_accfupds, combinTheory.K_THM] THENC
            birs_exps_of_senv_CONV
          ) THENC
          (pred_setLib.IMAGE_CONV
            bir_vars_of_exp_DIRECT_CONV
            NO_CONV)) THENC
        (varset_BIGUNION_CONV)
      )) THENC
      (varset_UNION_CONV)
      (*
      (* basic solution for flattening the set and avoid comparisons *)
      RATOR_CONV (RAND_CONV (REWRITE_CONV [pred_setTheory.BIGUNION_INSERT, pred_setTheory.BIGUNION_EMPTY])) THENC
      REWRITE_CONV [Once pred_setTheory.UNION_COMM] THENC
      REWRITE_CONV [pred_setTheory.UNION_ASSOC, pred_setTheory.INSERT_UNION_EQ, pred_setTheory.UNION_EMPTY]
      *)
    ) o (fn tm =>
      if is_birs_symb_symbols tm then tm else
        raise ERR "birs_symb_symbols_DIRECT_CONV" "cannot handle term"
    );
  val birs_symb_symbols_DIRECT_CONV = wrap_cache_result Term.compare birs_symb_symbols_DIRECT_CONV;
  val birs_symb_symbols_DIRECT_CONV = Profile.profile "birs_symb_symbols_DIRECT_CONV" birs_symb_symbols_DIRECT_CONV;

  val birs_symb_symbols_CONV =
    GEN_match_conv is_birs_symb_symbols birs_symb_symbols_DIRECT_CONV;


(* ---------------------------------------------------------------------------------- *)
(*  symbols of set of symbolic bir states                                             *)
(* ---------------------------------------------------------------------------------- *)
  val birs_symb_symbols_set_DIRECT_CONV =
    (
      REWR_CONV birs_rulesTheory.birs_symb_symbols_set_def THENC
      RAND_CONV (
        pred_setLib.IMAGE_CONV
          birs_symb_symbols_DIRECT_CONV
          NO_CONV) THENC
      (* now have BIGUNION {setA;setB;setC;...} *)
      varset_BIGUNION_CONV
    ) o (fn tm =>
      if is_birs_symb_symbols_set tm then tm else
        raise ERR "birs_symb_symbols_set_DIRECT_CONV" "cannot handle term"
    );
  val birs_symb_symbols_set_DIRECT_CONV = wrap_cache_result Term.compare birs_symb_symbols_set_DIRECT_CONV;
  val birs_symb_symbols_set_DIRECT_CONV = Profile.profile "birs_symb_symbols_set_DIRECT_CONV" birs_symb_symbols_set_DIRECT_CONV;

  val birs_symb_symbols_set_CONV =
    GEN_match_conv is_birs_symb_symbols_set birs_symb_symbols_set_DIRECT_CONV;


(* ---------------------------------------------------------------------------------- *)
(*  free symbols of execution structure (sys, L, Pi)                                  *)
(* ---------------------------------------------------------------------------------- *)
  val birs_freesymbs_DIRECT_CONV =
    (
      REWR_CONV birs_rulesTheory.birs_freesymbs_def THENC
      LAND_CONV (birs_symb_symbols_set_DIRECT_CONV) THENC
      RAND_CONV (birs_symb_symbols_DIRECT_CONV) THENC
      varset_DIFF_CONV
    ) o (fn tm =>
      if is_birs_freesymbs tm then tm else
        raise ERR "birs_freesymbs_DIRECT_CONV" "cannot handle term"
    );
  val birs_freesymbs_DIRECT_CONV = wrap_cache_result Term.compare birs_freesymbs_DIRECT_CONV;
  val birs_freesymbs_DIRECT_CONV = Profile.profile "birs_freesymbs_DIRECT_CONV" birs_freesymbs_DIRECT_CONV;

  val birs_freesymbs_CONV =
    GEN_match_conv is_birs_freesymbs birs_freesymbs_DIRECT_CONV;

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
