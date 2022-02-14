structure birs_composeLib =
struct

local

  open HolKernel Parse boolLib bossLib;


  (* error handling *)
  val libname = "bir_symb_composeLib"
  val ERR = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname

(*
open symb_recordTheory;
open symb_prop_transferTheory;
open bir_symbTheory;

open bir_symb_sound_coreTheory;
open HolBACoreSimps;
open symb_interpretTheory;
open pred_setTheory;
*)
  open birs_stepLib;
  open birs_auxTheory;
  val birs_state_ss = rewrites (type_rws ``:birs_state_t``);

in

(* first prepare the SEQ rule for prog *)
fun birs_rule_SEQ_prog_fun bprog_tm =
  let
    val prog_type = (hd o snd o dest_type o type_of) bprog_tm;
    val symbols_f_sound_thm = INST_TYPE [Type.alpha |-> prog_type] bir_symb_soundTheory.birs_symb_symbols_f_sound_thm;
    val birs_symb_symbols_f_sound_prog_thm =
      (SPEC (bprog_tm) symbols_f_sound_thm);
  in
    (MATCH_MP symb_rulesTheory.symb_rule_SEQ_thm birs_symb_symbols_f_sound_prog_thm)
  end;

(* symbol freedom helper function *)
fun birs_rule_SEQ_free_symbols_fun bprog_tm (sys_A_tm, sys_B_tm, Pi_B_tm) =
  let
    (*
    val freesymbols_thm = store_thm(
       "freesymbols_thm", ``
    *)

(* ------------------------------------------------------------------------ *)
(* COPIED FROM TRANSFER-TEST (and modified) *)
(* ------------------------------------------------------------------------ *)

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

val debug_conv = (fn tm => (print_term tm; raise Fail "abcdE!!!"));
val debug_conv2 = (fn tm => (if true then print ".\n" else print_term tm; REFL tm));

  fun GEN_match_conv is_tm_fun conv tm =
    if is_tm_fun tm then
      conv tm
    else if is_comb tm then
        ((RAND_CONV  (GEN_match_conv is_tm_fun conv)) THENC
         (RATOR_CONV (GEN_match_conv is_tm_fun conv))) tm
    else if is_abs tm then
        TRY_CONV (ABS_CONV (GEN_match_conv is_tm_fun conv)) tm
    else
      raise UNCHANGED
    ;

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

fun birs_exps_of_senv_COMP_CONV tm =
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
        RAND_CONV birs_exps_of_senv_COMP_CONV
      else
        birs_exps_of_senv_COMP_CONV
    ) tm))
    (fn tm => (print_term tm; raise Fail "unexpected here"))
) tm;

fun birs_exps_of_senv_CONV tm =
(
(*
(fn tm => (if false then print ".\n" else print_term tm; REFL tm)) THENC
*)
  REWRITE_CONV [birs_exps_of_senv_thm] THENC
  ((*TRY_CONV*) birs_exps_of_senv_COMP_CONV_cheat)
) tm;

fun is_birs_exps_of_senv tm = is_comb tm andalso
                              (is_const o fst o dest_comb) tm andalso
                              ((fn tm2 => tm2 = "birs_exps_of_senv") o fst o dest_const o fst o dest_comb) tm;
fun birs_symb_symbols_CONV tm =
(
  SIMP_CONV (std_ss++birs_state_ss) [birs_symb_symbols_thm] THENC
  debug_conv2 THENC
  GEN_match_conv is_birs_exps_of_senv birs_exps_of_senv_CONV THENC
  debug_conv2 THENC
  REWRITE_CONV [pred_setTheory.IMAGE_INSERT, pred_setTheory.IMAGE_EMPTY, bir_typing_expTheory.bir_vars_of_exp_def] THENC

  debug_conv2 THENC
  RATOR_CONV (RAND_CONV (REWRITE_CONV [pred_setTheory.BIGUNION_INSERT, pred_setTheory.BIGUNION_EMPTY])) THENC

  REWRITE_CONV [Once pred_setTheory.UNION_COMM] THENC
  REWRITE_CONV [pred_setTheory.UNION_ASSOC, pred_setTheory.INSERT_UNION_EQ, pred_setTheory.UNION_EMPTY]
) tm;

fun is_birs_symb_symbols tm = is_comb tm andalso
                              (is_const o fst o dest_comb) tm andalso
                              ((fn tm2 => tm2 = "birs_symb_symbols") o fst o dest_const o fst o dest_comb) tm;
fun birs_symb_symbols_MATCH_CONV tm =
  GEN_match_conv is_birs_symb_symbols birs_symb_symbols_CONV tm;

(* ................................................ *)

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

(* 65 * 30 * t_IN_VAR = 9-10s
t_IN_VAR = 0.005s *)
(* !!!!! try computeLib *)
val string_ss = rewrites (type_rws ``:string``);

val el_EQ_CONV = SIMP_CONV (std_ss++HolBACoreSimps.holBACore_ss++string_ss) [];
val el_EQ_CONV = RAND_CONV EVAL;

fun IN_INSERT_CONV el_EQ_CONV tm =
(
  REWRITE_CONV [pred_setTheory.NOT_IN_EMPTY] THENC
  REPEATC (CHANGED_CONV (
     (fn xyz => REWRITE_CONV [Once pred_setTheory.IN_INSERT] xyz) THENC
     (*(fn tm => (if false then print ".\n" else print_term tm; print "aa\n\n"; REFL tm)) THENC*)
     IFC
       (RATOR_CONV el_EQ_CONV)
       (REWRITE_CONV [pred_setTheory.NOT_IN_EMPTY])
       REFL))
) tm;

fun INTER_INSERT_ONCE_CONV el_EQ_CONV tm =
(
  (QCHANGED_CONV (CHANGED_CONV (fn x => REWRITE_CONV [Once pred_setTheory.INSERT_INTER, pred_setTheory.INTER_EMPTY] x))) THENC
  IFC
    (RATOR_CONV (RATOR_CONV (RAND_CONV (
(*
fn tm => (print_term (concl (prove (mk_eq (tm, F), cheat))); prove (mk_eq (tm, F), cheat))
*)
(*fn tm => (prove (mk_eq (tm, F), cheat))*)
(*(fn tm => (if false then print ".\n" else print_term tm; print "aa\n\n"; REFL tm)) THENC*)
IN_INSERT_CONV el_EQ_CONV
))))
    (REWRITE_CONV [])
    (REFL)
) tm;

fun INTER_INSERT_CONV el_EQ_CONV tm =
(
  if pred_setSyntax.is_empty tm then
    REFL
  else
  (fn tm => (if true then print ".\n" else (print_term tm; print "\n\n"); REFL tm)) THENC
  IFC
    (INTER_INSERT_ONCE_CONV el_EQ_CONV)
    (
(*
(fn tm => (if false then print ".\n" else print_term tm; print "bb\n\n"; REFL tm)) THENC
*)
(fn tm =>
      (
      (*(fn tm => (if false then print ".\n" else print_term tm; print "bb\n\n"; REFL tm)) THENC *)
      (if pred_setSyntax.is_empty tm then
       (REFL)
      else if pred_setSyntax.is_inter tm then
       (INTER_INSERT_CONV el_EQ_CONV)
      else if pred_setSyntax.is_insert tm then
       (RAND_CONV (INTER_INSERT_CONV el_EQ_CONV))
      else
       (REFL))) tm))
(* the following causes trouble as "normal exit" if there is nothing to be done at the first call *)
    (fn tm => (print_term tm; raise Fail "unexpected here"))
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

fun freevarset_CONV tm =
(
  REWRITE_CONV [Once (prove(``
!s t g.
g INTER (s DIFF t) =
s INTER (g DIFF t)
``,
(*REWRITE_RULE [Once pred_setTheory.INTER_COMM] pred_setTheory.DIFF_INTER*)
METIS_TAC [pred_setTheory.INTER_COMM, pred_setTheory.DIFF_INTER]
))] THENC

  (* DIFF first *)
(*
  RATOR_CONV (RAND_CONV (SIMP_CONV (std_ss++HolBACoreSimps.holBACore_ss++string_ss) [pred_setTheory.INSERT_INTER, pred_setTheory.INTER_EMPTY])) THENC
*)
 (* RATOR_CONV (RAND_CONV (INTER_INSERT_CONV el_EQ_CONV)) THENC*)
  (RAND_CONV (
(*
   (fn tm => prove (``^tm = EMPTY``, cheat))
*)
   DIFF_INSERT_CONV_cheat
)) THENC
(*
(fn tm => (if false then print ".\n" else print_term tm; print "aa\n\n"; REFL tm)) THENC
*)

  

  (* then INTER *)
(*
  INTER_INSERT_CONV el_EQ_CONV
*)
  INTER_INSERT_CONV_cheat
) tm;

(* EVAL tm *)

(* ------------------------------------------------------------------------ *)
(* ------------------------------------------------------------------------ *)

    val freesymbols_thm = prove(``
    symb_symbols (bir_symb_rec_sbir ^bprog_tm) ^sys_A_tm INTER
      (symb_symbols_set (bir_symb_rec_sbir ^bprog_tm) ^Pi_B_tm DIFF
         symb_symbols (bir_symb_rec_sbir ^bprog_tm) ^sys_B_tm)
    = EMPTY
    ``,
      FULL_SIMP_TAC (std_ss) [bir_symb_sound_coreTheory.birs_symb_symbols_EQ_thm, birs_symb_symbols_set_EQ_thm] >>

      (* TODO *)
      CONV_TAC (computeLib.RESTR_EVAL_CONV [``birs_symb_symbols``, ``$BIGUNION``]) >>



      CONV_TAC (birs_symb_symbols_MATCH_CONV) >>
(*
      CONV_TAC (
  SIMP_CONV (std_ss++birs_state_ss) [birs_symb_symbols_thm] THENC


  GEN_match_conv is_birs_exps_of_senv birs_exps_of_senv_CONV THENC
(*
  REWRITE_CONV [birs_exps_of_senv_thm] THENC
*)
  REWRITE_CONV [bir_typing_expTheory.bir_vars_of_exp_def] THENC

  computeLib.RESTR_EVAL_CONV [``$DIFF``, ``$INTER``, ``$UNION``, ``$INSERT``, ``$BIGUNION``] THENC
      REWRITE_CONV [pred_setTheory.BIGUNION_INSERT, pred_setTheory.BIGUNION_EMPTY] THENC
      REWRITE_CONV [pred_setTheory.UNION_ASSOC, pred_setTheory.INSERT_UNION_EQ, pred_setTheory.UNION_EMPTY] THENC

  REFL
) >>
*)

      REWRITE_TAC [pred_setTheory.BIGUNION_INSERT, pred_setTheory.BIGUNION_EMPTY] >>
      REWRITE_TAC [pred_setTheory.UNION_ASSOC, pred_setTheory.INSERT_UNION_EQ, pred_setTheory.UNION_EMPTY] >>

(*
      (fn (al,g) => (print_term g; ([(al,g)], fn ([t]) => t))) >>
*)
      (fn (al,g) => (print "starting to proof free symbols\n"; ([(al,g)], fn ([t]) => t))) >>

(*
prove(``{BVar "sy_tmp_countw" (BType_Imm Bit64);
 BVar "sy_tmp_ModeHandler" (BType_Imm Bit1);
 BVar "sy_tmp_SP_process" (BType_Imm Bit32);
 BVar "sy_tmp_SP_main" (BType_Imm Bit32); BVar "sy_tmp_LR" (BType_Imm Bit32);
 BVar "sy_tmp_R12" (BType_Imm Bit32); BVar "sy_tmp_R11" (BType_Imm Bit32);
 BVar "sy_tmp_R10" (BType_Imm Bit32); BVar "sy_tmp_R9" (BType_Imm Bit32);
 BVar "sy_tmp_R8" (BType_Imm Bit32); BVar "sy_tmp_R7" (BType_Imm Bit32);
 BVar "sy_tmp_R6" (BType_Imm Bit32); BVar "sy_tmp_R5" (BType_Imm Bit32);
 BVar "sy_tmp_R4" (BType_Imm Bit32); BVar "sy_tmp_R3" (BType_Imm Bit32);
 BVar "sy_tmp_R2" (BType_Imm Bit32); BVar "sy_tmp_R1" (BType_Imm Bit32);
 BVar "sy_tmp_R0" (BType_Imm Bit32); BVar "sy_tmp_PSR_Z" (BType_Imm Bit1);
 BVar "sy_tmp_PSR_V" (BType_Imm Bit1); BVar "sy_tmp_PSR_N" (BType_Imm Bit1);
 BVar "sy_tmp_PSR_C" (BType_Imm Bit1);
 BVar "sy_tmp_MEM" (BType_Mem Bit32 Bit8);
 BVar "sy_tmp_COND" (BType_Imm Bit1); BVar "sy_tmp_PC" (BType_Imm Bit32);
 BVar "sy_countw" (BType_Imm Bit64); BVar "sy_ModeHandler" (BType_Imm Bit1);
 BVar "sy_SP_process" (BType_Imm Bit32); BVar "sy_SP_main" (BType_Imm Bit32);
 BVar "sy_LR" (BType_Imm Bit32); BVar "sy_R12" (BType_Imm Bit32);
 BVar "sy_R11" (BType_Imm Bit32); BVar "sy_R10" (BType_Imm Bit32);
 BVar "sy_R9" (BType_Imm Bit32); BVar "sy_R8" (BType_Imm Bit32);
 BVar "sy_R7" (BType_Imm Bit32); BVar "sy_R6" (BType_Imm Bit32);
 BVar "sy_R5" (BType_Imm Bit32); BVar "sy_R4" (BType_Imm Bit32);
 BVar "sy_R3" (BType_Imm Bit32); BVar "sy_R2" (BType_Imm Bit32);
 BVar "sy_R1" (BType_Imm Bit32); BVar "sy_R0" (BType_Imm Bit32);
 BVar "sy_PSR_Z" (BType_Imm Bit1); BVar "sy_PSR_V" (BType_Imm Bit1);
 BVar "sy_PSR_N" (BType_Imm Bit1); BVar "sy_PSR_C" (BType_Imm Bit1);
 BVar "sy_MEM" (BType_Mem Bit32 Bit8)} ∩
({BVar "sy_countw" (BType_Imm Bit64); BVar "sy_SP_process" (BType_Imm Bit32);
  BVar "sy_SP_process" (BType_Imm Bit32);
  BVar "sy_SP_process" (BType_Imm Bit32);
  BVar "sy_SP_process" (BType_Imm Bit32);
  BVar "sy_SP_process" (BType_Imm Bit32);
  BVar "sy_SP_process" (BType_Imm Bit32);
  BVar "sy_tmp_countw" (BType_Imm Bit64);
  BVar "sy_tmp_ModeHandler" (BType_Imm Bit1);
  BVar "sy_tmp_SP_main" (BType_Imm Bit32);
  BVar "sy_tmp_LR" (BType_Imm Bit32); BVar "sy_tmp_R12" (BType_Imm Bit32);
  BVar "sy_tmp_R11" (BType_Imm Bit32); BVar "sy_tmp_R10" (BType_Imm Bit32);
  BVar "sy_tmp_R9" (BType_Imm Bit32); BVar "sy_tmp_R8" (BType_Imm Bit32);
  BVar "sy_tmp_R7" (BType_Imm Bit32); BVar "sy_tmp_R6" (BType_Imm Bit32);
  BVar "sy_tmp_R5" (BType_Imm Bit32); BVar "sy_tmp_R4" (BType_Imm Bit32);
  BVar "sy_tmp_R3" (BType_Imm Bit32); BVar "sy_tmp_R2" (BType_Imm Bit32);
  BVar "sy_tmp_R1" (BType_Imm Bit32); BVar "sy_tmp_R0" (BType_Imm Bit32);
  BVar "sy_tmp_PSR_Z" (BType_Imm Bit1); BVar "sy_tmp_PSR_V" (BType_Imm Bit1);
  BVar "sy_tmp_PSR_N" (BType_Imm Bit1); BVar "sy_tmp_PSR_C" (BType_Imm Bit1);
  BVar "sy_tmp_MEM" (BType_Mem Bit32 Bit8);
  BVar "sy_tmp_COND" (BType_Imm Bit1); BVar "sy_tmp_PC" (BType_Imm Bit32);
  BVar "sy_ModeHandler" (BType_Imm Bit1);
  BVar "sy_SP_process" (BType_Imm Bit32);
  BVar "sy_SP_main" (BType_Imm Bit32); BVar "sy_LR" (BType_Imm Bit32);
  BVar "sy_R12" (BType_Imm Bit32); BVar "sy_R11" (BType_Imm Bit32);
  BVar "sy_R10" (BType_Imm Bit32); BVar "sy_R9" (BType_Imm Bit32);
  BVar "sy_R8" (BType_Imm Bit32); BVar "sy_R7" (BType_Imm Bit32);
  BVar "sy_R6" (BType_Imm Bit32); BVar "sy_R5" (BType_Imm Bit32);
  BVar "sy_R4" (BType_Imm Bit32); BVar "sy_R3" (BType_Imm Bit32);
  BVar "sy_R2" (BType_Imm Bit32); BVar "sy_R1" (BType_Imm Bit32);
  BVar "sy_R0" (BType_Imm Bit32); BVar "sy_PSR_Z" (BType_Imm Bit1);
  BVar "sy_PSR_V" (BType_Imm Bit1); BVar "sy_PSR_N" (BType_Imm Bit1);
  BVar "sy_PSR_C" (BType_Imm Bit1); BVar "sy_MEM" (BType_Mem Bit32 Bit8);
  BVar "sy_SP_process" (BType_Imm Bit32); BVar "sy_countw" (BType_Imm Bit64)} DIFF
 {BVar "sy_countw" (BType_Imm Bit64); BVar "sy_SP_process" (BType_Imm Bit32);
  BVar "sy_SP_process" (BType_Imm Bit32);
  BVar "sy_SP_process" (BType_Imm Bit32);
  BVar "sy_SP_process" (BType_Imm Bit32);
  BVar "sy_SP_process" (BType_Imm Bit32);
  BVar "sy_SP_process" (BType_Imm Bit32);
  BVar "sy_tmp_countw" (BType_Imm Bit64);
  BVar "sy_tmp_ModeHandler" (BType_Imm Bit1);
  BVar "sy_tmp_SP_main" (BType_Imm Bit32);
  BVar "sy_tmp_LR" (BType_Imm Bit32); BVar "sy_tmp_R12" (BType_Imm Bit32);
  BVar "sy_tmp_R11" (BType_Imm Bit32); BVar "sy_tmp_R10" (BType_Imm Bit32);
  BVar "sy_tmp_R9" (BType_Imm Bit32); BVar "sy_tmp_R8" (BType_Imm Bit32);
  BVar "sy_tmp_R7" (BType_Imm Bit32); BVar "sy_tmp_R6" (BType_Imm Bit32);
  BVar "sy_tmp_R5" (BType_Imm Bit32); BVar "sy_tmp_R4" (BType_Imm Bit32);
  BVar "sy_tmp_R3" (BType_Imm Bit32); BVar "sy_tmp_R2" (BType_Imm Bit32);
  BVar "sy_tmp_R1" (BType_Imm Bit32); BVar "sy_tmp_R0" (BType_Imm Bit32);
  BVar "sy_tmp_PSR_Z" (BType_Imm Bit1); BVar "sy_tmp_PSR_V" (BType_Imm Bit1);
  BVar "sy_tmp_PSR_N" (BType_Imm Bit1); BVar "sy_tmp_PSR_C" (BType_Imm Bit1);
  BVar "sy_tmp_MEM" (BType_Mem Bit32 Bit8);
  BVar "sy_tmp_COND" (BType_Imm Bit1); BVar "sy_tmp_PC" (BType_Imm Bit32);
  BVar "sy_countw" (BType_Imm Bit64); BVar "sy_ModeHandler" (BType_Imm Bit1);
  BVar "sy_SP_process" (BType_Imm Bit32);
  BVar "sy_SP_main" (BType_Imm Bit32); BVar "sy_LR" (BType_Imm Bit32);
  BVar "sy_R12" (BType_Imm Bit32); BVar "sy_R11" (BType_Imm Bit32);
  BVar "sy_R10" (BType_Imm Bit32); BVar "sy_R9" (BType_Imm Bit32);
  BVar "sy_R8" (BType_Imm Bit32); BVar "sy_R7" (BType_Imm Bit32);
  BVar "sy_R6" (BType_Imm Bit32); BVar "sy_R5" (BType_Imm Bit32);
  BVar "sy_R4" (BType_Imm Bit32); BVar "sy_R3" (BType_Imm Bit32);
  BVar "sy_R2" (BType_Imm Bit32); BVar "sy_R1" (BType_Imm Bit32);
  BVar "sy_R0" (BType_Imm Bit32); BVar "sy_PSR_Z" (BType_Imm Bit1);
  BVar "sy_PSR_V" (BType_Imm Bit1); BVar "sy_PSR_N" (BType_Imm Bit1);
  BVar "sy_PSR_C" (BType_Imm Bit1); BVar "sy_MEM" (BType_Mem Bit32 Bit8);
  BVar "sy_SP_process" (BType_Imm Bit32)}) ⊆ ∅
``,
);
*)


      CONV_TAC (RATOR_CONV (RAND_CONV (freevarset_CONV))) >>
      (fn (al,g) => (print "finished to proof free symbols operation\n"; ([(al,g)], fn ([t]) => t))) >>

      REWRITE_TAC [pred_setTheory.EMPTY_SUBSET]
      >> (fn (al,g) => (print "finished to proof free symbols\n"; ([(al,g)], fn ([t]) => t)))

(*
      EVAL_TAC (* TODO: speed this up... *)
*)

(*
      FULL_SIMP_TAC (std_ss) [pred_setTheory.IMAGE_INSERT, pred_setTheory.IMAGE_EMPTY] >>
      FULL_SIMP_TAC (std_ss++birs_state_ss) [birs_symb_symbols_thm] >>

      CONV_TAC (conv) >>
      REPEAT (
        CHANGED_TAC ( fn xyz =>
            REWRITE_TAC [Once (prove(``!x. (IMAGE bir_vars_of_exp x) = I (IMAGE bir_vars_of_exp x)``, REWRITE_TAC [combinTheory.I_THM]))]
            xyz
        ) >>
        CONV_TAC (GEN_match_conv combinSyntax.is_I (RAND_CONV birs_exps_of_senv_CONV))
      ) >>

      EVAL_TAC
*)
(*
      CONV_TAC (conv)
      CONV_TAC (fn tm => (print_term tm; REFL tm))
      CONV_TAC (DEPTH_CONV (PAT_CONV ``\A. (I:((bir_var_t->bool)->bool)->((bir_var_t->bool)->bool)) A`` (fn tm => (print_term tm; raise Fail "abcdE!!!"))))



(combinSyntax.is_I o snd o dest_comb) tm





      CONV_TAC (ONCE_DEPTH_CONV (PAT_CONV ``\A. IMAGE bir_vars_of_exp A`` (birs_exps_of_senv_CONV)))


FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) []
      EVAL_TAC

      CONV_TAC (PAT_CONV ``\A. (A DIFF C)`` (conv))





      FULL_SIMP_TAC (std_ss++birs_state_ss) [birs_exps_of_senv_thm, birs_exps_of_senv_COMP_thm] >>

      EVAL_TAC
    (*
      FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [pred_setTheory.GSPECIFICATION]
    *)
*)
    );
  in
    freesymbols_thm
  end;

(*
val step_A_thm = single_step_A_thm;
val step_B_thm = single_step_B_thm;
*)
fun birs_rule_SEQ_fun birs_rule_SEQ_thm step_A_thm step_B_thm =
  let
    val get_SEQ_thm_concl_symb_struct_fun = snd o strip_imp o snd o strip_binder (SOME boolSyntax.universal) o concl;
    val symb_struct_get_bprog_fun = snd o dest_comb o hd o snd o strip_comb;
    val bprog_tm   = (symb_struct_get_bprog_fun o get_SEQ_thm_concl_symb_struct_fun) birs_rule_SEQ_thm;
    val bprog_A_tm = (symb_struct_get_bprog_fun o concl) step_A_thm;
    val bprog_B_tm = (symb_struct_get_bprog_fun o concl) step_B_thm;
    val _ = if identical bprog_tm bprog_A_tm andalso identical bprog_tm bprog_B_tm then () else
            raise Fail "birs_rule_SEQ_fun:: the programs have to match";

    val (sys_A_tm, _, _)       = (symb_sound_struct_get_sysLPi_fun o concl) step_A_thm;
    val (sys_B_tm, _, Pi_B_tm) = (symb_sound_struct_get_sysLPi_fun o concl) step_B_thm;

    val freesymbols_thm = birs_rule_SEQ_free_symbols_fun bprog_tm (sys_A_tm, sys_B_tm, Pi_B_tm);
    val _ = print "finished to proof free symbols altogether\n";
    (*
    val bprog_composed_thm = save_thm(
       "bprog_composed_thm",
    *)
    val bprog_composed_thm =
      MATCH_MP
        (MATCH_MP
           (MATCH_MP
              birs_rule_SEQ_thm
              freesymbols_thm)
        step_A_thm)
        step_B_thm;
    val _ = print "composed\n";

    (* TODO: tidy up set operations to not accumulate (in both, post state set and label set) - does this simplification work well enough? *)
    (* val bprog_composed_thm_ = SIMP_RULE (std_ss++pred_setLib.PRED_SET_ss) [] bprog_composed_thm; *)
    (* val bprog_composed_thm_ = SIMP_RULE (std_ss++pred_setLib.PRED_SET_ss++HolBACoreSimps.holBACore_ss) [pred_setTheory.INSERT_UNION] bprog_composed_thm; *)

(*
val tm = (snd o dest_comb o snd o dest_comb o snd o dest_comb o concl) bprog_composed_thm;
*)

    fun DIFF_UNION_CONV tm =
      let
        val pat_tm = ``(IMAGE (birs_symb_to_symbst) Pi_a) DIFF {birs_symb_to_symbst sys_b} UNION (IMAGE birs_symb_to_symbst Pi_b)``;
        val (tm_match, ty_match) = match_term pat_tm tm;

        val Pi_a  = pred_setSyntax.strip_set(subst tm_match (inst ty_match ``Pi_a:birs_state_t->bool``));
        val sys_b = subst tm_match (inst ty_match ``sys_b:birs_state_t``);
        val Pi_b  = pred_setSyntax.strip_set(subst tm_match (inst ty_match ``Pi_b:birs_state_t->bool``));

        fun eq_fun sys1 sys2 = identical sys1 sys2; (* TODO: birs_state_eq_fun*)
        fun in_f l x = List.foldr (fn (y, b) => b orelse eq_fun x y) false l;
        val Pi_a_minus_b = List.filter (not o eq_fun sys_b) Pi_a;
        fun UNION_foldfun (sys,Pi) = if in_f Pi sys then Pi else (sys::Pi);
        val Pi_c = List.foldr UNION_foldfun Pi_a_minus_b Pi_b;
        val tm_l_set = if List.null Pi_c then pred_setSyntax.mk_empty (``:birs_state_t``) else pred_setSyntax.mk_set Pi_c;
(*
length Pi_a
length Pi_a_minus_b
length Pi_c
*)
      in
        prove(``^tm = IMAGE birs_symb_to_symbst ^tm_l_set``, cheat)
      end;

(*
    val conv = DIFF_UNION_CONV;
*)

    fun Pi_CONV conv tm =
      RAND_CONV (RAND_CONV (conv)) tm;

    fun L_CONV conv tm =
      RAND_CONV (LAND_CONV (conv)) tm;

    val bprog_Pi_fixed_thm = CONV_RULE (RAND_CONV (Pi_CONV DIFF_UNION_CONV)) bprog_composed_thm;

    val bprog_L_fixed_thm  = CONV_RULE (RAND_CONV (L_CONV (
      SIMP_CONV
        (std_ss++HolBACoreSimps.holBACore_ss++birs_state_ss++pred_setLib.PRED_SET_ss)
        [bir_symbTheory.birs_symb_to_symbst_EQ_thm, pred_setTheory.INSERT_UNION]))) bprog_Pi_fixed_thm;

(*
    val bprog_composed_thm_1 =
      (SIMP_RULE
        (std_ss++HolBACoreSimps.holBACore_ss++birs_state_ss++pred_setLib.PRED_SET_ss)
        [bir_symbTheory.birs_symb_to_symbst_EQ_thm, pred_setTheory.INSERT_UNION]
        bprog_composed_thm);
    val _ = print "UNION\n";

    (* reconstruct IMAGE in the post state set *)
    val IMAGE_EMPTY_thm =
      Q.SPEC `birs_symb_to_symbst` (
        INST_TYPE [beta |-> Type`:(bir_programcounter_t, string, bir_exp_t, bir_status_t) symb_symbst_t`, alpha |-> Type`:birs_state_t`] 
        pred_setTheory.IMAGE_EMPTY
      );
    val _ = print "FIX\n";
    val bprog_composed_thm_2 =
      CONV_RULE
        (PAT_CONV ``\A. symb_hl_step_in_L_sound B (C, D, A)`` (REWRITE_CONV [GSYM IMAGE_EMPTY_thm, GSYM pred_setTheory.IMAGE_INSERT]))
        bprog_composed_thm_1
    val _ = print "IMAGE_INSERT\n";
*)
  in
    bprog_L_fixed_thm
  end;


end (* local *)

end (* struct *)
