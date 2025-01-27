open HolKernel boolLib Parse bossLib;

open markerTheory wordsTheory wordsLib;

open addressTheory;

open holba_auxiliaryTheory;

open bir_programSyntax bir_program_labelsTheory;
open bir_immTheory bir_valuesTheory bir_expTheory bir_exp_immTheory;
open bir_tsTheory bir_bool_expTheory bir_programTheory;

open bir_riscv_backlifterTheory;
open bir_backlifterLib;
open bir_compositionLib;

open bir_lifting_machinesTheory;
open bir_typing_expTheory;
open bir_htTheory;

open total_program_logicTheory;
open total_ext_program_logicTheory;

open jgmt_rel_bir_contTheory;

open pred_setTheory;

open program_logicSimps;

open bir_env_oldTheory;
open bir_program_varsTheory;

open HolBACoreSimps;

open chachaTheory;
open chacha_specTheory;
open chacha_symb_transf_column_roundTheory;

val _ = new_theory "chacha_column_round_prop";

Definition riscv_chacha_column_round_pre_def:
 riscv_chacha_column_round_pre 
  (pre_arr_0:word32) (pre_arr_1:word32) (pre_arr_2:word32) (pre_arr_3:word32)
  (pre_arr_4:word32) (pre_arr_5:word32) (pre_arr_6:word32) (pre_arr_7:word32) 
  (pre_arr_8:word32) (pre_arr_9:word32) (pre_arr_10:word32) (pre_arr_11:word32) 
  (pre_arr_12:word32) (pre_arr_13:word32) (pre_arr_14:word32) (pre_arr_15:word32)
 (m:riscv_state) : bool =
 (T)
End

Definition riscv_chacha_column_round_post_def:
 riscv_chacha_column_round_post
  (pre_arr_0:word32) (pre_arr_1:word32) (pre_arr_2:word32) (pre_arr_3:word32)
  (pre_arr_4:word32) (pre_arr_5:word32) (pre_arr_6:word32) (pre_arr_7:word32) 
  (pre_arr_8:word32) (pre_arr_9:word32) (pre_arr_10:word32) (pre_arr_11:word32) 
  (pre_arr_12:word32) (pre_arr_13:word32) (pre_arr_14:word32) (pre_arr_15:word32)
 (m:riscv_state) : bool =
 (T)
End

(* ------------------------------------- *)
(* Connecting RISC-V and BSPEC contracts *)
(* ------------------------------------- *)

Theorem chacha_column_round_riscv_pre_imp_bspec_pre_thm:
 bir_pre_riscv_to_bir
  (riscv_chacha_column_round_pre pre_arr_0 pre_arr_1 pre_arr_2 pre_arr_3 pre_arr_4 pre_arr_5 pre_arr_6
    pre_arr_7 pre_arr_8 pre_arr_9 pre_arr_10 pre_arr_11 pre_arr_12
    pre_arr_13 pre_arr_14 pre_arr_15)
  (bspec_chacha_column_round_pre pre_arr_0 pre_arr_1 pre_arr_2 pre_arr_3 pre_arr_4 pre_arr_5 pre_arr_6
    pre_arr_7 pre_arr_8 pre_arr_9 pre_arr_10 pre_arr_11 pre_arr_12
    pre_arr_13 pre_arr_14 pre_arr_15)
Proof 
 cheat
QED

Theorem chacha_column_round_riscv_post_imp_bspec_post_thm:
 !ls. bir_post_bir_to_riscv
   (riscv_chacha_column_round_post pre_arr_0 pre_arr_1 pre_arr_2 pre_arr_3 pre_arr_4 pre_arr_5 pre_arr_6
     pre_arr_7 pre_arr_8 pre_arr_9 pre_arr_10 pre_arr_11 pre_arr_12 pre_arr_13 pre_arr_14 pre_arr_15)
   (\l. (bspec_chacha_column_round_post pre_arr_0 pre_arr_1 pre_arr_2 pre_arr_3 pre_arr_4 pre_arr_5 pre_arr_6
          pre_arr_7 pre_arr_8 pre_arr_9 pre_arr_10 pre_arr_11 pre_arr_12 pre_arr_13 pre_arr_14 pre_arr_15))
   ls
Proof
 cheat
QED

(* --------------------- *)
(* Auxiliary definitions *)
(* --------------------- *)

val progbin_tm = (fst o dest_eq o concl) bir_chacha_progbin_def;
val riscv_pre_tm = (fst o dest_comb o lhs o snd o strip_forall o concl) riscv_chacha_column_round_pre_def;
val riscv_post_tm = (fst o dest_comb o lhs o snd o strip_forall o concl) riscv_chacha_column_round_post_def;

(* ---------------------------------- *)
(* Backlifting BIR contract to RISC-V *)
(* ---------------------------------- *)

val riscv_cont_chacha_column_round_thm =
 get_riscv_contract
  bspec_cont_chacha_column_round
  progbin_tm riscv_pre_tm riscv_post_tm
  bir_chacha_prog_def
  [bspec_chacha_column_round_pre_def]
  bspec_chacha_column_round_pre_def chacha_column_round_riscv_pre_imp_bspec_pre_thm
  [bspec_chacha_column_round_post_def] chacha_column_round_riscv_post_imp_bspec_post_thm
  bir_chacha_riscv_lift_THM;

Theorem riscv_cont_chacha_column_round:
 riscv_cont bir_chacha_progbin chacha_column_round_init_addr {chacha_column_round_end_addr}
 (riscv_chacha_column_round_pre pre_arr_0 pre_arr_1 pre_arr_2 pre_arr_3 pre_arr_4 pre_arr_5 pre_arr_6
   pre_arr_7 pre_arr_8 pre_arr_9 pre_arr_10 pre_arr_11 pre_arr_12 pre_arr_13 pre_arr_14 pre_arr_15)
 (riscv_chacha_column_round_post pre_arr_0 pre_arr_1 pre_arr_2 pre_arr_3 pre_arr_4 pre_arr_5 pre_arr_6
   pre_arr_7 pre_arr_8 pre_arr_9 pre_arr_10 pre_arr_11 pre_arr_12 pre_arr_13 pre_arr_14 pre_arr_15)
Proof
 rw [chacha_column_round_init_addr_def,chacha_column_round_end_addr_def] >>
 ACCEPT_TAC riscv_cont_chacha_column_round_thm
QED

(* ------------------------ *)
(* Unfolded RISC-V contract *)
(* ------------------------ *)

val readable_thm = computeLib.RESTR_EVAL_RULE [``riscv_weak_trs``] riscv_cont_chacha_column_round;
Theorem riscv_cont_chacha_column_round_full = GEN_ALL readable_thm;

val _ = export_theory ();
