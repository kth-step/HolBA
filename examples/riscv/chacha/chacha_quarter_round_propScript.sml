open HolKernel boolLib Parse bossLib;

open markerTheory;

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

open chachaTheory;
open chacha_specTheory;
open chacha_symb_transf_quarter_roundTheory;

val _ = new_theory "chacha_quarter_round_prop";

Definition riscv_chacha_line_pre_def:
 riscv_chacha_line_pre (pre_a:word32)
  (pre_b:word32) (pre_d:word32)
  (m:riscv_state) : bool = T  
End

Definition riscv_chacha_line_post_def:
 riscv_chacha_line_post (pre_a:word32)
  (pre_b:word32) (pre_d:word32)
  (m:riscv_state) : bool = T  
End


(* ------------------------------------- *)
(* Connecting RISC-V and BSPEC contracts *)
(* ------------------------------------- *)

Theorem chacha_line_riscv_pre_imp_bspec_pre_thm:
 bir_pre_riscv_to_bir
  (riscv_chacha_line_pre pre_a pre_b pre_d)
  (bspec_chacha_line_pre pre_a pre_b pre_d)
Proof
 cheat
QED

Theorem chacha_line_riscv_post_imp_bspec_post_thm:
 !ls. bir_post_bir_to_riscv
   (riscv_chacha_line_post pre_a pre_b pre_d)
   (\l. (bspec_chacha_line_post pre_a pre_b pre_d))
   ls
Proof
 cheat
QED

(* --------------------- *)
(* Auxiliary definitions *)
(* --------------------- *)

val progbin_tm = (fst o dest_eq o concl) bir_chacha_progbin_def;
val riscv_pre_tm = (fst o dest_comb o lhs o snd o strip_forall o concl) riscv_chacha_line_pre_def;
val riscv_post_tm = (fst o dest_comb o lhs o snd o strip_forall o concl) riscv_chacha_line_post_def;

(* ---------------------------------- *)
(* Backlifting BIR contract to RISC-V *)
(* ---------------------------------- *)

val riscv_cont_chacha_line_thm =
 get_riscv_contract
  bspec_cont_chacha_line
  progbin_tm riscv_pre_tm riscv_post_tm
  bir_chacha_prog_def
  [bspec_chacha_line_pre_def]
  bspec_chacha_line_pre_def chacha_line_riscv_pre_imp_bspec_pre_thm
  [bspec_chacha_line_post_def] chacha_line_riscv_post_imp_bspec_post_thm
  bir_chacha_riscv_lift_THM;

Theorem riscv_cont_chacha_line:
 riscv_cont bir_chacha_progbin chacha_line_init_addr {chacha_line_end_addr}
 (riscv_chacha_line_pre pre_a pre_b pre_d)
 (riscv_chacha_line_post pre_a pre_b pre_d)
Proof
 rw [chacha_line_init_addr_def,chacha_line_end_addr_def] >>
 ACCEPT_TAC riscv_cont_chacha_line_thm
QED

(* ------------------------ *)
(* Unfolded RISC-V contract *)
(* ------------------------ *)

val readable_thm = computeLib.RESTR_EVAL_RULE [``riscv_weak_trs``] riscv_cont_chacha_line;
Theorem riscv_cont_chacha_line_full = GEN_ALL readable_thm;

val _ = export_theory ();
