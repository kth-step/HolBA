open HolKernel boolLib Parse bossLib;

open markerTheory;

open numTheory arithmeticTheory int_bitwiseTheory;
open pairTheory combinTheory wordsTheory;

open distribute_generic_stuffLib;

open bir_programSyntax bir_program_labelsTheory;
open bir_immTheory bir_valuesTheory bir_expTheory;
open bir_tsTheory bir_bool_expTheory bir_programTheory;

open bir_riscv_backlifterTheory;
open bir_backlifterLib;
open bir_compositionLib;

open bir_wpLib bir_wp_expLib;
open bir_wpTheory bir_htTheory;
open bir_wp_interfaceLib;

open bir_symbTheory birs_auxTheory;
open HolBACoreSimps;
open bir_program_transfTheory;

open total_program_logicTheory;
open total_ext_program_logicTheory;
open symb_prop_transferTheory;

open jgmt_rel_bir_contTheory;

open bir_symbTheory;
open birs_stepLib;
open bir_symb_sound_coreTheory;
open symb_recordTheory;
open symb_interpretTheory;

open pred_setTheory;

open program_logicSimps;

open distribute_generic_stuffTheory;

open mod2_memTheory;
open mod2_mem_specTheory;
open mod2_mem_symb_transfTheory;

val _ = new_theory "mod2_mem_prop";

(* --------------- *)
(* HL BIR contract *)
(* --------------- *)

val end_addr_tm = (snd o dest_eq o concl) mod2_mem_end_addr_def;

val bir_cont_mod2_mem_thm = use_post_weak_rule_simp
 (use_pre_str_rule_simp bspec_cont_mod2_mem mod2_mem_bir_pre_imp_bspec_pre)
 ``BL_Address (Imm64 ^end_addr_tm)``
 mod2_mem_bspec_post_imp_bir_post;

Theorem bir_cont_mod2_mem:
 bir_cont bir_mod2_mem_prog bir_exp_true
  (BL_Address (Imm64 mod2_mem_init_addr)) {BL_Address (Imm64 mod2_mem_end_addr)} {}
  (bir_mod2_mem_pre pre_x10 pre_x10_deref)
  (\l. if l = BL_Address (Imm64 mod2_mem_end_addr)
       then bir_mod2_mem_post pre_x10 pre_x10_deref
       else bir_exp_false)
Proof
 rw [mod2_mem_init_addr_def,mod2_mem_end_addr_def] >>
 ACCEPT_TAC bir_cont_mod2_mem_thm
QED

(* --------------------- *)
(* Auxiliary definitions *)
(* --------------------- *)

val progbin_tm = (fst o dest_eq o concl) bir_mod2_mem_progbin_def;
val riscv_pre_tm = (fst o dest_comb o lhs o snd o strip_forall o concl) riscv_mod2_mem_pre_def;
val riscv_post_tm = (fst o dest_comb o lhs o snd o strip_forall o concl) riscv_mod2_mem_post_def;

(* ---------------------------------- *)
(* Backlifting BIR contract to RISC-V *)
(* ---------------------------------- *)

val riscv_cont_mod2_mem_thm =
 get_riscv_contract
  bir_cont_mod2_mem
  progbin_tm riscv_pre_tm riscv_post_tm
  bir_mod2_mem_prog_def
  [bir_mod2_mem_pre_def]
  bir_mod2_mem_pre_def mod2_mem_riscv_pre_imp_bir_pre_thm
  [bir_mod2_mem_post_def] mod2_mem_riscv_post_imp_bir_post_thm
  bir_mod2_mem_riscv_lift_THM;

Theorem riscv_cont_mod2_mem:
 riscv_cont bir_mod2_mem_progbin mod2_mem_init_addr {mod2_mem_end_addr}
  (riscv_mod2_mem_pre pre_x10 pre_x10_deref)
  (riscv_mod2_mem_post pre_x10 pre_x10_deref)
Proof
 ACCEPT_TAC riscv_cont_mod2_mem_thm
QED

(* ------------------------ *)
(* Unfolded RISC-V contract *)
(* ------------------------ *)

val readable_thm = computeLib.RESTR_EVAL_RULE [``riscv_weak_trs``] riscv_cont_mod2_mem;
Theorem riscv_cont_mod2_mem_full = GEN_ALL readable_thm;

val _ = export_theory ();
