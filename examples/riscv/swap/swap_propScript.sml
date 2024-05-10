open HolKernel boolLib Parse bossLib;

open bir_programSyntax bir_program_labelsTheory;
open bir_immTheory bir_valuesTheory bir_expTheory;
open bir_tsTheory bir_bool_expTheory bir_programTheory;

open bir_riscv_backlifterTheory;
open bir_backlifterLib;
open bir_compositionLib;

open bir_wpLib bir_wp_expLib;
open bir_wpTheory bir_htTheory;
open bir_wp_interfaceLib;

open tutorial_smtSupportLib;

open bir_symbTheory;
open bir_program_transfTheory;

open total_program_logicTheory;
open total_ext_program_logicTheory;
open symb_prop_transferTheory;

open jgmt_rel_bir_contTheory;

open birs_stepLib;

open swapTheory;

open swap_symb_execTheory;

val _ = new_theory "swap_prop";

Definition swap_mem_spec_def:
 swap_mem_spec ms =
 let ms'_mem8 = (riscv_mem_store_dword (ms.c_gpr ms.procID 0w)
   (riscv_mem_load_dword ms.MEM8 (ms.c_gpr ms.procID 1w)) ms.MEM8)
 in
   (riscv_mem_store_dword (ms.c_gpr ms.procID 1w)
    (riscv_mem_load_dword ms.MEM8 (ms.c_gpr ms.procID 0w)) ms'_mem8)
End

Definition swap_spec_output_def:
 swap_spec_output ms : riscv_state = ms with MEM8 := swap_mem_spec ms
End

Definition swap_spec_def:
 swap_spec ms ms' : bool = (ms'.MEM8 = swap_mem_spec ms)
End

Definition riscv_swap_pre_def:
 riscv_swap_pre (m : riscv_state) = F
End

Definition riscv_swap_post_def:
 riscv_swap_post (m : riscv_state) = T
End

Definition bir_swap_pre_def:
  bir_swap_pre : bir_exp_t = bir_exp_false
End

Definition bir_swap_post_def:
 bir_swap_post : bir_exp_t = bir_exp_true
End

Theorem swap_riscv_pre_imp_bir_pre_thm:
 bir_pre_riscv_to_bir riscv_swap_pre bir_swap_pre
Proof
 EVAL_TAC >> rw []
QED

Theorem swap_riscv_post_imp_bir_post_thm:
 !ls. bir_post_bir_to_riscv riscv_swap_post (\l. bir_swap_post) ls
Proof
 EVAL_TAC >> rw []
QED

(* TODO: re-enable symbolic analysis once free-variable problem is solved *)

(*
val (sys_i, L_s, Pi_f) = (symb_sound_struct_get_sysLPi_fun o concl) swap_symb_analysis_thm;

Definition swap_analysis_L_def:
 swap_analysis_L = ^(L_s)
End

val birs_state_init_lbl = ``<|bpc_label := BL_Address (Imm64 0w); bpc_index := 0|>``;
val birs_state_end_lbl = (snd o dest_eq o concl o EVAL) ``bir_block_pc (BL_Address (Imm64 20w))``;
*)

val prog_tm = (lhs o concl) bir_swap_prog_def;
val prefix = "swap_entry_";
val first_block_label_tm = ``BL_Address (Imm64 0w)``;
val ending_set = ``{BL_Address (Imm64 20w)}``;
val postcond_tm = ``\l : bir_label_t . if l = BL_Address (Imm64 20w) then bir_swap_post else bir_exp_false``;
val defs = [bir_swap_prog_def, bir_swap_post_def, bir_swap_pre_def, type_of_bir_exp_def,
            bir_exp_false_def, bir_exp_true_def, BType_Bool_def,bir_is_bool_exp_def,
            type_of_bir_imm_def];

val (bir_swap_entry_ht, bir_swap_entry_wp_tm) =
  bir_obtain_ht prog_tm first_block_label_tm
                ending_set ending_set_to_sml_list
                postcond_tm postcond_exp_from_label
                prefix defs;

Definition bir_swap_entry_wp_def:
 bir_swap_entry_wp = ^bir_swap_entry_wp_tm
End
val _ = save_thm("bir_swap_entry_ht", bir_swap_entry_ht);

val bir_swap_pre_tm = (lhs o concl) bir_swap_pre_def;
val bir_swap_pre_imp = bimp (bir_swap_pre_tm, bir_swap_entry_wp_tm);
val bir_swap_pre_imp_taut_thm = prove_exp_is_taut bir_swap_pre_imp;

val bir_cont_swap =
  bir_exec_to_labels_triple_to_bir_cont_predset bir_swap_entry_ht bir_swap_pre_imp_taut_thm;
val _= save_thm ("bir_cont_swap", bir_cont_swap);

(* For debugging:

val bir_ct = bir_cont_swap;
val prog_bin = ``bir_swap_progbin``;
val riscv_pre = ``riscv_swap_pre``;
val riscv_post = ``riscv_swap_post``;
val bir_prog_def = bir_swap_prog_def;
val bir_pre_defs = [bir_swap_pre_def]
val bir_pre1_def = bir_swap_pre_def;
val riscv_pre_imp_bir_pre_thm = swap_riscv_pre_imp_bir_pre_thm;
val bir_post_defs = [bir_swap_post_def];
val riscv_post_imp_bir_post_thm = swap_riscv_post_imp_bir_post_thm;
val bir_is_lifted_prog_thm = bir_swap_riscv_lift_THM;
*)

val riscv_swap_contract_thm = save_thm("riscv_swap_contract_thm",
 get_riscv_contract_sing
  bir_cont_swap
  ``bir_swap_progbin``
  ``riscv_swap_pre`` ``riscv_swap_post`` bir_swap_prog_def
  [bir_swap_pre_def]
  bir_swap_pre_def swap_riscv_pre_imp_bir_pre_thm
  [bir_swap_post_def] swap_riscv_post_imp_bir_post_thm
  bir_swap_riscv_lift_THM);

val _ = export_theory ();
