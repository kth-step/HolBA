open HolKernel Parse boolLib bossLib;

(* FIXME: needed to avoid quse errors *)
open m0_stepLib;

open bir_backlifterLib;

val _ = new_theory "mod2_backlifting";

(*
val arm_add_reg_contract_thm =
  save_thm("arm_add_reg_contract_thm",
  get_arm8_contract_sing bir_add_reg_ct ``bir_add_reg_progbin`` ``arm8_add_reg_pre``
                       ``arm8_add_reg_post`` bir_add_reg_prog_def
                       [bir_add_reg_contract_1_pre_def, bir_add_reg_pre_def]
                       bir_add_reg_contract_1_pre_def arm8_pre_imp_bir_pre_thm
                       [bir_add_reg_contract_4_post_def] arm8_post_imp_bir_post_thm
                       bir_prog_add_regTheory.bir_add_reg_arm8_lift_THM);

|- arm8_cont bir_add_reg_progbin 28w {72w} arm8_add_reg_pre arm8_add_reg_post
*)

val _ = export_theory ();
