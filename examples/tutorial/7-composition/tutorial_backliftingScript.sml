open HolKernel Parse boolLib bossLib;

open examplesBinaryTheory tutorial_bir_to_armTheory
     tutorial_compositionTheory;

open tutorial_backliftingLib;

val _ = new_theory "tutorial_backlifting";

(*****************************************************)
(*                    BACKLIFTING                    *)
(*****************************************************)

(* For debugging:
  val bir_ct = bir_add_reg_ct;
  val prog_bin = ``bir_add_reg_progbin``;
  val arm8_pre = ``arm8_add_reg_pre``;
  val arm8_post = ``arm8_add_reg_post``;
  val bir_prog_def = bir_add_reg_prog_def;
  val bir_pre_defs = [bir_add_reg_contract_1_pre_def, bir_add_reg_pre_def];
  val bir_pre1_def = bir_add_reg_contract_1_pre_def;
  val arm8_pre_imp_bir_pre_thm = arm8_pre_imp_bir_pre_thm;
  val bir_post_defs = [bir_add_reg_contract_4_post_def];
  val arm8_post_imp_bir_post_thm = arm8_post_imp_bir_post_thm;
  val bir_is_lifted_prog_thm = examplesBinaryTheory.bir_add_reg_arm8_lift_THM;
*)

val arm_add_reg_contract_thm = save_thm("arm_add_reg_contract_thm", get_arm8_contract_sing bir_add_reg_ct ``bir_add_reg_progbin`` ``arm8_add_reg_pre`` ``arm8_add_reg_post`` bir_add_reg_prog_def [bir_add_reg_contract_1_pre_def, bir_add_reg_pre_def] bir_add_reg_contract_1_pre_def arm8_pre_imp_bir_pre_thm [bir_add_reg_contract_4_post_def] arm8_post_imp_bir_post_thm examplesBinaryTheory.bir_add_reg_arm8_lift_THM);

val _ = export_theory();
