Theory add_reg_prop

Ancestors
 bir_prog_add_reg
 add_reg_arm8
 add_reg_bir
 add_reg_composition

Libs bir_backlifterLib

(*****************************************************)
(*                    BACKLIFTING                    *)
(*****************************************************)

val arm8_cont_add_reg_thm =
 get_arm8_contract_thm
  bir_add_reg_ct add_reg_init_addr_def [add_reg_end_addr_def]
  bir_add_reg_progbin_def
  arm8_add_reg_pre_def arm8_add_reg_post_def
  bir_add_reg_prog_def
  [bir_add_reg_contract_1_pre_def, bir_add_reg_pre_def]
  bir_add_reg_contract_1_pre_def arm8_pre_imp_bir_pre_thm
  [bir_add_reg_contract_4_post_def] arm8_post_imp_bir_post_thm
  bir_add_reg_arm8_lift_THM;

Theorem arm8_cont_add_reg:
 arm8_cont bir_add_reg_progbin
  add_reg_init_addr {add_reg_end_addr}
  arm8_add_reg_pre arm8_add_reg_post
Proof
 ACCEPT_TAC arm8_cont_add_reg_thm
QED
