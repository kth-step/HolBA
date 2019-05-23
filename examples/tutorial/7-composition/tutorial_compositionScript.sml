EVAL ``((bir_vars_of_exp bir_add_reg_contract_2_pre) = (bir_vars_of_exp (^precondition)))``;

val string_ss = rewrites (type_rws ``:string``);
val char_ss = rewrites (type_rws ``:char``);

val prog_tm = (extract_subprogram bir_prog_tm 0x40025c 0x40028c);


val prog_term = ((el 4) o snd o strip_comb o concl) examples_arm8_program_THM;

(SIMP_CONV (
std_ss++pred_setSimps.PRED_SET_ss++HolBACoreSimps.holBACore_ss++stringSimps.STRING_ss++string_ss++char_ss++HolBASimps.VARS_OF_PROG_ss)
) [bir_add_reg_contract_2_pre_def, bir_add_reg_I_def, bir_valuesTheory.BType_Bool_def] ``
((bir_vars_of_exp bir_add_reg_contract_2_pre)) ⊆
 ((bir_vars_of_program (^prog_term)))``;


(SIMP_CONV (
std_ss++pred_setSimps.PRED_SET_ss++HolBACoreSimps.holBACore_ss++stringSimps.STRING_ss++string_ss++char_ss++HolBASimps.VARS_OF_PROG_ss)
) [bir_add_reg_contract_2_pre_def, bir_add_reg_I_def, bir_valuesTheory.BType_Bool_def] ``
((bir_vars_of_exp bir_add_reg_contract_2_pre))``;

(SIMP_CONV (
std_ss++pred_setSimps.PRED_SET_ss++HolBACoreSimps.holBACore_ss++stringSimps.STRING_ss++string_ss++char_ss++HolBASimps.VARS_OF_PROG_ss)
) [bir_add_reg_contract_2_pre_def, bir_add_reg_I_def, bir_valuesTheory.BType_Bool_def] ``
 ((bir_vars_of_program (^prog_tm)))``;

EVAL ``((bir_vars_of_exp bir_add_reg_contract_2_pre))``;
EVAL ``(bir_vars_of_exp (^precondition))``;
