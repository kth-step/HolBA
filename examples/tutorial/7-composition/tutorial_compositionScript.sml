open HolKernel Parse boolLib bossLib;
open tutorial_bir_to_armTheory;
open tutorial_wpTheory;
open bslSyntax;

val string_ss = rewrites (type_rws ``:string``);
val char_ss = rewrites (type_rws ``:char``);

fun get_contract_prog contract_thm = ((el 1) o snd o strip_comb o concl) contract_thm;
fun get_contract_l contract_thm = ((el 2) o snd o strip_comb o concl) contract_thm;
fun get_contract_ls contract_thm = ((el 3) o snd o strip_comb o concl) contract_thm;
fun get_contract_pre contract_thm = ((el 4) o snd o strip_comb o concl) contract_thm;
fun get_contract_post contract_thm = ((el 5) o snd o strip_comb o concl) contract_thm;


fun use_impl_rule contract_thm pre =
  let 
    val prog = ((el 1) o snd o strip_comb o concl) contract_thm;
    val entry = ((el 2) o snd o strip_comb o concl) contract_thm;
    val exit = ((el 3) o snd o strip_comb o concl) contract_thm;
    val post = ((el 5) o snd o strip_comb o concl) contract_thm;
    val wp = ((el 4) o snd o strip_comb o concl) contract_thm;
    val pre_impl_wp = prove(``
      (bir_exp_is_taut (BExp_BinExp BIExp_Or (BExp_UnaryExp BIExp_Not ^pre) ^wp))
      ``, cheat);
    val pre_var_thm = prove (``
       ((bir_vars_of_exp ^pre) ⊆ (bir_vars_of_program ^prog))
       ``,
       computeLib.RESTR_EVAL_TAC [``bir_vars_of_exp``, ``bir_vars_of_program``] >>
       (SIMP_TAC (
       std_ss++pred_setSimps.PRED_SET_ss++HolBACoreSimps.holBACore_ss++stringSimps.STRING_ss++string_ss++char_ss++HolBASimps.VARS_OF_PROG_ss)
       ) [bir_valuesTheory.BType_Bool_def]
    );
    val wp_var_thm = prove (``
       ((bir_vars_of_exp ^wp) ⊆ (bir_vars_of_program ^prog))
       ``,
       computeLib.RESTR_EVAL_TAC [``bir_vars_of_exp``, ``bir_vars_of_program``] >>
       (SIMP_TAC (
       std_ss++pred_setSimps.PRED_SET_ss++HolBACoreSimps.holBACore_ss++stringSimps.STRING_ss++string_ss++char_ss++HolBASimps.VARS_OF_PROG_ss)
       ) [bir_valuesTheory.BType_Bool_def]
    );
    val new_contract_thm = ((SIMP_RULE (std_ss) [contract_thm, pre_impl_wp, wp_var_thm, pre_var_thm]) 
      ((SPECL [wp, pre, prog, entry, exit, post])
          bir_triple_weak_rule_thm)
          );
    in   new_contract_thm end;

val bir_add_contract_1 = use_impl_rule bir_add_reg_entry_ht ``bir_add_reg_contract_1_pre``;
val bir_add_contract_2 = use_impl_rule bir_add_reg_loop_ht ``bir_add_reg_contract_2_pre``;
val bir_add_contract_3 = use_impl_rule bir_add_reg_loop_continue_ht ``bir_add_reg_contract_3_pre``;
val bir_add_contract_4 = use_impl_rule bir_add_reg_loop_exit_ht ``bir_add_reg_contract_4_pre``;



val comp_seq_thm = prove(``
! l l1 ls prog P R Q.
(bir_triple prog l (\x.x=l1) P R) ==>
(bir_triple prog l1 ls R Q) ==>
(bir_triple prog l ls P Q)
``, cheat
);

val comp_loop_thm = prove(
``! l l1 ls prog invariant condition postcondition.
(bir_triple prog l1 (\x.x=l) (^(band(``invariant:bir_exp_t``, ``condition:bir_exp_t``))) invariant) ==>
(bir_triple prog l (\x.x=l1) (^(band(``invariant:bir_exp_t``, ``condition:bir_exp_t``))) (^(band(``invariant:bir_exp_t``, ``condition:bir_exp_t``)))) ==>
(bir_triple prog l ls (^(band(``invariant:bir_exp_t``, bnot ``condition:bir_exp_t``))) postcondition) ==>
(bir_triple prog l ls invariant postcondition)
``, cheat
);

val add_comp_loop_rule_thm =  SPECL [get_contract_l bir_add_contract_3,
       get_contract_l bir_add_contract_2,
       get_contract_ls bir_add_contract_4,
       get_contract_prog bir_add_contract_3,
       ``bir_add_reg_I``,
       ``bir_add_reg_loop_condition``,
       get_contract_post bir_add_contract_4
      ]
comp_loop_thm;

val add_reg_loop_contract_thm = prove(``
^(concl (UNDISCH_ALL add_comp_loop_rule_thm))
``,
REPEAT STRIP_TAC >>
ASSUME_TAC add_comp_loop_rule_thm >>

ASSUME_TAC bir_add_contract_2 >>
SUBGOAL_THEN ``
  (bir_add_reg_contract_2_pre = (BExp_BinExp BIExp_And bir_add_reg_I bir_add_reg_loop_condition)) /\
  (add_reg_loop_prog = add_reg_loop_continue_prog) /\
  (add_reg_loop_postcond = bir_add_reg_I)
`` (fn thm => FULL_SIMP_TAC std_ss (CONJUNCTS thm)) >- (EVAL_TAC) >>

ASSUME_TAC bir_add_contract_3 >>
SUBGOAL_THEN ``
  (bir_add_reg_contract_3_pre = (BExp_BinExp BIExp_And bir_add_reg_I bir_add_reg_loop_condition)) /\
  (add_reg_loop_continue_postcond = (BExp_BinExp BIExp_And bir_add_reg_I bir_add_reg_loop_condition)) /\
  (add_reg_loop_continue_prog = add_reg_loop_continue_prog)
`` (fn thm => FULL_SIMP_TAC std_ss (CONJUNCTS thm)) >- (EVAL_TAC) >>

ASSUME_TAC bir_add_contract_4 >>
SUBGOAL_THEN ``
  (bir_add_reg_contract_4_pre = (BExp_BinExp BIExp_And bir_add_reg_I
              (BExp_UnaryExp BIExp_Not bir_add_reg_loop_condition))) /\
  (add_reg_loop_exit_prog = add_reg_loop_continue_prog)
`` (fn thm => FULL_SIMP_TAC std_ss (CONJUNCTS thm)) >> EVAL_TAC
);





val add_comp_seq_rule_thm =  SPECL [get_contract_l bir_add_contract_1,
    get_contract_l add_reg_loop_contract_thm,
    get_contract_ls add_reg_loop_contract_thm,
    get_contract_prog add_reg_loop_contract_thm,
    ``bir_add_reg_pre``,
    get_contract_pre add_reg_loop_contract_thm,
    ``bir_add_reg_post``
      ]
comp_seq_thm;

val add_reg_contract_thm = prove(``
^(concl (UNDISCH_ALL add_comp_seq_rule_thm))
``,
REPEAT STRIP_TAC >>
ASSUME_TAC add_comp_seq_rule_thm >>

ASSUME_TAC bir_add_contract_1 >>
SUBGOAL_THEN ``
  (bir_add_reg_contract_1_pre = bir_add_reg_pre) /\
  (add_reg_entry_prog = add_reg_loop_continue_prog) /\
  (add_reg_entry_postcond = bir_add_reg_I)
`` (fn thm => FULL_SIMP_TAC std_ss (CONJUNCTS thm)) >- (EVAL_TAC) >>

ASSUME_TAC add_reg_loop_contract_thm >>
SUBGOAL_THEN ``
  (add_reg_loop_exit_postcond = bir_add_reg_post)
`` (fn thm => FULL_SIMP_TAC std_ss (CONJUNCTS thm)) >> (EVAL_TAC)
);





val add_lift_thm = SPECL [``add_reg_loop_continue_prog``,
      (((el 3) o snd o strip_comb o concl) examplesBinaryTheory.examples_arm8_program_THM),
      ``28w:word64``,
      ``{72w:word64}``,
      (((el 2) o snd o strip_comb o concl) examplesBinaryTheory.examples_arm8_program_THM),
      ``arm8_add_reg_pre``, ``arm8_add_reg_post``,
      get_contract_pre add_reg_contract_thm,
      get_contract_post add_reg_contract_thm
      ]
lift_contract_thm;

val arm_add_reg_contract_thm = prove(``
^(concl (UNDISCH_ALL add_lift_thm))
``,
REPEAT STRIP_TAC >>
ASSUME_TAC add_lift_thm >>
FULL_SIMP_TAC std_ss [EVAL ``MEM (^(get_contract_l add_reg_contract_thm)) (bir_labels_of_program add_reg_loop_continue_prog)``] >>

ASSUME_TAC add_reg_contract_thm >>
SUBGOAL_THEN ``
  ((λx. x = BL_Address (Imm64 72w)) = {BL_Address (Imm64 ml') | ml' ∈ {72w}})
`` (fn thm => FULL_SIMP_TAC std_ss (CONJUNCTS thm)) >- (cheat) >>

SUBGOAL_THEN ``
bir_is_lifted_prog arm8_bmr (WI_end 0w 0x1000000w)
           [(0w,
             [255w; 67w; 0w; 209w; 224w; 7w; 0w; 249w; 225w; 3w; 0w; 249w;
              226w; 7w; 64w; 249w; 227w; 3w; 64w; 249w; 228w; 7w; 64w; 249w;
              229w; 3w; 64w; 249w; 7w; 0w; 0w; 20w; 224w; 3w; 3w; 170w; 0w;
              4w; 0w; 145w; 227w; 3w; 0w; 170w; 224w; 3w; 2w; 170w; 0w; 4w;
              0w; 209w; 226w; 3w; 0w; 170w; 224w; 3w; 2w; 170w; 31w; 0w; 0w;
              241w; 12w; 255w; 255w; 84w; 224w; 3w; 3w; 170w; 255w; 67w; 0w;
              145w; 192w; 3w; 95w; 214w])] add_reg_loop_continue_prog
``  (fn thm=> FULL_SIMP_TAC std_ss [thm]) >-
 (FULL_SIMP_TAC std_ss [add_reg_loop_continue_prog_def, examplesBinaryTheory.examples_arm8_program_THM] >> cheat) >>

SUBGOAL_THEN ``arm8_wf_varset
           (bir_vars_of_program add_reg_loop_continue_prog ∪
            bir_vars_of_exp bir_add_reg_pre)`` (fn thm => FULL_SIMP_TAC std_ss [thm]) >- cheat >>

(*
       (SIMP_CONV (
       std_ss++pred_setSimps.PRED_SET_ss++HolBACoreSimps.holBACore_ss++stringSimps.STRING_ss++string_ss++char_ss++HolBASimps.VARS_OF_PROG_ss)
       ) [bir_valuesTheory.BType_Bool_def,
       add_reg_loop_continue_prog_def] ``arm8_wf_varset
           (bir_vars_of_program add_reg_loop_continue_prog ∪
            bir_vars_of_exp bir_add_reg_pre)``
            *)

FULL_SIMP_TAC (EVAL ``arm8_wf_varset (bir_vars_of_exp b_sqrt_I)``;


FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss++HolBACoreSimps.holBACore_ss) [] >>
METIS_TAC []