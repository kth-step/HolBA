open HolKernel Parse boolLib bossLib;

(* From tools/wp: *)
open bir_wpLib bir_wp_expLib bir_htLib;
open easy_noproof_wpLib;
open bir_wpTheory bir_htTheory;

(* From theory/bir-support: *)
open bir_program_labelsTheory bir_program_valid_stateTheory
     bir_program_blocksTheory bir_program_multistep_propsTheory
     bir_subprogramTheory;
open bir_bool_expSyntax;

(* From theory/bir: *)
open bir_programTheory;
open bir_expSyntax bir_programSyntax bir_immSyntax;
open HolBACoreSimps;

(* From shared: *)
open bir_exp_to_wordsLib bslSyntax;

(* From examples: *)
open examplesBinaryTheory;
open tutorial_bir_to_armSupportTheory;
open tutorial_bir_to_armTheory;
open examplesBinaryLib;
open tutorial_wpSupportLib;

(* From HOL4: *)
open finite_mapSyntax pairSyntax pred_setSyntax;

val _ = new_theory "tutorial_wp";

val prog_tm = (rhs o concl o EVAL) bir_prog_tm;
(******************     (1) bir_add_reg_entry      ********************)
(* The WP for the loop entry of the add_reg is generated and proved
 * here. *)
(* 1c -> 38 -> 3c -> 40 *)
val prefix = "add_reg_entry_";
val first_block_label_tm = ``BL_Address (Imm64 0x1cw)``; (* 28 *)
val last_block_label_tm =  ``BL_Address (Imm64 0x40w)``; (* 64 *)
val false_label_l = [];
val postcond_tm =
  (snd o dest_eq o concl o EVAL) ``bir_add_reg_contract_1_post``;
(* bir_add_reg_entry_htis the HT stating the generated WP: *)
val (bir_add_reg_entry_ht, bir_add_reg_entry_defs) =
  bir_obtain_ht prog_tm first_block_label_tm last_block_label_tm
                postcond_tm prefix false_label_l;

(* bir_add_reg_entry_wp is the weakest precondition obtained as a
 * term: *)
val bir_add_reg_entry_wp =
  (rhs o concl o EVAL o (el 4) o snd o strip_comb o concl) bir_add_reg_entry_ht;

val bir_add_reg_entry_wp_def = Define `bir_add_reg_entry_wp = ^(bir_add_reg_entry_wp)`;

(******************    (2)  bir_add_reg_loop     *********************)
(* The WP for the loop content is generated and proved here. *)
(* 20 -> 24 -> 28 -> 2c -> 30 -> 34 -> 38 -> 3c -> 40 *)
val prefix = "add_reg_loop_";
val first_block_label_tm = ``BL_Address (Imm64 0x20w)``;
val last_block_label_tm =  ``BL_Address (Imm64 0x40w)``;
val false_label_l = [];
val postcond_tm =
  (snd o dest_eq o concl o EVAL) ``bir_add_reg_contract_2_post``;
val (bir_add_reg_loop_ht, bir_add_reg_loop_defs) =
  bir_obtain_ht prog_tm first_block_label_tm last_block_label_tm
                postcond_tm prefix false_label_l;

val bir_add_reg_loop_wp =
  (rhs o concl o EVAL o (el 4) o snd o strip_comb o concl) bir_add_reg_loop_ht;

val bir_add_reg_loop_wp_def = Define `bir_add_reg_loop_wp = ^(bir_add_reg_loop_wp)`;

(**************   (3)  bir_add_reg_loop_continue     *****************)
(* This WP is for execution which starts at the loop condition and
 * then continues looping. *)
(* 40 -> 20 *)
val prefix = "add_reg_loop_continue_";
val first_block_label_tm = ``BL_Address (Imm64 0x40w)``;
val last_block_label_tm =  ``BL_Address (Imm64 0x20w)``;
val false_label_l = [``BL_Address (Imm64 0x44w)``];
val postcond_tm =
  (snd o dest_eq o concl o EVAL) ``bir_add_reg_contract_3_post``;
val (bir_add_reg_loop_continue_ht, bir_add_reg_loop_continue_defs) =
  bir_obtain_ht prog_tm first_block_label_tm last_block_label_tm
                postcond_tm prefix false_label_l;

val bir_add_reg_loop_continue_wp =
  (rhs o concl o EVAL o (el 4) o snd o strip_comb o concl) bir_add_reg_loop_continue_ht;

val bir_add_reg_loop_continue_wp_def = Define
  `bir_add_reg_loop_continue_wp = ^(bir_add_reg_loop_continue_wp)`;

(***************       bir_add_reg_loop_exit      *****************)
(* This WP is for execution which starts at the loop condition and
 * then exits the loop. Note that the blocks following 44 are
 * SP manipulation and return. *)
(* 40 -> 48 *)
val prefix = "add_reg_loop_exit_";
val first_block_label_tm = ``BL_Address (Imm64 0x40w)``;
val last_block_label_tm =  ``BL_Address (Imm64 0x48w)``;
val false_label_l = [``BL_Address (Imm64 0x20w)``];

val postcond_tm =
  (snd o dest_eq o concl o EVAL) ``bir_add_reg_contract_4_post``;

val (bir_add_reg_loop_exit_ht, bir_add_reg_loop_exit_defs) =
  bir_obtain_ht prog_tm first_block_label_tm last_block_label_tm
                postcond_tm prefix false_label_l;

val bir_add_reg_loop_exit_wp =
  (rhs o concl o EVAL o (el 4) o snd o strip_comb o concl) bir_add_reg_loop_exit_ht;

val bir_add_reg_loop_exit_wp_def = Define
  `bir_add_reg_loop_exit_wp = ^(bir_add_reg_loop_exit_wp)`;

(************           RECENT EXPERIMENTS           **************)
(*
(* Contract 1 *)
val contract_1_pre = (rhs o concl o EVAL) ``bir_add_reg_contract_1_pre``
val contract_1_imp = prove_imp_w_smt contract_1_pre bir_add_reg_entry_wp;

(* Contract 2 *)
val contract_2_pre = (rhs o concl o EVAL) ``bir_add_reg_contract_2_pre``;
val contract_2_imp = prove_imp_w_smt contract_2_pre bir_add_reg_loop_wp;

(* Contract 3 *)
val contract_3_pre = (rhs o concl o EVAL) ``bir_add_reg_contract_3_pre``;
val contract_3_imp = prove_imp_w_smt contract_3_pre bir_add_reg_loop_continue_wp;

(* Contract 4 *)
val contract_4_pre = (rhs o concl o EVAL) ``bir_add_reg_contract_4_pre``;
val contract_4_imp = prove_imp_w_smt contract_4_pre bir_add_reg_loop_exit_wp;
*)

(*
val test_def = Define `
cond = 
(BExp_BinExp BIExp_Or
               (BExp_UnaryExp BIExp_Not
                  (BExp_BinPred BIExp_Equal
                     (BExp_Den (BVar "ProcState_N" (BType_Imm Bit1)))
                     (BExp_Den (BVar "ProcState_V" (BType_Imm Bit1)))))
               (BExp_Den (BVar "ProcState_Z" (BType_Imm Bit1))))

`;

(rhs o concl) (REWRITE_CONV [GSYM test_def] wp_need);
(rhs o concl) (REWRITE_CONV [GSYM test_def] precondition);
REWRITE_RULE [GSYM test_def] bir_add_reg_loop_continue_ht;
 val _ = bir_ppLib.remove_bir_pretty_printers ();
 val _ = bir_ppLib.install_bir_pretty_printers ();


val x = bir2bool precondition;
HolSmtLib.Z3_ORACLE_PROVE x;
Z3_SAT_modelLib.Z3_GET_SAT_MODEL  (bir2bool (bnot precondition));
*)
(************              OLD STUFF                 **************)
(*
(****************** bir_add_reg_entry_contract ********************)
val prefix = "add_reg_entry_";
val first_block_label_tm = ``BL_Address (Imm64 0x40025cw)``;
(* TODO: Can be stated as a BL_Address?  *)
val last_block_label_tm =  ``BL_Address (Imm64 0x400280w)``;
val postcond_tm = (snd o dest_eq o concl o EVAL) ``bir_add_reg_contract_1_post``;
val bir_add_reg_entry_ht =
  bir_obtain_ht prog_tm first_block_label_tm last_block_label_tm
                postcond_tm prefix;

val precondition = ((el 4) o snd o strip_comb o concl o fst) bir_add_reg_entry_ht;
val precondition = (snd o dest_eq o concl o EVAL) precondition;



open bir_exp_to_wordsLib;
val x = bir2bool precondition;
HolSmtLib.Z3_ORACLE_PROVE x;
Z3_SAT_modelLib.Z3_GET_SAT_MODEL  (bir2bool (bnot precondition));

val x = bir2bool
 ((snd o dest_eq o concl o EVAL) (bor ((bnot ``bir_add_reg_contract_1_pre``), precondition)));
HolSmtLib.Z3_ORACLE_PROVE x;
Z3_SAT_modelLib.Z3_GET_SAT_MODEL  (mk_neg x);

EVAL ``((bir_vars_of_exp bir_add_reg_contract_1_pre) = (bir_vars_of_exp (^precondition)))``;


(****************** bir_add_reg_loop_contract ***********************)
val prefix = "add_reg_loop_";
val first_block_label_tm = ``BL_Address (Imm64 0x400260w)``;
(* TODO: Can be stated as a BL_Address?  *)
val last_block_label_tm =  ``BL_Address (Imm64 0x400280w)``;
val postcond_tm = (snd o dest_eq o concl o EVAL) ``bir_add_reg_contract_2_post``;
val bir_add_reg_entry_ht =
  bir_obtain_ht prog_tm first_block_label_tm last_block_label_tm
                postcond_tm prefix;

val precondition = ((el 4) o snd o strip_comb o concl o fst) bir_add_reg_entry_ht;
val precondition = (snd o dest_eq o concl o EVAL) precondition;

val x = bir2bool
 ((snd o dest_eq o concl o EVAL) (bor ((bnot ``bir_add_reg_contract_2_pre``), precondition)));
HolSmtLib.Z3_ORACLE_PROVE x;
Z3_SAT_modelLib.Z3_GET_SAT_MODEL  (mk_neg x);

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

(*
open bir_exp_to_wordsLib;

val x = bir2bool wp;
*)


(****************** bir_sqrt_loop_inv_contract ********************)
val first_block_label_tm = ``BL_Address (Imm64 0x400288w)``;
(* TODO: Can be stated as a BL_Address?  *)
val last_block_label_tm =
  ``BL_Address_HC (Imm64 0x400288w)
      "54FFFEC9 (b.ls 400260 <sqrt_+0x10>  // b.plast)"``;
val postcond_tm = (snd o dest_eq o concl) b_sqrt_I_def;
val bir_sqrt_entry_ht =
  bir_obtain_ht prog_tm first_block_label_tm last_block_label_tm
                postcond_tm;

(***************** bir_sqrt_loop_exit_contract ********************)
val first_block_label_tm = ``BL_Address (Imm64 0x400288w)``;
(* TODO: Can be stated as a BL_Address?  *)
val last_block_label_tm =
  ``BL_Address (Imm64 0x400294w)``;
val postcond_tm =
  ``(BExp_BinExp BIExp_And (b_sqrt_I)
      (BExp_UnaryExp BIExp_Not
        (BExp_Den (BVar "ProcState_C" BType_Bool))
      )
    )``;
val bir_sqrt_entry_ht =
  bir_obtain_ht prog_tm first_block_label_tm last_block_label_tm
                postcond_tm;


(* 33333333333333333333333333333333333333333333333333333333333333 *)
(****************** bir_sqrt_entry_contract ***********************)
(* This theorem would allow us to prove the contractual HT from
 * the generated one. *)
val bir_sqrt_entry_contract_roc =
  store_thm("bir_sqrt_entry_contract_roc",
  ``bir_triple_assumviol_free sqrt_prog
      (BL_Address (Imm64 0x400250w))
      (\x.(x = (BL_Address (Imm64 0x400284w))))
      bir_wp_comp_wps_iter_step2_wp_0x400250w
      sqrt_post ==>
    bir_triple_assumviol_free sqrt_prog
      (BL_Address (Imm64 0x400250w))
      (\x.(x = (BL_Address (Imm64 0x400284w))))
      (BExp_Const (Imm1 1w))
      b_sqrt_I``,

cheat
);

(******************************************************************)
(*                 Trying to define contracts                     *)
(* TODO: Add that the SP is higher than program code and smaller
 * than max stack. Both to precondition and invariant. *)
(* TODO: WHY DOES NO DEFINITION WORK? *)
(***                     TEST AREA                              ***)
(* The below apparently works... *)
val test = SPECL [``sqrt_prog``,
                  ``(BL_Address (Imm64 2132w))``,
                  ``(\x.(x = (BL_Address (Imm64 2192w))))``,
                  ``(BExp_Const (Imm1 1w))``,
                  ``b_sqrt_I``] bir_triple_assumviol_free_def;
(* Check type... *)
val test_ty = type_of ((snd o dest_eq o concl) sqrt_prog_def);
(* The below does not work either... :( *)
(* Nullary definition failed - giving up *)
val bir_sqrt_entry_contract_test_def = Define `
  test_def_triple = bir_exec_to_labels_or_assumviol_triple test_prog
`;
(* Nullary definition failed - giving up *)
val bir_sqrt_entry_contract_def = Define `
  bir_sqrt_entry_contract =
    bir_triple_assumviol_free sqrt_prog
      (BL_Address (Imm64 0x400250w))
      (\x.(x = (BL_Address (Imm64 0x400284w))))
      (BExp_Const (Imm1 1w))
      b_sqrt_I
`;
(* Nullary definition failed - giving up *)
val bir_sqrt_loop_inv_contract_def = Define `
  `bir_sqrt_loop_inv_contract =
     bir_triple_assumviol_free sqrt_prog
       (BL_Address (Imm64 0x400288w))
       {BL_Address (Imm64 0x400288w)}
       (BExp_BinExp BIExp_And (b_sqrt_I)
         (BExp_Den (BVar "ProcState_C" BType_Bool))
       )
       b_sqrt_I`;
(* Nullary definition failed - giving up *)
val bir_sqrt_loop_exit_contract_def = Define `
  `bir_sqrt_loop_exit_contract =
     bir_triple_assumviol_free sqrt_prog
       (BL_Address (Imm64 0x400288w))
       {BL_Address (Imm64 0x400294w)}
       (BExp_BinExp BIExp_And (b_sqrt_I)
	 (BExp_UnaryExp BIExp_Not
	   (BExp_Den (BVar "ProcState_C" BType_Bool))
	 )
       )
       (BExp_BinExp BIExp_And (b_sqrt_I)
	 (BExp_UnaryExp BIExp_Not
	   (BExp_Den (BVar "ProcState_C" BType_Bool))
	 )
       )`;
*)
(******************************************************************)

val _ = export_theory();
