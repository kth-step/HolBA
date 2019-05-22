open HolKernel Parse boolLib bossLib;

open bir_wpLib;
open bir_wpTheory;
open bir_htTheory;
open bir_wp_expLib;
open bir_program_labelsTheory;
open bir_program_valid_stateTheory;
open bir_programTheory;
open bir_program_blocksTheory;
open bir_program_multistep_propsTheory;
open bir_subprogramTheory;

open bir_expSyntax;
open bir_programSyntax;
open bir_immSyntax;
open finite_mapSyntax bir_bool_expSyntax pairSyntax;
open bir_exp_to_wordsLib;
open pred_setSyntax;

open bir_htLib;
open examplesBinaryTheory;
open tutorial_bir_to_armSupportTheory;
open tutorial_bir_to_armTheory;
open HolBACoreSimps;
open examplesBinaryLib;
open bslSyntax;

val _ = new_theory "tutorial_wp";

(* Content:
 * 1. Theorem to obtain bir_triple from
 *    bir_exec_to_labels_or_assumviol_triple, given a program that
 *    has no Assume statements.
 * 2. WPs of the example code segments: loop entry, loop
 *    invariant and loop exit of sqrt program.
 * 3. Proof of the contracts using the RoC. *)

(* 11111111111111111111111111111111111111111111111111111111111111 *)
(* TODO: Move this... *)
val bir_exec_to_labels_exists =
  store_thm("bir_exec_to_labels_exists",
  ``!ls prog st.
      ?r.
        bir_exec_to_labels ls prog st = r``,

FULL_SIMP_TAC std_ss [bir_exec_to_labels_def]
);


val bir_never_assumviol_block_n_ht_from_to_labels_ht =
  store_thm("bir_never_assumviol_block_n_ht_from_to_labels_ht",
  ``!prog l ls pre post.
    bir_prog_has_no_assumes prog ==>
    bir_exec_to_labels_or_assumviol_triple prog l ls pre post ==>
    bir_triple prog l ls pre post``,

REWRITE_TAC [bir_triple_def,
             bir_exec_to_labels_or_assumviol_triple_def] >>
REPEAT STRIP_TAC >>
ASSUME_TAC (SPECL [``ls:bir_label_t -> bool``,
                   ``prog:'a bir_program_t``,
                   ``s:bir_state_t``] bir_exec_to_labels_exists) >>
FULL_SIMP_TAC std_ss [] >>
PAT_X_ASSUM ``!s'. _``
            (fn thm => ASSUME_TAC
              (SPEC ``s:bir_state_t`` thm)
            ) >>
REV_FULL_SIMP_TAC std_ss [] >| [
  FULL_SIMP_TAC std_ss [bir_exec_to_labels_def] >>
  IMP_RES_TAC bir_exec_to_labels_n_TO_bir_exec_block_n >>
  quantHeuristicsLib.QUANT_TAC [("n", `m`, []),
				("l1", `l1`, []),
				("c1", `c1`, []),
				("c2", `c_l'`, []),
				("s'", `s'`, [])] >>
  FULL_SIMP_TAC std_ss [],

  Cases_on `bir_is_valid_pc prog s.bst_pc` >| [
    FULL_SIMP_TAC std_ss
                  [bir_is_valid_pc_def,
                   bir_get_program_block_info_by_label_def] >>
    subgoal `?bl. bir_get_current_block prog s.bst_pc = SOME bl`
      >- (
      FULL_SIMP_TAC std_ss [bir_get_current_block_def]
    ) >>
    subgoal `s.bst_status <> BST_AssumptionViolated` >- (
      FULL_SIMP_TAC (std_ss++holBACore_ss) [] 
    ) >>
    IMP_RES_TAC bir_prog_not_assume_never_assumviol_exec_to_labels,

    (* This part is admittedly a bit of a yarn *)
    FULL_SIMP_TAC (std_ss++holBACore_ss)
                  [bir_exec_to_labels_def] >>
    IMP_RES_TAC bir_exec_to_labels_n_TO_bir_exec_step_n >>
    subgoal `~bir_state_is_terminated s` >- (
      FULL_SIMP_TAC std_ss [bir_state_is_terminated_def]
    ) >>
    IMP_RES_TAC bir_state_is_failed_step_not_valid_pc >>
    Cases_on `c1` >| [
      FULL_SIMP_TAC (std_ss++holBACore_ss)
                    [bir_exec_step_n_REWR_0],

      FULL_SIMP_TAC (std_ss++holBACore_ss)
                    [bir_exec_step_n_SUC,
                     bir_exec_step_state_def] >>
      Cases_on `(bir_exec_step prog s)` >>
      ASSUME_TAC (el 4 (CONJUNCTS bir_exec_step_n_REWRS)) >>
      FULL_SIMP_TAC (std_ss++holBACore_ss)
                    [bir_state_is_terminated_def, LET_DEF] >>
      REV_FULL_SIMP_TAC (std_ss++holBACore_ss) []
    ]
  ]
]
);

(* 22222222222222222222222222222222222222222222222222222222222222 *)

fun find_ht _            []     = NONE
  | find_ht target_label (h::t) =
  let
    val curr_label = (el 2 o snd o strip_comb o concl) h
  in
    if (term_eq curr_label target_label)
    then SOME h
    else find_ht target_label t
  end
;

fun make_false_label_fmap false_label_l =
  List.foldl (fn (label, map) => mk_fupdate (map, mk_pair (label, bir_exp_false_tm)))
             (mk_fempty (bir_label_t_ty, bir_exp_t_ty))
             false_label_l
;

(* TODO: Need to make sure a mess is not caused by overloading
 * definitions.
 *
 * This can be solved by passing an additional prefix/suffix to
 * bir_wp_comp_wps.
 *)
fun bir_obtain_ht prog_tm first_block_label_tm last_block_label_tm
                  postcond_tm prefix false_label_l =
  let
    (* TODO: Make some sort of test to check if computations have
     * already been performed for current prefix. *)
    (* Definitions: *)
    val prog_def = Define `
      ^(mk_var(prefix^"prog", type_of prog_tm)) = ^prog_tm
    `
    (*   For some reason prog requires this approach... *)
    val prog_var = Parse.Term [QUOTE (prefix^"prog")]
    val postcond_def = Define `
      ^(mk_var(prefix^"postcond", bir_exp_t_ty)) = ^postcond_tm
    `
    val postcond_var = (fst o dest_eq o concl) postcond_def
    val ls_def = Define `
      ^(mk_var(prefix^"ls", mk_set_type bir_label_t_ty)) =
        \x.(x = ^last_block_label_tm)
    `
    val ls_var = (fst o dest_eq o concl) ls_def
    val false_fmap_tm = make_false_label_fmap false_label_l
    val wps_def = Define `
      ^(mk_var(prefix^"wps", ``:bir_label_t |-> bir_exp_t``)) =
        ((^false_fmap_tm) |+ (^last_block_label_tm,
                    ^((fst o dest_eq o concl) postcond_def)
                   )
        )
    `
    val wps_var = (fst o dest_eq o concl) wps_def

    (* List of definitions: *)
    val defs = [prog_def, postcond_def, ls_def, wps_def]

    (* Initialize queue of blocks to process: *)
    val wps_tm =
      (snd o dest_comb o concl o (SIMP_CONV std_ss defs)) wps_var
(* For experimentation: 
val (program, post, ls) = (prog_var, postcond_var, ls_var)
val wps = wps_var
*)
    val wps_bool_sound_thm =
      bir_wp_init_wps_bool_sound_thm
        (prog_var, postcond_var, ls_var) wps_var defs
    val (wpsdom, blstodo) =
      bir_wp_init_rec_proc_jobs prog_tm wps_tm false_label_l

    (* Prepare "problem-static" part of computation: *)
    val prog_thm =
      bir_wp_comp_wps_iter_step0_init
        bir_wp_exec_of_block_reusable_thm
        (prog_var, postcond_var, ls_var) defs

    (* Main computation: *)
    val (wps1, wps1_bool_sound_thm) =
      bir_wp_comp_wps prog_thm ((wps_var, wps_bool_sound_thm),
				(wpsdom, List.rev blstodo))
			       (prog_var, postcond_var, ls_var) defs

    (* Pick out the soundness theorems, *)
    val sound_thms = ((el 2 o CONJUNCTS) wps1_bool_sound_thm)
    (* expand bir_sound_wps_map definition, *)
    val simp_thm2 =
      SIMP_RULE std_ss [bir_sound_wps_map_def] sound_thms
    (* transform the FEVERY into conjunctions for the individual
     * cases, *)
    val simp_thm3 =
      CONV_RULE finite_mapLib.fevery_EXPAND_CONV simp_thm2
    (* then simplify set-theoretical operations and address
     * equality. *)
    val simp_thm4 =
      SIMP_RULE (std_ss++holBACore_ss++wordsLib.WORD_ss++
		 wordsLib.WORD_ARITH_EQ_ss++pred_setLib.PRED_SET_ss)
		[ls_def, BL_Address_HC_def] simp_thm3
    (* CONJUNCTS now obtains a list with Hoare triples (plus an
     * abbreviation for the postcondition), from which we can pick
     * the theorem we need. *)
    val hts_list = CONJUNCTS simp_thm4
    val hts_list_trim = List.take (hts_list, (length hts_list) - 1)
    val target_ht =
      valOf (find_ht first_block_label_tm hts_list_trim)
    (* Transform HT to bir_triple *)
    (* TODO: Make bir_htSyntax *)
    val no_assumes_thm =
      REWRITE_RULE [GSYM prog_def]
        (bir_prog_has_no_assumes_pp
           ``bir_prog_has_no_assumes ^prog_tm``
        )
    val target_bir_triple =
      HO_MATCH_MP
        (HO_MATCH_MP bir_never_assumviol_block_n_ht_from_to_labels_ht
                     no_assumes_thm
        ) target_ht
    (* Obtain definition of WP expression *)
    val wp_name =
      "bir_wp_comp_wps_iter_step2_wp_"^
      ((term_to_string o snd o gen_dest_Imm o dest_BL_Address)
        first_block_label_tm)
    val final_wp_def =
      EVAL (Parse.Term [QUOTE wp_name])
  in
    (target_bir_triple, [prog_def, postcond_def, final_wp_def])
  end handle Option => raise ERR "extract_subprogram"
	("No Hoare triple was found for the addresses "^
	 (term_to_string first_block_label_tm)^" and "^
	 (term_to_string last_block_label_tm)^
	 ". Please double-check these addresses in the BIR "^
         "program.")
;

(******************************************************************)
open easy_noproof_wpLib;
val prog_tm = bir_prog_tm;
(****************** bir_add_reg_entry_contract ***********************)
val prefix = "add_reg_entry_";
val first_block_label_tm = ``BL_Address (Imm64 0x1cw)``;
val last_block_label_tm =  ``BL_Address (Imm64 0x40w)``;
val false_label_l = [];
val postcond_tm = (snd o dest_eq o concl o EVAL) ``bir_add_reg_contract_1_post``;
val (bir_add_reg_entry_ht, bir_add_reg_entry_def) =
  bir_obtain_ht prog_tm first_block_label_tm last_block_label_tm
                postcond_tm prefix false_label_l;

val wp_precondition_thm = bir_add_reg_entry_ht;


val precondition = ((el 4) o snd o strip_comb o concl) bir_add_reg_entry_ht;
val precondition = (snd o dest_eq o concl o EVAL) precondition;

(****************** bir_add_reg_loop_contract ***********************)
val prefix = "add_reg_loop_";
val first_block_label_tm = ``BL_Address (Imm64 0x20w)``;
val last_block_label_tm =  ``BL_Address (Imm64 0x40w)``;
val false_label_l = [];
val postcond_tm = (snd o dest_eq o concl o EVAL) ``bir_add_reg_contract_2_post``;
val (bir_add_reg_loop_ht, bir_add_reg_loop_def) =
  bir_obtain_ht prog_tm first_block_label_tm last_block_label_tm
                postcond_tm prefix false_label_l;

val precondition = ((el 4) o snd o strip_comb o concl) bir_add_reg_entry_ht;
val precondition = (snd o dest_eq o concl o EVAL) precondition;
val x = bir2bool precondition;

(************** bir_add_reg_loop_continue_contract *******************)
val prefix = "add_reg_loop_continue_";
val first_block_label_tm = ``BL_Address (Imm64 0x40w)``;
val last_block_label_tm =  ``BL_Address (Imm64 0x20w)``;
val false_label_l = [``BL_Address (Imm64 0x44w)``];
val postcond_tm = (snd o dest_eq o concl o EVAL) ``bir_add_reg_contract_3_pre``;
val (bir_add_reg_loop_continue_ht, bir_add_reg_loop_continue_def) =
  bir_obtain_ht prog_tm first_block_label_tm last_block_label_tm
                postcond_tm prefix false_label_l;

val precondition = ((el 4) o snd o strip_comb o concl) bir_add_reg_loop_continue_ht;
val precondition = (snd o dest_eq o concl o EVAL) precondition;
val wp_need = (rhs o rhs o concl o (REWRITE_CONV [bir_add_reg_I_def, bir_valuesTheory.BType_Bool_def]) o concl) bir_add_reg_contract_3_pre_def;

fun prove_imp_w_smt lhs rhs =
  let
    val bir_impl = bor (bnot lhs, rhs)
    val w_tm = bir2bool bir_impl
  in
    HolSmtLib.Z3_ORACLE_PROVE w_tm

    handle HOL_ERR e => let
      val neg_tm = mk_neg w_tm
      val model = Z3_SAT_modelLib.Z3_GET_SAT_MODEL neg_tm
      val _ = print "Failed to prove the implication. Anyways, have a SAT model:";
      val _ = PolyML.print model;
    in
      raise HOL_ERR e
    end
  end
;

(* Prove using Z3 *)

prove_imp_w_smt wp_need precondition;

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

(****************** bir_add_reg_entry_contract ***********************)
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
(******************************************************************)

val _ = export_theory();
