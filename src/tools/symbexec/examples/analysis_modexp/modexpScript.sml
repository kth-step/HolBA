open HolKernel Parse boolLib bossLib;

open birs_stepLib;
open birs_composeLib;
open birs_driveLib;
open birs_auxTheory;

open bin_balrob_smallprogsTheory;

open bir_program_transfTheory;

val _ = new_theory "modexp";

(*
val _ = print_term (concl bin_motor_func_thm);
*)

val bprog = List.nth((snd o strip_comb o concl) bin_balrob_smallprogs_thm, 3);
(*
(hd o fst o listSyntax.dest_list o snd o dest_comb) bprog
(hd o tl o fst o listSyntax.dest_list o snd o dest_comb) bprog

List.nth ((fst o listSyntax.dest_list o snd o dest_comb) bprog, 13)
*)
val bprog_def = Define `
    bprog = ^(bprog)
`;
val bprog_tm_ = (fst o dest_eq o concl) bprog_def;
(* ........................... *)

(* motor_prep_input *)
val birs_state_init_lbl = (snd o dest_eq o concl o EVAL) ``bir_block_pc (BL_Address (Imm32 0x100014f0w))``;

val birs_stop_lbls_ = [(snd o dest_eq o concl o EVAL) ``bir_block_pc (BL_Address (Imm32 0x1000150aw))``,
                       (snd o dest_eq o concl o EVAL) ``bir_block_pc (BL_Address (Imm32 0x1000155cw))``];




(* TODO: add a sanity check here that all the variables of the program are included in birenvtyl! *)

val birs_state_init_ = ``<|
  bsst_pc       := ^birs_state_init_lbl;
  bsst_environ  := bir_senv_GEN_list birenvtyl;
  bsst_status   := BST_Running;
  bsst_pcond    := BExp_BinExp BIExp_And
                     (BExp_BinExp BIExp_And
                       (BExp_BinExp BIExp_And
                        (BExp_BinPred BIExp_LessOrEqual
                         (BExp_Const (Imm32 0x10001A00w))
                         (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32))))
                        (BExp_BinPred BIExp_LessOrEqual
                         (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 0x10001FF0w))))
                       (BExp_Aligned Bit32 2 (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)))))
                     (BExp_BinPred BIExp_LessOrEqual
                       (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 0xFFFFFFFFFF000000w)))
|>``;
(* TODO: probably need this later in the path condition: 
  ``BExp_UnaryExp BIExp_Not (BExp_Den (BVar "ModeHandler" BType_Bool))``;
 *)


(* ........................... *)


fun birs_execute bprog_tm birs_state_init birs_stop_lbls =
  let
    val birs_rule_STEP_thm = birs_rule_STEP_prog_fun (bir_prog_has_no_halt_fun bprog_tm);
    val birs_rule_SUBST_thm = birs_rule_SUBST_prog_fun bprog_tm;
    val birs_rule_STEP_fun_spec = (birs_rule_SUBST_trysimp_const_add_subst_fun birs_rule_SUBST_thm o birs_rule_tryjustassert_fun true o birs_rule_STEP_fun birs_rule_STEP_thm bprog_tm);
    (* now the composition *)
    val birs_rule_SEQ_thm = birs_rule_SEQ_prog_fun bprog_tm;
    val birs_rule_SEQ_fun_spec = birs_rule_SEQ_fun birs_rule_SEQ_thm;
    (* ........................... *)

    val single_step_A_thm = birs_rule_STEP_fun_spec birs_state_init;
    (* ........................... *)

    (* and also the sequential composition *)
    val birs_rule_STEP_SEQ_thm = MATCH_MP birs_rulesTheory.birs_rule_STEP_SEQ_gen_thm (bir_prog_has_no_halt_fun bprog_tm);
    val birs_rule_STEP_SEQ_fun_spec = birs_rule_STEP_SEQ_fun (birs_rule_SUBST_thm, birs_rule_STEP_SEQ_thm);
    (* ........................... *)

    (*
    val tree = build_tree (birs_rule_STEP_fun_spec, birs_rule_SEQ_fun_spec, birs_rule_STEP_SEQ_fun_spec) single_step_A_thm birs_stop_lbls;
    val _ = print "done building the tree\n";
    *)

    val _ = print "now reducing it to one sound structure\n";

    val result = exec_until (birs_rule_STEP_fun_spec, birs_rule_SEQ_fun_spec, birs_rule_STEP_SEQ_fun_spec) single_step_A_thm birs_stop_lbls;
  in
    result
  end;





val result = birs_execute bprog_tm_ birs_state_init_ birs_stop_lbls_;
val (_, _, Pi_tm) = (symb_sound_struct_get_sysLPi_fun o concl) result;
val Pi_tm_l = symb_sound_struct_Pi_to_birstatelist_fun Pi_tm;
(* hd Pi_tm_l - infeasible, remove this branch and the added path condition *)

val loop_entry_state = List.nth (Pi_tm_l, 1);
(* need to generalize countw indirection *)
(* need to generalize loop iteration *)

(* get to branch and work with each branch individually *)

(* b1, execute to the mod, then apply the mod, deal with the return, fix the path condition and rename symbols to get back to standard form *)

(* b2, similar, but with two calls *)

(* then bring them together by forgetting values in the state, fix up the countw intervals for each branch and get them into a unified form *)

(* execute to the loop conditional branch *)

(* iterate and rename until leaving the loop finally *)

(* execute to the end *)

(* compose everything *)

(*
val timer = bir_miscLib.timer_start 0;

val _ = bir_miscLib.timer_stop (fn delta_s => print ("\n======\n > exec_until took " ^ delta_s ^ "\n")) timer;
val _ = (print_term o concl) result;

val _ = show_tags := true;
val _ = Portable.pprint Tag.pp_tag (tag result);

(* birs_stepLib *)
val (_, _, Pi_tm) = (symb_sound_struct_get_sysLPi_fun o concl) result;
val Pi_tm_l = symb_sound_struct_Pi_to_birstatelist_fun Pi_tm;

val countw_incs = List.map (fn s =>
  let
    (*
    val s = hd Pi_tm_l;
    *)
    val countw_exp = (snd o dest_eq o concl o EVAL) ``THE ((^s).bsst_environ "countw")``;
    val countw_inc_pat_tm = ``BExp_BinExp BIExp_Plus (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
       (BExp_Const (Imm64 incval))``;
    val (substv, _) = match_term countw_inc_pat_tm countw_exp;
    val countw_inc = subst substv ``incval:word64``;
  in
    countw_inc
  end) Pi_tm_l;
val _ = print "countw increments = [";
val _ = List.map (fn countw_inc => (print (term_to_string countw_inc); print "; ")) countw_incs;
val _ = print "]\n";

val _ = save_thm ("bin_smallprog_thm", result);
*)

val _ = export_theory();
