open HolKernel Parse boolLib bossLib;

open birs_stepLib;
open birs_composeLib;
open birs_driveLib;
open birs_auxTheory;

open bin_runningexampleTheory;

open bir_program_transfTheory;

val _ = new_theory "runningexample";

(*
val _ = print_term (concl bin_runningexample_thm);
*)

val bprog = List.nth((snd o strip_comb o concl) bin_runningexample_thm, 3);
(*
(hd o fst o listSyntax.dest_list o snd o dest_comb) bprog
(hd o tl o fst o listSyntax.dest_list o snd o dest_comb) bprog

List.nth ((fst o listSyntax.dest_list o snd o dest_comb) bprog, 13)
*)
Definition bprog_def:
  bprog = ^(bprog)
End
val bprog_tm = (fst o dest_eq o concl) bprog_def;
(* ........................... *)

(* motor_prep_input *)
val birs_state_init_lbl = (snd o dest_eq o concl o EVAL) ``bir_block_pc (BL_Address (Imm32 0x8006w))``;
(*
val birs_stop_lbls = [``<|bpc_label := BL_Address (Imm32 0xb08w); bpc_index := 7|>``];
*)
val birs_stop_lbls = [(snd o dest_eq o concl o EVAL) ``bir_block_pc (BL_Address (Imm32 0x8018w))``]; (* label 7 *)
val birs_stop_lbls = [(snd o dest_eq o concl o EVAL) ``bir_block_pc (BL_Address (Imm32 0x8016w))``]; (* label 6 *)




(* TODO: add a sanity check here that all the variables of the program are included in birenvtyl! *)


val birs_state_init = ``<|
  bsst_pc       := ^birs_state_init_lbl;
  bsst_environ  := bir_senv_GEN_list birenvtyl;
  bsst_status   := BST_Running;
  bsst_pcond    := BExp_BinExp BIExp_And
                     (BExp_BinExp BIExp_And
                       (BExp_BinPred BIExp_LessOrEqual
                         (BExp_Const (Imm32 0xFFFFFFw))
                         (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32))))
                       (BExp_BinExp BIExp_And
                         (BExp_BinPred BIExp_LessOrEqual
                           (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)))
                           (BExp_Const (Imm32 0xFFFFFFFBw)))
                         (BExp_Aligned Bit32 2 (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32))))))
                     (BExp_BinPred BIExp_LessOrEqual
                       (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 0xFFFFFFFFFFFFFF00w)))
|>``;
(* TODO: probably need this later in the path condition: 
  ``BExp_UnaryExp BIExp_Not (BExp_Den (BVar "ModeHandler" BType_Bool))``;
 *)
(* ........................... *)

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

val timer = holba_miscLib.timer_start 0;
val result = exec_until (birs_rule_STEP_fun_spec, birs_rule_SEQ_fun_spec, birs_rule_STEP_SEQ_fun_spec) single_step_A_thm birs_stop_lbls;
val _ = holba_miscLib.timer_stop (fn delta_s => print ("\n======\n > exec_until took " ^ delta_s ^ "\n")) timer;

val _ = (print_term o concl) result;

val _ = show_tags := true;
val _ = Portable.pprint Tag.pp_tag (tag result);



Theorem bin_runningexample_analysis_thm = result


val _ = export_theory();


(*


val testexp1 = ``
  (BExp_BinExp BIExp_And
     (BExp_BinExp BIExp_And
        (BExp_BinExp BIExp_And
           (BExp_BinPred BIExp_LessOrEqual (BExp_Const (Imm32 0xFFFFFFw))
              (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32))))
           (BExp_BinExp BIExp_And
              (BExp_BinPred BIExp_LessOrEqual
                 (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)))
                 (BExp_Const (Imm32 0xFFFFFFFBw)))
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)))
                    (BExp_Const (Imm32 3w))) (BExp_Const (Imm32 0w)))))
        (BExp_BinPred BIExp_LessOrEqual
           (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
           (BExp_Const (Imm64 0xFFFFFFFFFFFFFF00w))))
     (BExp_BinPred BIExp_Equal (BExp_Const (Imm32 8w))
        (BExp_Const (Imm32 0w))))
``;
val testexp2 = ``
  (BExp_UnaryExp BIExp_Not
     (BExp_Cast BIExp_LowCast
        (BExp_Load (BExp_Den (BVar "sy_MEM" (BType_Mem Bit32 Bit8)))
           (BExp_BinExp BIExp_Minus
              (BExp_BinExp BIExp_And
                 (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)))
                 (BExp_Const (Imm32 0xFFFFFFFCw))) (BExp_Const (Imm32 0w)))
           BEnd_LittleEndian Bit32) Bit1))``;



val testexp3 = ``BExp_Cast BIExp_LowCast
        (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)))
        Bit1``;


val testexp = ``BExp_BinExp BIExp_And ^testexp1 ^testexp2``;

val vars_empty = Redblackset.empty bir_smtLib.smtlib_vars_compare;

bir_smtLib.bexp_to_smtlib [] vars_empty testexp3

*)
