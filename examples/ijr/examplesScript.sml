open HolKernel Parse boolLib bossLib;

open bslSyntax bir_execLib bir_bool_expTheory bir_htSyntax;
open bir_wp_interfaceLib;
open tutorial_smtSupportLib;
open bir_compositionLib;

open resolveTheory resolveFullyTheory;
open resolveFullyLib;

val _ = new_theory "examples";


val _ = bir_ppLib.install_bir_pretty_printers();

val observe_type = Type `: 'a`
val bdefprog_list = bdefprog_list observe_type

val block1 = (blabel_addr32 0,
              [bassign (bvarimm32 "y", bconst32 4)],
              (bjmp o belabel_expr o bden o bvarimm32) "y")

val block2: term * term list * term  = (blabel_addr32 4,
                                        [],
                                        (bhalt o bconst32) 0)


(*Program definition*)
val prog_def = bdefprog_list "prog" [block1, block2]
val prog_tm = (rhs o concl) prog_def
(*val _ = bir_exec_prog_print "prog" prog_tm 10 NONE NONE NONE;*)

val prog_var = mk_var("prog", type_of prog_tm);
val prog_def = Define `^prog_var = ^prog_tm`;
val prog_tm' = (lhs o concl) prog_def


(*resolve_fail and resolve tests*)
val prog'_thm = EVAL “resolve_fail ^prog_tm (BL_Address (Imm32 0w)) (Imm32 4w)”
val prog'_tm = (dest_some o rhs o concl) prog'_thm
(*val _ = bir_exec_prog_print "prog'" prog'_tm 10 NONE NONE NONE;*)

val prog'_thm = EVAL “resolve ^prog_tm (BL_Address (Imm32 0w)) (Imm32 10w) "0w-1"”
val prog'_tm = (dest_some o rhs o concl) prog'_thm
(*val _ = bir_exec_prog_print "prog'" prog' n_max NONE NONE NONE;*)


(*resolve_fully test*)
val arg1 = “BL_Address (Imm32 0w)”
val arg2 = “[(Imm32 10w, "0w-1"); (Imm32 4w, "0w-2")]”
val arg3 = “Imm32 4w”
val prog'_thm = EVAL “resolve_fully ^prog_tm ^arg1 ^arg2 ^arg3”
val prog'_tm = (dest_some o rhs o concl) prog'_thm


(*resolve_fully_n one indirect jump test many steps*)
val args = “[(^arg1, ^arg2, ^arg3)]”
val prog'_thm = EVAL “resolve_fully_n ^prog_tm ^args”
val prog'_tm = (dest_some o rhs o concl) prog'_thm


(*resolve_fully_n many indirect jumps many steps test*)
val block1' = (blabel_addr32 8,
               [bassign (bvarimm32 "z", bconst32 4)],
               (bjmp o belabel_expr o bden o bvarimm32) "z")
val prog2_def = bdefprog_list "prog2" [block1, block2, block1']
val prog2_tm = (rhs o concl) prog2_def

val args = “[(^arg1, ^arg2, ^arg3);
             (BL_Address (Imm32 8w), [(Imm32 10w, "8w-1"); (Imm32 4w, "8w-2")], ^arg3)]”
val prog2'_thm = EVAL “resolve_fully_n ^prog2_tm ^args”
val prog2'_tm = (dest_some o rhs o concl) prog2'_thm


(*contract transfer test*)
(*Transform program*)
val args = “[(BL_Address (Imm32 0w), [(Imm32 4w, "0w-2")], ^arg3)]”
val (prog'_tm, prog'_def, prog'_thm) = resolve_indirect_jumps(prog_tm', args)

(*Obtain WP contract*)
val pre_def = Define ‘pre = bir_exp_true’;
val post_def = Define ‘post = ^(beq((bden o bvarimm32) "y", bconst32 4))’;

val prefix = "example_";
val entry_label_tm = “BL_Address (Imm32 0w)”;
val ending_labels_tm = “{BL_Address (Imm32 4w)}”;
val post_tm = “\l. if (l = BL_Address (Imm32 4w))
                   then post
                   else bir_exp_false”;
val defs = [prog'_def, post_def, bir_exp_false_def];

val (ht_thm, wp_tm) =
  bir_obtain_ht prog'_tm entry_label_tm
                ending_labels_tm ending_set_to_sml_list
                post_tm postcond_exp_from_label
                prefix defs;

val wp_def = Define `wp = ^(wp_tm)`;
val ht_thm' = REWRITE_RULE [GSYM wp_def] ht_thm;

(*
val defs = [prog_def, post_def, bir_exp_true_def, bir_exp_false_def];
val (ht, wp_tm) =
  bir_obtain_ht prog_tm entry_label_tm
                ending_labels_tm ending_set_to_sml_list
                post_tm postcond_exp_from_label
                prefix defs;
*)

(*Transfer WP contract*)
val ht'_thm = transfer_contract(prog_tm', prog'_thm, ht_thm')

(*Obtain contract by proving implication*)
val contract_pre = (lhs o concl) pre_def;
val contract_wp = (lhs o concl) wp_def;
val contract_imp = bimp (contract_pre, contract_wp);
val contract_imp_taut_thm = prove_exp_is_taut contract_imp;
val contract =
  label_ct_to_simp_ct_predset ht'_thm contract_imp_taut_thm;


val _ = export_theory();

