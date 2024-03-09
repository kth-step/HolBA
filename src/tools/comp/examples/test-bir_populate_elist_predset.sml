open HolKernel Parse boolLib bossLib;
open bslSyntax;

(* FIXME: needed to avoid quse errors *)
open m0_stepLib;

open bir_compositionLib;
open bir_bool_expTheory;

val observe_type = Type `: 'a`
val bdefprog_list = bdefprog_list observe_type

val p_def = bdefprog_list "p" [(blabel_str "entry", [], (bjmp o belabel_str) "0w"),
                               (blabel_str "0w", [], (bjmp o belabel_str) "1w"),
                               (blabel_str "1w", [], (bjmp o belabel_addr64) 2),
                               (blabel_addr64 2, [], (bhalt o bconst64) 0)]

val post = ``(\l. if (l = BL_Address (Imm64 2w)) then bir_exp_true else bir_exp_false)``
val c = prove(
  ``bir_cont p bir_exp_true (BL_Label "entry") {BL_Address (Imm64 2w) ; BL_Label "0w" ; BL_Label "1w"} {} bir_exp_true ^post``,
    cheat)

(* Check that string labels are handled correctly *)
val c' = bir_populate_elist_predset c
