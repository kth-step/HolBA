open HolKernel Parse boolLib bossLib;
open bslSyntax;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = Globals.show_types := true;

(* Specialize observe types *)
val observe_type = Type `: 'a`;
val bdefprog_list = bdefprog_list observe_type;

(* No-op program *)
val noop_prog_def = bdefprog_list "noop_prog" [
  (blabel_str "prologue", [], (bjmp o belabel_str) "epilogue"),
  (blabel_str "epilogue", [], (bhalt o bconst32) 0)
];

(* Print it *)
val _ = print "noop_prog_def:\n";
val _ = Hol_pp.print_thm noop_prog_def;
val _ = print "\n";

(* Compare against the same hand-written BIR program *)
val noop_prog_tm = (snd o dest_eq o concl) noop_prog_def;
val is_correct = (noop_prog_tm = ``
  BirProgram [
    <|bb_label := BL_Label "prologue";
      bb_statements := [];
      bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "epilogue"))
    |>;
    <|bb_label := BL_Label "epilogue";
      bb_statements := [];
      bb_last_statement := BStmt_Halt (BExp_Const (Imm32 0w))
    |>
  ]``);

val _ = if is_correct
  then print "Ok.\n"
  else raise Fail "The BSL program isn't correct.";
