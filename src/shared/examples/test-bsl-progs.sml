open HolKernel Parse boolLib bossLib;
open bslSyntax;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = Globals.show_types := true;

(* Specialize observe types *)
val observe_type = Type `: 'a`
val bdefprog_list = bdefprog_list observe_type

fun test_eq (name, bsl_blocks, bir_prog_tm) =
  let
    val bsl_prog_def = bdefprog_list name bsl_blocks
    (* Print the BSL program *)
    val _ = print (name ^ ": \n")
    val _ = Hol_pp.print_thm bsl_prog_def
    val _ = print "\n"
    (* Compare against the same hand-written BIR program *)
    val bsl_prog_tm = (snd o dest_eq o concl) bsl_prog_def
    val is_correct = (identical bsl_prog_tm bir_prog_tm)
  in
    if is_correct
      then print "Ok.\n"
      else (
        print "Expected:\n";
        Hol_pp.print_term bir_prog_tm;
        print "\n";
        raise Fail ("The BSL program isn't correct: " ^ name)
      )
  end

val tests = [
  (* No-op program *)
  ("noop_prog",
    [
      (blabel_str "prologue", F, [], (bjmp o belabel_str) "epilogue"),
      (blabel_str "epilogue", F, [], (bhalt o bconst32) 0)
    ],
    ``BirProgram [
        <|bb_label := BL_Label "prologue";
          bb_atomic := F;
          bb_statements := [];
          bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "epilogue"))
        |>;
        <|bb_label := BL_Label "epilogue";
          bb_atomic := F;
          bb_statements := [];
          bb_last_statement := BStmt_Halt (BExp_Const (Imm32 0w))
        |>
      ]``),
  (* Program doing simple arithmetic *)
  ("simple_arith_prog",
    [
      (blabel_str "prologue", F, [], (bjmp o belabel_str) "plus_mult"),
      (blabel_str "plus_mult", F, [
        bassign (bvarimm 32 "x", bplusl [
          bconstii 32 0,
          bconstii 32 1,
          bmult (bconstii 32 21, bconstii 32 2),
          bconstii 32 3,
          bconstii 32 4
        ])
      ], (bjmp o belabel_str) "minus_div"),
      (blabel_str "minus_div", F, [
        bassign (bvarimm 32 "y", bminusl [
          bden (bvarimm 32 "x"),
          bconstii 32 1,
          bdivl [bconstii 32 1337, bconstii 32 191, bconstii 32 7],
          bconstii 32 3,
          bconstii 32 4
        ])
      ], (bjmp o belabel_str) "epilogue"),
      (blabel_str "epilogue", F, [], (bhalt o bconst32) 0)
    ],
    ``BirProgram [
        <|bb_label := BL_Label "prologue";
          bb_atomic := F;
          bb_statements := [];
          bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "plus_mult"))
        |>;
        <|bb_label := BL_Label "plus_mult";
          bb_atomic := F;
          bb_statements := [
            BStmt_Assign (BVar "x" (BType_Imm Bit32))
             (BExp_BinExp BIExp_Plus (BExp_Const (Imm32 (0w :word32)))
                (BExp_BinExp BIExp_Plus (BExp_Const (Imm32 (1w :word32)))
                   (BExp_BinExp BIExp_Plus
                      (BExp_BinExp BIExp_Mult
                         (BExp_Const (Imm32 (21w :word32)))
                         (BExp_Const (Imm32 (2w :word32))))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Const (Imm32 (3w :word32)))
                         (BExp_Const (Imm32 (4w :word32)))))))
          ];
          bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "minus_div"))
        |>;
        <|bb_label := BL_Label "minus_div";
          bb_atomic := F;
          bb_statements := [
            BStmt_Assign (BVar "y" (BType_Imm Bit32))
             (BExp_BinExp BIExp_Minus (BExp_Den (BVar "x" (BType_Imm Bit32)))
                (BExp_BinExp BIExp_Minus (BExp_Const (Imm32 (1w :word32)))
                   (BExp_BinExp BIExp_Minus
                      (BExp_BinExp BIExp_Div
                         (BExp_Const (Imm32 (1337w :word32)))
                         (BExp_BinExp BIExp_Div
                            (BExp_Const (Imm32 (191w :word32)))
                            (BExp_Const (Imm32 (7w :word32)))))
                      (BExp_BinExp BIExp_Minus
                         (BExp_Const (Imm32 (3w :word32)))
                         (BExp_Const (Imm32 (4w :word32)))))))
          ];
          bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "epilogue"))
        |>;
        <|bb_label := BL_Label "epilogue";
          bb_atomic := F;
          bb_statements := [];
          bb_last_statement := BStmt_Halt (BExp_Const (Imm32 0w))
        |>
      ]``)
]

val _ = List.map test_eq tests
val _ = print "All tests passed.\n"

