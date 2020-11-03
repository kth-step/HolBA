open HolKernel Parse boolLib bossLib;
open pretty_exnLib;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = Globals.show_tags := true;


val wp_tests =
[
  (* ========================================================================================================= *)
  (
    (* program name *)
    "addrs_eq_imp_x42",
    (* program term *)
    ``BirProgram [
      <|bb_label := BL_Label "entry";
	bb_statements := [];
	bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "mem_store"))
      |>;
      <|bb_label := BL_Label "mem_store"; (* init *)
	bb_statements := [
	  BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
	    (BExp_Store
	      (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
	      (BExp_Den (BVar "ADDR1" (BType_Imm Bit32)))
	      BEnd_BigEndian
	      (BExp_Const (Imm16 42w)))
	];
	bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "mem_load"))
      |>;
      <|bb_label := BL_Label "mem_load";
	bb_statements := [
	  BStmt_Assign (BVar "x" (BType_Imm Bit16))
	    (BExp_Load
	      (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
	      (BExp_Den (BVar "ADDR2" (BType_Imm Bit32)))
	      BEnd_BigEndian
	      Bit16)
	];
	bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "end"))
      |>;
      <|bb_label := BL_Label "end";
	bb_statements := [];
	bb_last_statement := BStmt_Halt (BExp_Const (Imm32 0w))
      |>
    ]``,
    (* Precondition *)
    (``BL_Label "entry"``,
     ``BExp_BinPred BIExp_Equal
         (BExp_Den (BVar "ADDR1" (BType_Imm Bit32)))
         (BExp_Den (BVar "ADDR2" (BType_Imm Bit32)))``),
    (* Postconditions *)
    ([``BL_Label "end"``],
     ``BExp_BinPred BIExp_Equal
         (BExp_Den (BVar "x" (BType_Imm Bit16)))
         (BExp_Const (Imm16 42w))
     ``),
    (* Expected WP *)
    ``BExp_BinExp BIExp_Or
      (BExp_UnaryExp BIExp_Not
         (BExp_BinPred BIExp_Equal
            (BExp_Den (BVar "ADDR1" (BType_Imm Bit32)))
            (BExp_Den (BVar "ADDR2" (BType_Imm Bit32)))))
      (BExp_BinPred BIExp_Equal
         (BExp_Load
            (BExp_Store (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
               (BExp_Den (BVar "ADDR1" (BType_Imm Bit32))) BEnd_BigEndian
               (BExp_Const (Imm16 42w)))
            (BExp_Den (BVar "ADDR2" (BType_Imm Bit32))) BEnd_BigEndian Bit16)
         (BExp_Const (Imm16 42w)))``
  ),

  (* ========================================================================================================= *)
  (
    (* program name *)
    "cjmp",
    (* program term *)
    ``BirProgram
       [<|bb_label := BL_Label "entry"; bb_statements := [];
          bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "assign_x_1"))|>;
        <|bb_label := BL_Label "assign_x_1";
          bb_statements :=
            [BStmt_Assign (BVar "x" (BType_Imm Bit32))
               (BExp_Const (Imm32 1w))];
          bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "cjmp"))|>;
        <|bb_label := BL_Label "cjmp"; bb_statements := [];
          bb_last_statement :=
            BStmt_CJmp
              (BExp_BinPred BIExp_Equal
                 (BExp_Den (BVar "x" (BType_Imm Bit32)))
                 (BExp_Const (Imm32 1w)))
              (BLE_Label (BL_Label "assign_y_100"))
              (BLE_Label (BL_Label "assign_y_200"))|>;
        <|bb_label := BL_Label "assign_y_100";
          bb_statements :=
            [BStmt_Assign (BVar "y" (BType_Imm Bit32))
               (BExp_Const (Imm32 100w))];
          bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "epilogue"))|>;
        <|bb_label := BL_Label "assign_y_200";
          bb_statements :=
            [BStmt_Assign (BVar "y" (BType_Imm Bit32))
               (BExp_Const (Imm32 200w))];
          bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "epilogue"))|>;
        <|bb_label := BL_Label "epilogue"; bb_statements := [];
          bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "end"))|>;
        <|bb_label := BL_Label "end"; bb_statements := [];
          bb_last_statement := BStmt_Halt (BExp_Const (Imm32 0w))|>]``,
    (* Precondition *)
    (``BL_Label "entry"``, ``BExp_Const (Imm1 1w)``),
    (* Postconditions *)
    ([``BL_Label "end"``],
    ``BExp_BinPred BIExp_Equal (BExp_Den (BVar "y" (BType_Imm Bit32)))
       (BExp_Const (Imm32 100w))``),
    (* Expected WP *)
    ``BExp_BinExp BIExp_Or (BExp_UnaryExp BIExp_Not (BExp_Const (Imm1 1w)))
      (BExp_BinExp BIExp_And
         (BExp_BinExp BIExp_Or
            (BExp_UnaryExp BIExp_Not
               (BExp_BinPred BIExp_Equal (BExp_Const (Imm32 1w))
                  (BExp_Const (Imm32 1w))))
            (BExp_BinPred BIExp_Equal (BExp_Const (Imm32 100w))
               (BExp_Const (Imm32 100w))))
         (BExp_BinExp BIExp_Or
            (BExp_BinPred BIExp_Equal (BExp_Const (Imm32 1w))
               (BExp_Const (Imm32 1w)))
            (BExp_BinPred BIExp_Equal (BExp_Const (Imm32 200w))
               (BExp_Const (Imm32 100w)))))``
  ),

  (* ========================================================================================================= *)
  (
    (* program name *)
    "gauss_no_mem_s3",
    (* program term *)
    ``BirProgram
       [<|bb_label := BL_Label "entry"; bb_statements := [];
          bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "ret_eq_0"))|>;
        <|bb_label := BL_Label "ret_eq_0";
          bb_statements :=
            [BStmt_Assign (BVar "ret" (BType_Imm Bit16))
               (BExp_Const (Imm16 0w))];
          bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "end"))|>;
        <|bb_label := BL_Label "end"; bb_statements := [];
          bb_last_statement := BStmt_Halt (BExp_Const (Imm32 0w))|>]``,
    (* Precondition *)
    (``BL_Label "entry"``,
    ``BExp_BinPred BIExp_Equal (BExp_Den (BVar "x" (BType_Imm Bit16)))
       (BExp_Den (BVar "x0" (BType_Imm Bit16)))``),
    (* Postconditions *)
    ([``BL_Label "end"``],
    ``BExp_BinPred BIExp_Equal
       (BExp_BinExp BIExp_Mult (BExp_Den (BVar "x0" (BType_Imm Bit16)))
          (BExp_BinExp BIExp_Plus (BExp_Den (BVar "x0" (BType_Imm Bit16)))
             (BExp_Const (Imm16 1w))))
       (BExp_BinExp BIExp_Plus
          (BExp_BinExp BIExp_Mult (BExp_Den (BVar "x" (BType_Imm Bit16)))
             (BExp_BinExp BIExp_Plus (BExp_Den (BVar "x" (BType_Imm Bit16)))
                (BExp_Const (Imm16 1w))))
          (BExp_BinExp BIExp_Mult (BExp_Den (BVar "ret" (BType_Imm Bit16)))
             (BExp_Const (Imm16 2w))))``),
    (* Expected WP *)
    ``BExp_BinExp BIExp_Or
      (BExp_UnaryExp BIExp_Not
         (BExp_BinPred BIExp_Equal (BExp_Den (BVar "x" (BType_Imm Bit16)))
            (BExp_Den (BVar "x0" (BType_Imm Bit16)))))
      (BExp_BinPred BIExp_Equal
         (BExp_BinExp BIExp_Mult (BExp_Den (BVar "x0" (BType_Imm Bit16)))
            (BExp_BinExp BIExp_Plus (BExp_Den (BVar "x0" (BType_Imm Bit16)))
               (BExp_Const (Imm16 1w))))
         (BExp_BinExp BIExp_Plus
            (BExp_BinExp BIExp_Mult (BExp_Den (BVar "x" (BType_Imm Bit16)))
               (BExp_BinExp BIExp_Plus
                  (BExp_Den (BVar "x" (BType_Imm Bit16)))
                  (BExp_Const (Imm16 1w))))
            (BExp_BinExp BIExp_Mult (BExp_Const (Imm16 0w))
               (BExp_Const (Imm16 2w)))))``
  ),

  (* ========================================================================================================= *)
  (
    (* program name *)
    "gauss_no_mem_s2",
    (* program term *)
    ``BirProgram
       [<|bb_label := BL_Label "entry"; bb_statements := [];
          bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "ret_add_x"))|>;
        <|bb_label := BL_Label "ret_add_x";
          bb_statements :=
            [BStmt_Assign (BVar "ret" (BType_Imm Bit16))
               (BExp_BinExp BIExp_Plus
                  (BExp_Den (BVar "ret" (BType_Imm Bit16)))
                  (BExp_Den (BVar "x" (BType_Imm Bit16))))];
          bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "x_dec"))|>;
        <|bb_label := BL_Label "x_dec";
          bb_statements :=
            [BStmt_Assign (BVar "x" (BType_Imm Bit16))
               (BExp_BinExp BIExp_Minus
                  (BExp_Den (BVar "x" (BType_Imm Bit16)))
                  (BExp_Const (Imm16 1w)))];
          bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "end"))|>;
        <|bb_label := BL_Label "end"; bb_statements := [];
          bb_last_statement := BStmt_Halt (BExp_Const (Imm32 0w))|>]``,
    (* Precondition *)
    (``BL_Label "entry"``,
    ``BExp_BinExp BIExp_And
       (BExp_BinPred BIExp_Equal
          (BExp_BinExp BIExp_Mult (BExp_Den (BVar "x0" (BType_Imm Bit16)))
             (BExp_BinExp BIExp_Plus (BExp_Den (BVar "x0" (BType_Imm Bit16)))
                (BExp_Const (Imm16 1w))))
          (BExp_BinExp BIExp_Plus
             (BExp_BinExp BIExp_Mult (BExp_Den (BVar "x" (BType_Imm Bit16)))
                (BExp_BinExp BIExp_Plus
                   (BExp_Den (BVar "x" (BType_Imm Bit16)))
                   (BExp_Const (Imm16 1w))))
             (BExp_BinExp BIExp_Mult
                (BExp_Den (BVar "ret" (BType_Imm Bit16)))
                (BExp_Const (Imm16 2w)))))
       (BExp_BinPred BIExp_LessThan (BExp_Const (Imm16 0w))
          (BExp_Den (BVar "x" (BType_Imm Bit16))))``),
    (* Postconditions *)
    ([``BL_Label "end"``],
    ``BExp_BinPred BIExp_Equal
       (BExp_BinExp BIExp_Mult (BExp_Den (BVar "x0" (BType_Imm Bit16)))
          (BExp_BinExp BIExp_Plus (BExp_Den (BVar "x0" (BType_Imm Bit16)))
             (BExp_Const (Imm16 1w))))
       (BExp_BinExp BIExp_Plus
          (BExp_BinExp BIExp_Mult (BExp_Den (BVar "x" (BType_Imm Bit16)))
             (BExp_BinExp BIExp_Plus (BExp_Den (BVar "x" (BType_Imm Bit16)))
                (BExp_Const (Imm16 1w))))
          (BExp_BinExp BIExp_Mult (BExp_Den (BVar "ret" (BType_Imm Bit16)))
             (BExp_Const (Imm16 2w))))``),
    (* Expected WP *)
    ``BExp_BinExp BIExp_Or
      (BExp_UnaryExp BIExp_Not
         (BExp_BinExp BIExp_And
            (BExp_BinPred BIExp_Equal
               (BExp_BinExp BIExp_Mult
                  (BExp_Den (BVar "x0" (BType_Imm Bit16)))
                  (BExp_BinExp BIExp_Plus
                     (BExp_Den (BVar "x0" (BType_Imm Bit16)))
                     (BExp_Const (Imm16 1w))))
               (BExp_BinExp BIExp_Plus
                  (BExp_BinExp BIExp_Mult
                     (BExp_Den (BVar "x" (BType_Imm Bit16)))
                     (BExp_BinExp BIExp_Plus
                        (BExp_Den (BVar "x" (BType_Imm Bit16)))
                        (BExp_Const (Imm16 1w))))
                  (BExp_BinExp BIExp_Mult
                     (BExp_Den (BVar "ret" (BType_Imm Bit16)))
                     (BExp_Const (Imm16 2w)))))
            (BExp_BinPred BIExp_LessThan (BExp_Const (Imm16 0w))
               (BExp_Den (BVar "x" (BType_Imm Bit16))))))
      (BExp_BinPred BIExp_Equal
         (BExp_BinExp BIExp_Mult (BExp_Den (BVar "x0" (BType_Imm Bit16)))
            (BExp_BinExp BIExp_Plus (BExp_Den (BVar "x0" (BType_Imm Bit16)))
               (BExp_Const (Imm16 1w))))
         (BExp_BinExp BIExp_Plus
            (BExp_BinExp BIExp_Mult
               (BExp_BinExp BIExp_Minus
                  (BExp_Den (BVar "x" (BType_Imm Bit16)))
                  (BExp_Const (Imm16 1w)))
               (BExp_BinExp BIExp_Plus
                  (BExp_BinExp BIExp_Minus
                     (BExp_Den (BVar "x" (BType_Imm Bit16)))
                     (BExp_Const (Imm16 1w))) (BExp_Const (Imm16 1w))))
            (BExp_BinExp BIExp_Mult
               (BExp_BinExp BIExp_Plus
                  (BExp_Den (BVar "ret" (BType_Imm Bit16)))
                  (BExp_Den (BVar "x" (BType_Imm Bit16))))
               (BExp_Const (Imm16 2w)))))``
  )

(*
  (* ========================================================================================================= *)
  (
    (* program name *)
    "",
    (* program term *)
    ````,
    (* Precondition *)
    (),
    (* Postconditions *)
    (),
    (* Expected WP *)
    ````
  )
*)
];

val _ = bir_fileLib.makedir true "tempdir";
val _ = OS.FileSys.chDir "tempdir";

(*
val (prog_name, prog, (entry_lbl, precond), (exit_lbls, postcond), wp_expect) = List.nth (wp_tests,0);
*)
fun wp_test_fun (prog_name, prog, (entry_lbl, precond), (exit_lbls, postcond), wp_expect) =
  let
    val _ = new_theory ("temp_" ^ prog_name);
    val prog_def = Define [QUOTE (prog_name ^ "_def = "), ANTIQUOTE prog];
    val wp = easy_noproof_wpLib.compute_p_imp_wp_tm prog_name prog_def (entry_lbl, precond) (exit_lbls, postcond);
  in
    if not (identical wp wp_expect) then
      raise Fail ("test-wp.sml::unexpected wp: " ^ prog_name)
    else
      print ("SUCCESS, WP as expected: " ^ prog_name ^ "\r\n")
  end;

val _ = List.map wp_test_fun wp_tests;
val _ = print ("SUCCESS, all WPs as expected\r\n")

