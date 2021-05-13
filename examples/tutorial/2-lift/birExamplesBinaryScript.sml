open HolKernel boolLib liteLib simpLib Parse bossLib;

val _ = new_theory "birExamplesBinary";


val bprog_add_times_two_def = Define `
  bprog_add_times_two = (BirProgram
[
(* add times two *)
    <|bb_label := BL_Address (Imm32 0x000w);
      bb_atomic := F;
      bb_statements :=
        [BStmt_Assign (BVar "a" (BType_Imm Bit32))
                      (BExp_Den (BVar "x" (BType_Imm Bit32)));
         BStmt_Assign (BVar "b" (BType_Imm Bit32))
                      (BExp_Den (BVar "y" (BType_Imm Bit32)));
         BStmt_Assign (BVar "t" (BType_Imm Bit32))
                      (BExp_Const (Imm32 0x004w))
        ];
      bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm32 0x100w)))|>;
    <|bb_label := BL_Address (Imm32 0x004w);
      bb_atomic := F;
      bb_statements :=
        [BStmt_Assign (BVar "a" (BType_Imm Bit32))
                      (BExp_Den (BVar "c" (BType_Imm Bit32)));
         BStmt_Assign (BVar "b" (BType_Imm Bit32))
                      (BExp_Den (BVar "c" (BType_Imm Bit32)));
         BStmt_Assign (BVar "t" (BType_Imm Bit32))
                      (BExp_Const (Imm32 0x008w))
        ];
      bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm32 0x100w)))|>;
    <|bb_label := BL_Address (Imm32 0x008w);
      bb_atomic := F;
      bb_statements :=
        [BStmt_Assign (BVar "z" (BType_Imm Bit32))
                      (BExp_Den (BVar "c" (BType_Imm Bit32)))
        ];
      bb_last_statement := BStmt_Halt (BExp_Const (Imm32 0x0w))|>;

(* add *)
    <|bb_label := BL_Address (Imm32 0x100w);
      bb_atomic := F;
      bb_statements :=
        [BStmt_Assign (BVar "c" (BType_Imm Bit32))
           (BExp_BinExp BIExp_Plus
              (BExp_Den (BVar "a" (BType_Imm Bit32)))
              (BExp_Den (BVar "b" (BType_Imm Bit32)))
           )];
      bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm32 0x104w)))|>;
    <|bb_label := BL_Address (Imm32 0x104w);
      bb_atomic := F;
      bb_statements := [];
      bb_last_statement := BStmt_Jmp (BLE_Exp (BExp_Den (BVar "t" (BType_Imm Bit32))))|>;
]) : 'a bir_program_t
`;


val _ = export_theory();

