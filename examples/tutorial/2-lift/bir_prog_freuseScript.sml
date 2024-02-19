open HolKernel boolLib liteLib simpLib Parse bossLib;

open wordsTheory;

open bir_programTheory;

val _ = new_theory "bir_prog_freuse";

val freuse_def = Define `
  freuse = (BirProgram
[
(* add times two *)
    <|bb_label := BL_Address (Imm32 0x000w);
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
      bb_statements :=
        [BStmt_Assign (BVar "z" (BType_Imm Bit32))
                      (BExp_Den (BVar "c" (BType_Imm Bit32)))
        ];
      bb_last_statement := BStmt_Halt (BExp_Const (Imm32 0x0w))|>;

(* add *)
    <|bb_label := BL_Address (Imm32 0x100w);
      bb_statements :=
        [BStmt_Assign (BVar "c" (BType_Imm Bit32))
           (BExp_BinExp BIExp_Plus
              (BExp_Den (BVar "a" (BType_Imm Bit32)))
              (BExp_Den (BVar "b" (BType_Imm Bit32)))
           )];
      bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm32 0x104w)))|>;
    <|bb_label := BL_Address (Imm32 0x104w);
      bb_statements := [];
      bb_last_statement := BStmt_Jmp (BLE_Exp (BExp_Den (BVar "t" (BType_Imm Bit32))))|>;
]) : 'a bir_program_t
`;


val _ = export_theory();

