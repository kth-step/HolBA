open HolKernel Parse;

val _ = new_theory "birExamples2Binary";


val bprog_is_even_odd_def = Define `
  bprog_is_even_odd = (BirProgram
[
(* is_even *)
    <|bb_label := BL_Address (Imm32 0x000w);
      bb_statements :=
        [];
      bb_last_statement := BStmt_CJmp (BExp_BinPred BIExp_Equal
                                                      (BExp_Den (BVar "n" (BType_Imm Bit64)))
                                                      (BExp_Const (Imm64 0w)))
                                      (BLE_Label (BL_Address (Imm32 0x200w)))
                                      (BLE_Label (BL_Address (Imm32 0x004w)))|>;
    <|bb_label := BL_Address (Imm32 0x004w);
      bb_statements :=
        [BStmt_Assign (BVar "n" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Minus (BExp_Den (BVar "n" (BType_Imm Bit64))) (BExp_Const (Imm64 1w)));
        ];
      bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm32 0x100w)))|>;


(* is_odd *)
    <|bb_label := BL_Address (Imm32 0x100w);
      bb_statements :=
        [];
      bb_last_statement := BStmt_CJmp (BExp_BinPred BIExp_Equal
                                                      (BExp_Den (BVar "n" (BType_Imm Bit64)))
                                                      (BExp_Const (Imm64 0w)))
                                      (BLE_Label (BL_Address (Imm32 0x204w)))
                                      (BLE_Label (BL_Address (Imm32 0x104w)))|>;
    <|bb_label := BL_Address (Imm32 0x104w);
      bb_statements :=
        [BStmt_Assign (BVar "n" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Minus (BExp_Den (BVar "n" (BType_Imm Bit64))) (BExp_Const (Imm64 1w)));
        ];
      bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm32 0x000w)))|>;


(* yes *)
    <|bb_label := BL_Address (Imm32 0x200w);
      bb_statements :=
        [BStmt_Assign (BVar "r" (BType_Imm Bit1))
                      (BExp_Const (Imm1 1w))
        ];
      bb_last_statement := BStmt_Halt (BExp_Const (Imm32 0x0w))|>;


(* no *)
    <|bb_label := BL_Address (Imm32 0x204w);
      bb_statements :=
        [BStmt_Assign (BVar "r" (BType_Imm Bit1))
                      (BExp_Const (Imm1 0w))
        ];
      bb_last_statement := BStmt_Halt (BExp_Const (Imm32 0x0w))|>
]) : 'a bir_program_t
`;


val _ = export_theory();

