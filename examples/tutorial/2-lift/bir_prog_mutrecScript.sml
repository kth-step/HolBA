open HolKernel boolLib liteLib simpLib Parse bossLib;

val _ = new_theory "bir_prog_mutrec";

(* The below program can be written in more human-readable form as

    0: Jmp (if n = 0 then 512 else 4)
    4: n := n-1; Jmp 256

    256: Jmp (if n = 0 then 516 else 260)
    260: n := n-1; Jmp 0

    512: r := T
    516: r := F

  Note that unlike the add_reg example, this program isn't actually lifted but manually written in BIR.

  The verification goal is to prove that

    [v1 = n] 0 -> {512, 516} [512 |-> v1 % 2 = 0, 516 |-> v1 % 2 = 1]

  and

    [v1 = n] 256 -> {512, 516} [512 |-> v1 % 2 = 1, 516 |-> v1 % 2 = 0]

  where v1 is a HOL4 variable and n is a BIR variable.

  The meaning of the contracts is that if is_even is called (0 is starting point), exit at 512 signifies
  that the initial value of n was even, and exit at 516 signifies that the initial value of n was odd.
  Vice versa holds for the entry point 256 associated with a call to is_odd.
*)


val mutrec_def = Define `
  mutrec = (BirProgram
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

