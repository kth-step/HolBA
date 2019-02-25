open HolKernel Parse;

open bir_execLib;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;



val _ = print "loading...";

val name = "my_crazy_program";

val prog1 = ``
       BirProgram [
         <|bb_label :=
             BL_Label "entry";
           bb_statements :=
             [BStmt_Assign (BVar "bit1" BType_Bool)
                           (BExp_MSB Bit32 (BExp_Den (BVar "R1" (BType_Imm Bit32))))];
           bb_last_statement :=
             BStmt_Jmp (BLE_Label (BL_Address (Imm32 0x102w)))|>;
         <|bb_label :=
             BL_Address_HC (Imm32 0x102w) "abc";
           bb_statements :=
             [BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                (BExp_Const (Imm32 25w));
              BStmt_Assign (BVar "R2" (BType_Imm Bit32))
                (BExp_Const (Imm32 7w))];
           bb_last_statement :=
             BStmt_Jmp (BLE_Label (BL_Address (Imm32 0x104w))) |>;
         <|bb_label :=
             BL_Address_HC (Imm32 0x104w) "eeee";
           bb_statements :=
             [BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                (BExp_BinExp BIExp_Plus
                   (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                   (BExp_Den (BVar "R3" (BType_Imm Bit32))))];
           bb_last_statement :=
             BStmt_Halt (BExp_Const (Imm32 1w)) |>
       ]``;

val prog2 = ``
       BirProgram [
         <|bb_label :=
             BL_Label "entry";
           bb_statements :=
             [BStmt_Assign (BVar "bit1" BType_Bool)
                           (BExp_MSB Bit32 (BExp_Den (BVar "R1" (BType_Imm Bit32))))];
           bb_last_statement :=
             BStmt_Jmp (BLE_Label (BL_Address (Imm32 0x102w)))|>;
         <|bb_label :=
             BL_Address_HC (Imm32 0x102w) "abc";
           bb_statements :=
             [BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                (BExp_Const (Imm32 25w));
              BStmt_Assign (BVar "R2" (BType_Imm Bit32))
                (BExp_Const (Imm32 7w))];
           bb_last_statement :=
             BStmt_CJmp (BExp_BinPred BIExp_Equal (BExp_Const (Imm32 8w)) (BExp_Den (BVar "R2" (BType_Imm Bit32))))
                        (BLE_Label (BL_Address (Imm32 0x104w)))
                        (BLE_Label (BL_Address (Imm32 0x106w))) |>;
         <|bb_label :=
             BL_Address_HC (Imm32 0x104w) "eeee";
           bb_statements :=
             [BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                (BExp_BinExp BIExp_Plus
                   (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                   (BExp_Den (BVar "R3" (BType_Imm Bit32))))];
           bb_last_statement :=
             BStmt_Halt (BExp_Const (Imm32 1w)) |>;
         <|bb_label :=
             BL_Address_HC (Imm32 0x106w) "eeeeggg";
           bb_statements :=
             [];
           bb_last_statement :=
             BStmt_Halt (BExp_Const (Imm32 0w)) |>
       ]``;

val prog3 = ``
       BirProgram [
         <|bb_label :=
             BL_Label "entry";
           bb_statements :=
             [BStmt_Assign (BVar "Mem" (BType_Mem Bit64 Bit8))
                           (BExp_Store (BExp_Den (BVar "Mem" (BType_Mem Bit64 Bit8)))
                                       (BExp_Const (Imm64 25w))
                                       BEnd_LittleEndian
                                       (BExp_Const (Imm64 25w)))];
           bb_last_statement :=
             BStmt_Jmp (BLE_Label (BL_Address (Imm32 0x102w)))|>;

         <|bb_label :=
             BL_Address (Imm32 0x102w);
           bb_statements :=
             [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                           (BExp_Cast BIExp_UnsignedCast
                                      (BExp_Load (BExp_Den (BVar "Mem" (BType_Mem Bit64 Bit8)))
                                                 (BExp_Const (Imm64 24w))
                                                 BEnd_LittleEndian
                                                 Bit32)
                                      Bit64)];
           bb_last_statement :=
             BStmt_Jmp (BLE_Label (BL_Address (Imm32 0x200w))) |>;

         <|bb_label :=
             BL_Address (Imm32 0x200w);
           bb_statements := [];
           bb_last_statement :=
             BStmt_Halt (BExp_Const (Imm32 1w)) |>
       ]``;

val prog = prog3;

val validprog_o = NONE;
val welltypedprog_o = NONE;
val state_o = NONE;

val n_max = 50;

val _ = print "ok\n";


val _ = bir_exec_prog_print name prog n_max validprog_o welltypedprog_o state_o;

