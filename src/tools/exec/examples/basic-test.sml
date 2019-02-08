open HolKernel Parse;

open bir_execLib;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;



val _ = print "\n";
val _ = print "executing a simple program\n"
val _ = print "================================\n"



val _ = print "loading..."

val prog = ``
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


val prog = ``
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


val n_max = 50;

val _ = print "ok\n"





val _ = print "typechecking..."
val _ = bir_exec_typecheck_prog_result prog;
val _ = print "ok\n"


val _ = print "executing..."
val (ol, n, s2) = bir_exec_prog_result prog n_max;
val _ = print "ok\n"



val _ = print "\n";
val _ = print "ol = ";
val _ = print_term ol;
val _ = print "\n";

val _ = print "\n";
val _ = print "n = ";
val _ = print_term n;
val _ = print "\n";

val _ = print "\n";
val _ = print "s2 = ";
val _ = print_term s2;
val _ = print "\n";



val _ = print "\n";
val _ = print "================================\n"
val _ = print "done\n"
val _ = print "================================\n"
val _ = print "\n";
