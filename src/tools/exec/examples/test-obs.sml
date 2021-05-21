open HolKernel Parse bossLib boolLib;
open bslSyntax;

open bir_execLib;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;



val _ = print "Loading program... ";

val prog_ldld_w_obs = ("prog_ldld_w_obs", ``
     BirProgram
      [<|bb_label := BL_Address_HC (Imm64 0w) "F9400023 (ldr x3, [x1])";
         bb_atomic := F;
         bb_statements :=
           [BStmt_Assert
              (BExp_Aligned Bit64 3 (BExp_Den (BVar "R1" (BType_Imm Bit64))));
            BStmt_Assign (BVar "R3" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_Den (BVar "R1" (BType_Imm Bit64))) BEnd_LittleEndian
                 Bit64);
            BStmt_Observe 0
                          (BExp_Const (Imm1 1w))
                          ([BExp_BinExp BIExp_And
                                        (BExp_Const (Imm64 0x1FC0w))
                                        (BExp_Den (BVar "R1" (BType_Imm Bit64)))])
                          (HD)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 4w)))|>;
       <|bb_label := BL_Address_HC (Imm64 4w) "F9400044 (ldr x4, [x2])";
         bb_atomic := F;
         bb_statements :=
           [BStmt_Assert
              (BExp_Aligned Bit64 3 (BExp_Den (BVar "R2" (BType_Imm Bit64))));
            BStmt_Assign (BVar "R4" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_Den (BVar "R2" (BType_Imm Bit64))) BEnd_LittleEndian
                 Bit64);
            BStmt_Observe 0
                          (BExp_Const (Imm1 1w))
                          ([BExp_BinExp BIExp_And
                                        (BExp_Const (Imm64 0x1FC0w))
                                        (BExp_Den (BVar "R2" (BType_Imm Bit64)))])
                          (HD)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 8w)))|>]``);

val (name, prog) = prog_ldld_w_obs;

val validprog_o = NONE;
val welltypedprog_o = NONE;
val state_o = NONE;

val n_max = 50;

val _ = print "ok\n";


val _ = bir_exec_prog_print name prog n_max validprog_o welltypedprog_o state_o;

