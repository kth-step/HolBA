(*
load "bir_symb_execLib";
load "toyBinaryTheory";
*)

open bir_symb_masterLib;

val maxdepth = (~1);
val precond = ``bir_exp_true``;
(*val prog = (snd o dest_comb o concl) toy_arm8_THM; *)

val prog = ``BirProgram
  [<|bb_label :=
       BL_Address_HC (Imm64 0w) "3649DFA1 (tbz w1, #9, 3bf4 <.text+0x3bf4>)";
     bb_statements := [];
     bb_last_statement :=
       BStmt_CJmp
         (BExp_word_bit Bit32
            (BExp_Cast BIExp_LowCast (BExp_Den (BVar "R1" (BType_Imm Bit64)))
               Bit32) 9) (BLE_Label (BL_Address (Imm64 4w)))
         (BLE_Label (BL_Address (Imm64 15348w)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 4w) "B5010034 (cbnz x20, 2008 <.text+0x2008>)";
     bb_statements := [];
     bb_last_statement :=
       BStmt_CJmp
         (BExp_BinPred BIExp_Equal (BExp_Den (BVar "R20" (BType_Imm Bit64)))
            (BExp_Const (Imm64 0w))) (BLE_Label (BL_Address (Imm64 8200w)))
         (BLE_Label (BL_Address (Imm64 8w)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 8w) "F86158F4 (ldr x20, [x7, w1, uxtw #3])";
     bb_statements :=
       [BStmt_Assert
          (BExp_Aligned Bit64 3
             (BExp_BinExp BIExp_Plus (BExp_Den (BVar "R7" (BType_Imm Bit64)))
                (BExp_BinExp BIExp_LeftShift
                   (BExp_Cast BIExp_UnsignedCast
                      (BExp_Cast BIExp_LowCast
                         (BExp_Den (BVar "R1" (BType_Imm Bit64))) Bit32)
                      Bit64) (BExp_Const (Imm64 3w)))));
        BStmt_Assign (BVar "R20" (BType_Imm Bit64))
          (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
             (BExp_BinExp BIExp_Plus (BExp_Den (BVar "R7" (BType_Imm Bit64)))
                (BExp_BinExp BIExp_LeftShift
                   (BExp_Cast BIExp_UnsignedCast
                      (BExp_Cast BIExp_LowCast
                         (BExp_Den (BVar "R1" (BType_Imm Bit64))) Bit32)
                      Bit64) (BExp_Const (Imm64 3w)))) BEnd_LittleEndian
             Bit64)];
     bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 12w)))|>;
   <|bb_label := BL_Address_HC (Imm64 12w) "38346832 (strb w18, [x1, x20])";
     bb_statements :=
       [BStmt_Assert
          (BExp_unchanged_mem_interval_distinct Bit64 0 32
             (BExp_BinExp BIExp_Plus (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                (BExp_Den (BVar "R20" (BType_Imm Bit64)))) 1);
        BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
          (BExp_Store (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
             (BExp_BinExp BIExp_Plus (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                (BExp_Den (BVar "R20" (BType_Imm Bit64)))) BEnd_LittleEndian
             (BExp_Cast BIExp_LowCast
                (BExp_Den (BVar "R18" (BType_Imm Bit64))) Bit8))];
     bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 16w)))|>;
   <|bb_label := BL_Address_HC (Imm64 16w) "5AC0003F (rbit wzr, w1)";
     bb_statements := [];
     bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 20w)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 20w) "6B1E743C (subs w28, w1, w30, lsl #29)";
     bb_statements :=
       [BStmt_Assign (BVar "ProcState_C" BType_Bool)
          (BExp_nzcv_SUB_C
             (BExp_Cast BIExp_LowCast
                (BExp_Den (BVar "R1" (BType_Imm Bit64))) Bit32)
             (BExp_BinExp BIExp_LeftShift
                (BExp_Cast BIExp_LowCast
                   (BExp_Den (BVar "R30" (BType_Imm Bit64))) Bit32)
                (BExp_Const (Imm32 29w))));
        BStmt_Assign (BVar "ProcState_N" BType_Bool)
          (BExp_nzcv_SUB_N Bit32
             (BExp_Cast BIExp_LowCast
                (BExp_Den (BVar "R1" (BType_Imm Bit64))) Bit32)
             (BExp_BinExp BIExp_LeftShift
                (BExp_Cast BIExp_LowCast
                   (BExp_Den (BVar "R30" (BType_Imm Bit64))) Bit32)
                (BExp_Const (Imm32 29w))));
        BStmt_Assign (BVar "ProcState_V" BType_Bool)
          (BExp_nzcv_SUB_V Bit32
             (BExp_Cast BIExp_LowCast
                (BExp_Den (BVar "R1" (BType_Imm Bit64))) Bit32)
             (BExp_BinExp BIExp_LeftShift
                (BExp_Cast BIExp_LowCast
                   (BExp_Den (BVar "R30" (BType_Imm Bit64))) Bit32)
                (BExp_Const (Imm32 29w))));
        BStmt_Assign (BVar "ProcState_Z" BType_Bool)
          (BExp_nzcv_SUB_Z
             (BExp_Cast BIExp_LowCast
                (BExp_Den (BVar "R1" (BType_Imm Bit64))) Bit32)
             (BExp_BinExp BIExp_LeftShift
                (BExp_Cast BIExp_LowCast
                   (BExp_Den (BVar "R30" (BType_Imm Bit64))) Bit32)
                (BExp_Const (Imm32 29w))));
        BStmt_Assign (BVar "R28" (BType_Imm Bit64))
          (BExp_Cast BIExp_UnsignedCast
             (BExp_BinExp BIExp_Minus
                (BExp_Cast BIExp_LowCast
                   (BExp_Den (BVar "R1" (BType_Imm Bit64))) Bit32)
                (BExp_BinExp BIExp_LeftShift
                   (BExp_Cast BIExp_LowCast
                      (BExp_Den (BVar "R30" (BType_Imm Bit64))) Bit32)
                   (BExp_Const (Imm32 29w)))) Bit64)];
     bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 24w)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 24w)
         "BA542325 (ccmn x25, x20, #0x5, cs  // cs = hs, nlast)";
     bb_statements :=
       [BStmt_Assign (BVar "tmp_ProcState_C" BType_Bool)
          (BExp_BinExp BIExp_And (BExp_Den (BVar "ProcState_C" BType_Bool))
             (BExp_nzcv_ADD_C (BExp_Den (BVar "R25" (BType_Imm Bit64)))
                (BExp_Den (BVar "R20" (BType_Imm Bit64)))));
        BStmt_Assign (BVar "ProcState_N" BType_Bool)
          (BExp_BinExp BIExp_And (BExp_Den (BVar "ProcState_C" BType_Bool))
             (BExp_nzcv_ADD_N Bit64 (BExp_Den (BVar "R25" (BType_Imm Bit64)))
                (BExp_Den (BVar "R20" (BType_Imm Bit64)))));
        BStmt_Assign (BVar "ProcState_V" BType_Bool)
          (BExp_BinPred BIExp_LessOrEqual
             (BExp_Den (BVar "ProcState_C" BType_Bool))
             (BExp_nzcv_ADD_V Bit64 (BExp_Den (BVar "R25" (BType_Imm Bit64)))
                (BExp_Den (BVar "R20" (BType_Imm Bit64)))));
        BStmt_Assign (BVar "ProcState_Z" BType_Bool)
          (BExp_BinPred BIExp_LessOrEqual
             (BExp_Den (BVar "ProcState_C" BType_Bool))
             (BExp_nzcv_ADD_Z (BExp_Den (BVar "R25" (BType_Imm Bit64)))
                (BExp_Den (BVar "R20" (BType_Imm Bit64)))));
        BStmt_Assign (BVar "ProcState_C" BType_Bool)
          (BExp_Den (BVar "tmp_ProcState_C" BType_Bool))];
     bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 28w)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 28w) "CA140DA8 (eor x8, x13, x20, lsl #3)";
     bb_statements :=
       [BStmt_Assign (BVar "R8" (BType_Imm Bit64))
          (BExp_BinExp BIExp_Xor (BExp_Den (BVar "R13" (BType_Imm Bit64)))
             (BExp_BinExp BIExp_LeftShift
                (BExp_Den (BVar "R20" (BType_Imm Bit64)))
                (BExp_Const (Imm64 3w))))];
     bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 32w)))|>]``

val prog2 = ``BirProgram
  [<|bb_label :=
       BL_Address_HC (Imm64 0w) "3649DFA1 (tbz w1, #9, 3bf4 <.text+0x3bf4>)";
     bb_statements := [];
     bb_last_statement :=
       BStmt_CJmp
         (BExp_word_bit Bit32
            (BExp_Cast BIExp_LowCast (BExp_Den (BVar "R1" (BType_Imm Bit64)))
               Bit32) 9) (BLE_Label (BL_Address (Imm64 4w)))
         (BLE_Label (BL_Address (Imm64 15348w)))|>;
   <|bb_label :=
       BL_Address_HC (Imm64 4w) "B5010034 (cbnz x20, 2008 <.text+0x2008>)";
     bb_statements := [];
     bb_last_statement :=
       BStmt_CJmp
         (BExp_BinPred BIExp_Equal (BExp_Den (BVar "R20" (BType_Imm Bit64)))
            (BExp_Const (Imm64 0w))) (BLE_Label (BL_Address (Imm64 8200w)))
         (BLE_Label (BL_Address (Imm64 8w)))|>]``;


val prog3 = ``BirProgram
  [<|bb_label :=
   BL_Address_HC (Imm64 0w) "3649DFA1 (tbz w1, #9, 3bf4 <.text+0x3bf4>)";
   bb_statements := [];
   bb_last_statement :=
   BStmt_CJmp
       (BExp_word_bit Bit32
                      (BExp_Cast BIExp_LowCast (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                                 Bit32) 9) (BLE_Label (BL_Address (Imm64 4w)))
       (BLE_Label (BL_Address (Imm64 15348w)))|>]``;

val prog4 = ``BirProgram
  [<|bb_label :=
   BL_Address_HC (Imm64 4w) "B5010034 (cbnz x20, 2008 <.text+0x2008>)";
   bb_statements := [];
   bb_last_statement :=
   BStmt_CJmp
       (BExp_BinPred BIExp_Equal (BExp_Den (BVar "R20" (BType_Imm Bit64)))
                     (BExp_Const (Imm64 0w))) (BLE_Label (BL_Address (Imm64 8200w)))
       (BLE_Label (BL_Address (Imm64 8w)))|>]``;


fun leafs_of p = symb_exec_process_to_leafs_nosmt maxdepth precond p;

(*
============================
*)

val leafs_prog4 = leafs_of prog4;

val prog5 = ``BirProgram
  [<|bb_label :=
   BL_Address_HC (Imm64 4w) "B5010034 (cbnz x20, 2008 <.text+0x2008>)";
   bb_statements := [];
   bb_last_statement :=
   BStmt_CJmp
       (BExp_BinPred BIExp_Equal (BExp_Den (BVar "R20*" (BType_Imm Bit64)))
                     (BExp_Const (Imm64 0w))) (BLE_Label (BL_Address (Imm64 8200w)))
       (BLE_Label (BL_Address (Imm64 8w)))|>]``;


val leafs_prog4 = leafs_of prog5;

