

val bprog = “BirProgram
      [<|bb_label :=
           BL_Address_HC (Imm64 (0w :word64)) "D10043FF (sub sp, sp, #0x10)";
         bb_statements :=
           [(BStmt_Assign (BVar "SP_EL0" (BType_Imm Bit64))
               (BExp_BinExp BIExp_Minus
                  (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                  (BExp_Const (Imm64 (16w :word64)))) :
             'observation_type bir_stmt_basic_t)];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 (4w :word64))))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 (4w :word64)) "F90007E0 (str x0, [sp, #8])";
         bb_statements :=
           [(BStmt_Assert
               (BExp_Aligned Bit64 (3 :num)
                  (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))) :
             'observation_type bir_stmt_basic_t);
            (BStmt_Assert
               (BExp_unchanged_mem_interval_distinct Bit64 (0 :num)
                  (16777216 :num)
                  (BExp_BinExp BIExp_Plus
                     (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                     (BExp_Const (Imm64 (8w :word64)))) (8 :num)) :
             'observation_type bir_stmt_basic_t);
            (BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
               (BExp_Store (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                  (BExp_BinExp BIExp_Plus
                     (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                     (BExp_Const (Imm64 (8w :word64)))) BEnd_LittleEndian
                  (BExp_Den (BVar "R0" (BType_Imm Bit64)))) :
             'observation_type bir_stmt_basic_t)];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 (8w :word64))))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 (8w :word64)) "F90003E1 (str x1, [sp])";
         bb_statements :=
           [(BStmt_Assert
               (BExp_Aligned Bit64 (3 :num)
                  (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))) :
             'observation_type bir_stmt_basic_t);
            (BStmt_Assert
               (BExp_unchanged_mem_interval_distinct Bit64 (0 :num)
                  (16777216 :num)
                  (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))) (8 :num)) :
             'observation_type bir_stmt_basic_t);
            (BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
               (BExp_Store (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                  (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                  BEnd_LittleEndian (BExp_Den (BVar "R1" (BType_Imm Bit64)))) :
             'observation_type bir_stmt_basic_t)];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 (12w :word64))))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 (12w :word64)) "F94007E2 (ldr x2, [sp, #8])";
         bb_statements :=
           [(BStmt_Assert
               (BExp_Aligned Bit64 (3 :num)
                  (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))) :
             'observation_type bir_stmt_basic_t);
            (BStmt_Assign (BVar "R2" (BType_Imm Bit64))
               (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                  (BExp_BinExp BIExp_Plus
                     (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                     (BExp_Const (Imm64 (8w :word64)))) BEnd_LittleEndian
                  Bit64) :'observation_type bir_stmt_basic_t)];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 (16w :word64))))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 (16w :word64)) "F94003E3 (ldr x3, [sp])";
         bb_statements :=
           [(BStmt_Assert
               (BExp_Aligned Bit64 (3 :num)
                  (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))) :
             'observation_type bir_stmt_basic_t);
            (BStmt_Assign (BVar "R3" (BType_Imm Bit64))
               (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                  (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                  BEnd_LittleEndian Bit64) :
             'observation_type bir_stmt_basic_t)];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 (20w :word64))))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 (20w :word64)) "F94007E4 (ldr x4, [sp, #8])";
         bb_statements :=
           [(BStmt_Assert
               (BExp_Aligned Bit64 (3 :num)
                  (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))) :
             'observation_type bir_stmt_basic_t);
            (BStmt_Assign (BVar "R4" (BType_Imm Bit64))
               (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                  (BExp_BinExp BIExp_Plus
                     (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                     (BExp_Const (Imm64 (8w :word64)))) BEnd_LittleEndian
                  Bit64) :'observation_type bir_stmt_basic_t)];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 (24w :word64))))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 (24w :word64)) "F94003E5 (ldr x5, [sp])";
         bb_statements :=
           [(BStmt_Assert
               (BExp_Aligned Bit64 (3 :num)
                  (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))) :
             'observation_type bir_stmt_basic_t);
            (BStmt_Assign (BVar "R5" (BType_Imm Bit64))
               (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                  (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                  BEnd_LittleEndian Bit64) :
             'observation_type bir_stmt_basic_t)];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 (28w :word64))))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 (28w :word64))
             "14000007 (b 38 <add_reg+0x38>)";
         bb_statements := ([] :'observation_type bir_stmt_basic_t list);
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 (56w :word64))))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 (32w :word64)) "AA0303E0 (mov x0, x3)";
         bb_statements :=
           [(BStmt_Assign (BVar "R0" (BType_Imm Bit64))
               (BExp_Den (BVar "R3" (BType_Imm Bit64))) :
             'observation_type bir_stmt_basic_t)];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 (36w :word64))))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 (36w :word64)) "91000400 (add x0, x0, #0x1)";
         bb_statements :=
           [(BStmt_Assign (BVar "R0" (BType_Imm Bit64))
               (BExp_BinExp BIExp_Plus
                  (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                  (BExp_Const (Imm64 (1w :word64)))) :
             'observation_type bir_stmt_basic_t)];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 (40w :word64))))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 (40w :word64)) "AA0003E3 (mov x3, x0)";
         bb_statements :=
           [(BStmt_Assign (BVar "R3" (BType_Imm Bit64))
               (BExp_Den (BVar "R0" (BType_Imm Bit64))) :
             'observation_type bir_stmt_basic_t)];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 (44w :word64))))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 (44w :word64)) "AA0203E0 (mov x0, x2)";
         bb_statements :=
           [(BStmt_Assign (BVar "R0" (BType_Imm Bit64))
               (BExp_Den (BVar "R2" (BType_Imm Bit64))) :
             'observation_type bir_stmt_basic_t)];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 (48w :word64))))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 (48w :word64)) "D1000400 (sub x0, x0, #0x1)";
         bb_statements :=
           [(BStmt_Assign (BVar "R0" (BType_Imm Bit64))
               (BExp_BinExp BIExp_Plus
                  (BExp_Const (Imm64 (0xFFFFFFFFFFFFFFFFw :word64)))
                  (BExp_Den (BVar "R0" (BType_Imm Bit64)))) :
             'observation_type bir_stmt_basic_t)];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 (52w :word64))))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 (52w :word64)) "AA0003E2 (mov x2, x0)";
         bb_statements :=
           [(BStmt_Assign (BVar "R2" (BType_Imm Bit64))
               (BExp_Den (BVar "R0" (BType_Imm Bit64))) :
             'observation_type bir_stmt_basic_t)];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 (56w :word64))))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 (56w :word64)) "AA0203E0 (mov x0, x2)";
         bb_statements :=
           [(BStmt_Assign (BVar "R0" (BType_Imm Bit64))
               (BExp_Den (BVar "R2" (BType_Imm Bit64))) :
             'observation_type bir_stmt_basic_t)];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 (60w :word64))))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 (60w :word64)) "F100001F (cmp x0, #0x0)";
         bb_statements :=
           [(BStmt_Assign (BVar "ProcState_C" BType_Bool) bir_exp_true :
             'observation_type bir_stmt_basic_t);
            (BStmt_Assign (BVar "ProcState_N" BType_Bool)
               (BExp_MSB Bit64 (BExp_Den (BVar "R0" (BType_Imm Bit64)))) :
             'observation_type bir_stmt_basic_t);
            (BStmt_Assign (BVar "ProcState_V" BType_Bool) bir_exp_false :
             'observation_type bir_stmt_basic_t);
            (BStmt_Assign (BVar "ProcState_Z" BType_Bool)
               (BExp_BinPred BIExp_Equal
                  (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                  (BExp_Const (Imm64 (0w :word64)))) :
             'observation_type bir_stmt_basic_t)];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 (64w :word64))))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 (64w :word64))
             "54FFFF0C (b.gt 20 <add_reg+0x20>)";
         bb_statements := ([] :'observation_type bir_stmt_basic_t list);
         bb_last_statement :=
           BStmt_CJmp
             (BExp_BinPred BIExp_LessOrEqual
                (BExp_BinPred BIExp_Equal
                   (BExp_Den (BVar "ProcState_N" BType_Bool))
                   (BExp_Den (BVar "ProcState_V" BType_Bool)))
                (BExp_Den (BVar "ProcState_Z" BType_Bool)))
             (BLE_Label (BL_Address (Imm64 (68w :word64))))
             (BLE_Label (BL_Address (Imm64 (32w :word64))))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 (68w :word64)) "AA0303E0 (mov x0, x3)";
         bb_statements :=
           [(BStmt_Assign (BVar "R0" (BType_Imm Bit64))
               (BExp_Den (BVar "R3" (BType_Imm Bit64))) :
             'observation_type bir_stmt_basic_t)];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 (72w :word64))))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 (72w :word64)) "910043FF (add sp, sp, #0x10)";
         bb_statements :=
           [(BStmt_Assign (BVar "SP_EL0" (BType_Imm Bit64))
               (BExp_BinExp BIExp_Plus
                  (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                  (BExp_Const (Imm64 (16w :word64)))) :
             'observation_type bir_stmt_basic_t)];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 (76w :word64))))|>
]”;

(*
       ;<|bb_label := BL_Address_HC (Imm64 (76w :word64)) "D65F03C0 (halt)";
         bb_statements := ([] :'observation_type bir_stmt_basic_t list);
         bb_last_statement :=
           BStmt_Halt (BExp_Den (BVar "R30" (BType_Imm Bit64)))|>
*)

(*;
       ;<|bb_label := BL_Address_HC (Imm64 (76w :word64)) "D65F03C0 (ret)";
         bb_statements := ([] :'observation_type bir_stmt_basic_t list);
         bb_last_statement :=
           BStmt_Jmp (BLE_Exp (BExp_Den (BVar "R30" (BType_Imm Bit64))))|>*)







val bprog = “BirProgram
      [<|bb_label :=
           BL_Address_HC (Imm64 (0w :word64)) "D10043FF (sub sp, sp, #0x10)";
         bb_statements :=
           [(BStmt_Assign (BVar "SP_EL0" (BType_Imm Bit64))
               (BExp_BinExp BIExp_Minus
                  (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                  (BExp_Const (Imm64 (16w :word64)))) :
             'observation_type bir_stmt_basic_t)];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 (4w :word64))))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 (4w :word64)) "F90007E0 (str x0, [sp, #8])";
         bb_statements :=
           [(BStmt_Assert
               (BExp_Aligned Bit64 (3 :num)
                  (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))) :
             'observation_type bir_stmt_basic_t);
            (BStmt_Assert
               (BExp_unchanged_mem_interval_distinct Bit64 (0 :num)
                  (16777216 :num)
                  (BExp_BinExp BIExp_Plus
                     (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                     (BExp_Const (Imm64 (8w :word64)))) (8 :num)) :
             'observation_type bir_stmt_basic_t);
            (BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
               (BExp_Store (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                  (BExp_BinExp BIExp_Plus
                     (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                     (BExp_Const (Imm64 (8w :word64)))) BEnd_LittleEndian
                  (BExp_Den (BVar "R0" (BType_Imm Bit64)))) :
             'observation_type bir_stmt_basic_t)];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 (8w :word64))))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 (8w :word64)) "F90003E1 (str x1, [sp])";
         bb_statements :=
           [(BStmt_Assert
               (BExp_Aligned Bit64 (3 :num)
                  (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))) :
             'observation_type bir_stmt_basic_t);
            (BStmt_Assert
               (BExp_unchanged_mem_interval_distinct Bit64 (0 :num)
                  (16777216 :num)
                  (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))) (8 :num)) :
             'observation_type bir_stmt_basic_t);
            (BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
               (BExp_Store (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                  (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                  BEnd_LittleEndian (BExp_Den (BVar "R1" (BType_Imm Bit64)))) :
             'observation_type bir_stmt_basic_t)];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 (12w :word64))))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 (12w :word64)) "F94007E2 (ldr x2, [sp, #8])";
         bb_statements :=
           [(BStmt_Assert
               (BExp_Aligned Bit64 (3 :num)
                  (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))) :
             'observation_type bir_stmt_basic_t);
            (BStmt_Assign (BVar "R2" (BType_Imm Bit64))
               (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                  (BExp_BinExp BIExp_Plus
                     (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                     (BExp_Const (Imm64 (8w :word64)))) BEnd_LittleEndian
                  Bit64) :'observation_type bir_stmt_basic_t)];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 (16w :word64))))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 (16w :word64)) "F94003E3 (ldr x3, [sp])";
         bb_statements :=
           [(BStmt_Assert
               (BExp_Aligned Bit64 (3 :num)
                  (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))) :
             'observation_type bir_stmt_basic_t);
            (BStmt_Assign (BVar "R3" (BType_Imm Bit64))
               (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                  (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                  BEnd_LittleEndian Bit64) :
             'observation_type bir_stmt_basic_t)];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 (20w :word64))))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 (20w :word64)) "F94007E4 (ldr x4, [sp, #8])";
         bb_statements :=
           [(BStmt_Assert
               (BExp_Aligned Bit64 (3 :num)
                  (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))) :
             'observation_type bir_stmt_basic_t);
            (BStmt_Assign (BVar "R4" (BType_Imm Bit64))
               (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                  (BExp_BinExp BIExp_Plus
                     (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                     (BExp_Const (Imm64 (8w :word64)))) BEnd_LittleEndian
                  Bit64) :'observation_type bir_stmt_basic_t)];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 (24w :word64))))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 (24w :word64)) "F94003E5 (ldr x5, [sp])";
         bb_statements :=
           [(BStmt_Assert
               (BExp_Aligned Bit64 (3 :num)
                  (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))) :
             'observation_type bir_stmt_basic_t);
            (BStmt_Assign (BVar "R5" (BType_Imm Bit64))
               (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                  (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                  BEnd_LittleEndian Bit64) :
             'observation_type bir_stmt_basic_t)];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 (28w :word64))))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 (28w :word64))
             "14000007 (b 38 <add_reg+0x38>)";
         bb_statements := ([] :'observation_type bir_stmt_basic_t list);
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 (56w :word64))))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 (32w :word64)) "AA0303E0 (mov x0, x3)";
         bb_statements :=
           [(BStmt_Assign (BVar "R0" (BType_Imm Bit64))
               (BExp_Den (BVar "R3" (BType_Imm Bit64))) :
             'observation_type bir_stmt_basic_t)];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 (36w :word64))))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 (36w :word64)) "91000400 (add x0, x0, #0x1)";
         bb_statements :=
           [(BStmt_Assign (BVar "R0" (BType_Imm Bit64))
               (BExp_BinExp BIExp_Plus
                  (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                  (BExp_Const (Imm64 (1w :word64)))) :
             'observation_type bir_stmt_basic_t)];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 (40w :word64))))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 (40w :word64)) "AA0003E3 (mov x3, x0)";
         bb_statements :=
           [(BStmt_Assign (BVar "R3" (BType_Imm Bit64))
               (BExp_Den (BVar "R0" (BType_Imm Bit64))) :
             'observation_type bir_stmt_basic_t)];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 (44w :word64))))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 (44w :word64)) "AA0203E0 (mov x0, x2)";
         bb_statements :=
           [(BStmt_Assign (BVar "R0" (BType_Imm Bit64))
               (BExp_Den (BVar "R2" (BType_Imm Bit64))) :
             'observation_type bir_stmt_basic_t)];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 (48w :word64))))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 (48w :word64)) "D1000400 (sub x0, x0, #0x1)";
         bb_statements :=
           [(BStmt_Assign (BVar "R0" (BType_Imm Bit64))
               (BExp_BinExp BIExp_Plus
                  (BExp_Const (Imm64 (0xFFFFFFFFFFFFFFFFw :word64)))
                  (BExp_Den (BVar "R0" (BType_Imm Bit64)))) :
             'observation_type bir_stmt_basic_t)];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 (52w :word64))))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 (52w :word64)) "AA0003E2 (mov x2, x0)";
         bb_statements :=
           [(BStmt_Assign (BVar "R2" (BType_Imm Bit64))
               (BExp_Den (BVar "R0" (BType_Imm Bit64))) :
             'observation_type bir_stmt_basic_t)];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 (56w :word64))))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 (56w :word64)) "AA0203E0 (mov x0, x2)";
         bb_statements :=
           [(BStmt_Assign (BVar "R0" (BType_Imm Bit64))
               (BExp_Den (BVar "R2" (BType_Imm Bit64))) :
             'observation_type bir_stmt_basic_t)];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 (60w :word64))))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 (60w :word64)) "F100001F (cmp x0, #0x0)";
         bb_statements :=
           [(BStmt_Assign (BVar "ProcState_C" BType_Bool) bir_exp_true :
             'observation_type bir_stmt_basic_t);
            (BStmt_Assign (BVar "ProcState_N" BType_Bool)
               (BExp_MSB Bit64 (BExp_Den (BVar "R0" (BType_Imm Bit64)))) :
             'observation_type bir_stmt_basic_t);
            (BStmt_Assign (BVar "ProcState_V" BType_Bool) bir_exp_false :
             'observation_type bir_stmt_basic_t);
            (BStmt_Assign (BVar "ProcState_Z" BType_Bool)
               (BExp_BinPred BIExp_Equal
                  (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                  (BExp_Const (Imm64 (0w :word64)))) :
             'observation_type bir_stmt_basic_t)];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 (64w :word64))))|>
]”;


val _ = bir_angrLib.do_symb_exec bprog;

(*
val bprog_json_str = birprogjsonexportLib.birprogtojsonstr bprog;
val _ = print bprog_json_str;
*)


