(* ========================= prog_17 - cache_speculation - nested speculation =========================== *)

(*
=================================
	ldr x4, [x27,x21]
	ldr x12, [x15, #45]
	cmp x27, x12
	b.eq #0x30
	ldr x2, [x4, #140]
	ldr x27, [x12, #4]
	cmp x18, x14
	b.eq #0x20
	ldr x24, [x18,x1]
	ldr x14, [x12, #71]
	ldr x7, [x1, #46]
	cmp x14, x1
	b.eq #0xC
	ldr x26, [x24, #60]
	b #0x8
	ldr x24, [x0, #4]
	nop
=================================
*)

val prog_17 = ``
BirProgram
      [<|bb_label :=
           BL_Address_HC (Imm64 0x400000w) "F8756B64 (ldr x4, [x27, x21])";
         bb_statements :=
           [BStmt_Assert
              (BExp_Aligned Bit64 3
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R27" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R21" (BType_Imm Bit64)))));
            BStmt_Assign (BVar "R4" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R27" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R21" (BType_Imm Bit64))))
                 BEnd_LittleEndian Bit64)];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400004w)))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 0x400004w) "F842D1EC (ldur x12, [x15, #45])";
         bb_statements :=
           [BStmt_Assert
              (BExp_Aligned Bit64 3
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R15" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 5w))));
            BStmt_Assign (BVar "R12" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R15" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 45w))) BEnd_LittleEndian Bit64)];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400008w)))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 0x400008w) "EB0C037F (cmp x27, x12)";
         bb_statements :=
           [BStmt_Assign (BVar "ProcState_C" BType_Bool)
              (BExp_nzcv_SUB_C (BExp_Den (BVar "R27" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R12" (BType_Imm Bit64))));
            BStmt_Assign (BVar "ProcState_N" BType_Bool)
              (BExp_nzcv_SUB_N Bit64
                 (BExp_Den (BVar "R27" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R12" (BType_Imm Bit64))));
            BStmt_Assign (BVar "ProcState_V" BType_Bool)
              (BExp_nzcv_SUB_V Bit64
                 (BExp_Den (BVar "R27" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R12" (BType_Imm Bit64))));
            BStmt_Assign (BVar "ProcState_Z" BType_Bool)
              (BExp_nzcv_SUB_Z (BExp_Den (BVar "R27" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R12" (BType_Imm Bit64))))];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40000Cw)))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 0x40000Cw)
             "54000180 (b.eq 40003c <_stack+0x38003c>  // b.none)";
         bb_statements := [];
         bb_last_statement :=
           BStmt_CJmp (BExp_Den (BVar "ProcState_Z" BType_Bool))
             (BLE_Label (BL_Address (Imm64 0x40003Cw)))
             (BLE_Label (BL_Address (Imm64 0x400010w)))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 0x400010w) "F848C082 (ldur x2, [x4, #140])";
         bb_statements :=
           [BStmt_Assert
              (BExp_Aligned Bit64 3
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R4" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 4w))));
            BStmt_Assign (BVar "R2" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R4" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 140w))) BEnd_LittleEndian Bit64)];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400014w)))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 0x400014w) "F840419B (ldur x27, [x12, #4])";
         bb_statements :=
           [BStmt_Assert
              (BExp_Aligned Bit64 3
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R12" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 4w))));
            BStmt_Assign (BVar "R27" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R12" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 4w))) BEnd_LittleEndian Bit64)];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400018w)))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 0x400018w) "EB0E025F (cmp x18, x14)";
         bb_statements :=
           [BStmt_Assign (BVar "ProcState_C" BType_Bool)
              (BExp_nzcv_SUB_C (BExp_Den (BVar "R18" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R14" (BType_Imm Bit64))));
            BStmt_Assign (BVar "ProcState_N" BType_Bool)
              (BExp_nzcv_SUB_N Bit64
                 (BExp_Den (BVar "R18" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R14" (BType_Imm Bit64))));
            BStmt_Assign (BVar "ProcState_V" BType_Bool)
              (BExp_nzcv_SUB_V Bit64
                 (BExp_Den (BVar "R18" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R14" (BType_Imm Bit64))));
            BStmt_Assign (BVar "ProcState_Z" BType_Bool)
              (BExp_nzcv_SUB_Z (BExp_Den (BVar "R18" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R14" (BType_Imm Bit64))))];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40001Cw)))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 0x40001Cw)
             "54000100 (b.eq 40003c <_stack+0x38003c>  // b.none)";
         bb_statements := [];
         bb_last_statement :=
           BStmt_CJmp (BExp_Den (BVar "ProcState_Z" BType_Bool))
             (BLE_Label (BL_Address (Imm64 0x40003Cw)))
             (BLE_Label (BL_Address (Imm64 0x400020w)))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 0x400020w) "F8616A58 (ldr x24, [x18, x1])";
         bb_statements :=
           [BStmt_Assert
              (BExp_Aligned Bit64 3
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R18" (BType_Imm Bit64)))));
            BStmt_Assign (BVar "R24" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R18" (BType_Imm Bit64))))
                 BEnd_LittleEndian Bit64)];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400024w)))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 0x400024w) "F844718E (ldur x14, [x12, #71])";
         bb_statements :=
           [BStmt_Assert
              (BExp_Aligned Bit64 3
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R12" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 7w))));
            BStmt_Assign (BVar "R14" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R12" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 71w))) BEnd_LittleEndian Bit64)];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400028w)))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 0x400028w) "F842E027 (ldur x7, [x1, #46])";
         bb_statements :=
           [BStmt_Assert
              (BExp_Aligned Bit64 3
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 6w))));
            BStmt_Assign (BVar "R7" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 46w))) BEnd_LittleEndian Bit64)];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40002Cw)))|>;
       <|bb_label := BL_Address_HC (Imm64 0x40002Cw) "EB0101DF (cmp x14, x1)";
         bb_statements :=
           [BStmt_Assign (BVar "ProcState_C" BType_Bool)
              (BExp_nzcv_SUB_C (BExp_Den (BVar "R14" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R1" (BType_Imm Bit64))));
            BStmt_Assign (BVar "ProcState_N" BType_Bool)
              (BExp_nzcv_SUB_N Bit64
                 (BExp_Den (BVar "R14" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R1" (BType_Imm Bit64))));
            BStmt_Assign (BVar "ProcState_V" BType_Bool)
              (BExp_nzcv_SUB_V Bit64
                 (BExp_Den (BVar "R14" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R1" (BType_Imm Bit64))));
            BStmt_Assign (BVar "ProcState_Z" BType_Bool)
              (BExp_nzcv_SUB_Z (BExp_Den (BVar "R14" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R1" (BType_Imm Bit64))))];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400030w)))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 0x400030w)
             "54000060 (b.eq 40003c <_stack+0x38003c>  // b.none)";
         bb_statements := [];
         bb_last_statement :=
           BStmt_CJmp (BExp_Den (BVar "ProcState_Z" BType_Bool))
             (BLE_Label (BL_Address (Imm64 0x40003Cw)))
             (BLE_Label (BL_Address (Imm64 0x400034w)))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 0x400034w) "F843C31A (ldur x26, [x24, #60])";
         bb_statements :=
           [BStmt_Assert
              (BExp_Aligned Bit64 3
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 4w))));
            BStmt_Assign (BVar "R26" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 60w))) BEnd_LittleEndian Bit64)];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400038w)))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 0x400038w)
             "14000002 (b 400040 <_stack+0x380040>)"; bb_statements := [];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400040w)))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 0x40003Cw) "F8404018 (ldur x24, [x0, #4])";
         bb_statements :=
           [BStmt_Assert
              (BExp_Aligned Bit64 3
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 4w))));
            BStmt_Assign (BVar "R24" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 4w))) BEnd_LittleEndian Bit64)];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400040w)))|>;
       <|bb_label := BL_Address_HC (Imm64 0x400040w) "D503201F (nop)";
         bb_statements := [];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400044w)))|>;
       <|bb_label := BL_Address (Imm64 0x400044w); bb_statements := [];
         bb_last_statement := BStmt_Halt (BExp_Const (Imm32 0x400000w))|>]
:bir_val_t bir_program_t
``;

val prog_17_mem_address_pc = ``
F
``;

val prog_17_cache_tag_index = ``
F
``;

val prog_17_cache_tag_only = ``
F
``;

val prog_17_cache_index_only = ``
F
``;

val prog_17_cache_tag_index_part = ``
F
``;

val prog_17_cache_tag_index_part_page = ``
F
``;

val prog_17_cache_speculation = ``
BirProgram
      [<|bb_label := BL_Address (Imm64 0x400000w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_Const (Imm64 0x400000w)] HD;
            BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R27" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R21" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 0xFFCC0000w))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R27" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R21" (BType_Imm Bit64)))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R27" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R21" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 0xFFCCAFF0w))));
            BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "R27" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R21" (BType_Imm Bit64)))] HD;
            BStmt_Assign (BVar "R4" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R27" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R21" (BType_Imm Bit64))))
                 BEnd_LittleEndian Bit64)];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400004w)))|>;
       <|bb_label := BL_Address (Imm64 0x400004w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_Const (Imm64 0x400004w)] HD;
            BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R15" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 5w))) (BExp_Const (Imm64 7w)))
                 (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 0xFFCC0000w))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R15" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 45w))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R15" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 45w)))
                    (BExp_Const (Imm64 0xFFCCAFF0w))));
            BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "R15" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 45w))] HD;
            BStmt_Assign (BVar "R12" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R15" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 45w))) BEnd_LittleEndian Bit64)];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400008w)))|>;
       <|bb_label := BL_Address (Imm64 0x400008w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_Const (Imm64 0x400008w)] HD;
            BStmt_Assign (BVar "ProcState_C" (BType_Imm Bit1))
              (BExp_BinPred BIExp_LessOrEqual
                 (BExp_Den (BVar "R12" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R27" (BType_Imm Bit64))));
            BStmt_Assign (BVar "ProcState_N" (BType_Imm Bit1))
              (BExp_BinPred BIExp_SignedLessThan
                 (BExp_BinExp BIExp_Minus
                    (BExp_Den (BVar "R27" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R12" (BType_Imm Bit64))))
                 (BExp_Const (Imm64 0w)));
            BStmt_Assign (BVar "ProcState_V" (BType_Imm Bit1))
              (BExp_BinPred BIExp_Equal
                 (BExp_BinPred BIExp_SignedLessThan
                    (BExp_BinExp BIExp_Minus
                       (BExp_Den (BVar "R27" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R12" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 0w)))
                 (BExp_BinPred BIExp_SignedLessOrEqual
                    (BExp_Den (BVar "R12" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R27" (BType_Imm Bit64)))));
            BStmt_Assign (BVar "ProcState_Z" (BType_Imm Bit1))
              (BExp_BinPred BIExp_Equal
                 (BExp_Den (BVar "R27" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R12" (BType_Imm Bit64))))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "0x40000C*"))|>;
       <|bb_label := BL_Address (Imm64 0x40000Cw);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_Const (Imm64 0x40000Cw)] HD];
         bb_last_statement :=
           BStmt_CJmp (BExp_Den (BVar "ProcState_Z" (BType_Imm Bit1)))
             (BLE_Label (BL_Address (Imm64 0x40003Cw)))
             (BLE_Label (BL_Address (Imm64 0x400010w)))|>;
       <|bb_label := BL_Address (Imm64 0x400010w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_Const (Imm64 0x400010w)] HD;
            BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R4" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 4w))) (BExp_Const (Imm64 7w)))
                 (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 0xFFCC0000w))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R4" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 140w))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R4" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 140w)))
                    (BExp_Const (Imm64 0xFFCCAFF0w))));
            BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "R4" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 140w))] HD;
            BStmt_Assign (BVar "R2" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R4" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 140w))) BEnd_LittleEndian Bit64)];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400014w)))|>;
       <|bb_label := BL_Address (Imm64 0x400014w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_Const (Imm64 0x400014w)] HD;
            BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R12" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 4w))) (BExp_Const (Imm64 7w)))
                 (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 0xFFCC0000w))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R12" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 4w))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R12" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 4w)))
                    (BExp_Const (Imm64 0xFFCCAFF0w))));
            BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "R12" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 4w))] HD;
            BStmt_Assign (BVar "R27" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R12" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 4w))) BEnd_LittleEndian Bit64)];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400018w)))|>;
       <|bb_label := BL_Address (Imm64 0x400018w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_Const (Imm64 0x400018w)] HD;
            BStmt_Assign (BVar "ProcState_C" (BType_Imm Bit1))
              (BExp_BinPred BIExp_LessOrEqual
                 (BExp_Den (BVar "R14" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R18" (BType_Imm Bit64))));
            BStmt_Assign (BVar "ProcState_N" (BType_Imm Bit1))
              (BExp_BinPred BIExp_SignedLessThan
                 (BExp_BinExp BIExp_Minus
                    (BExp_Den (BVar "R18" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R14" (BType_Imm Bit64))))
                 (BExp_Const (Imm64 0w)));
            BStmt_Assign (BVar "ProcState_V" (BType_Imm Bit1))
              (BExp_BinPred BIExp_Equal
                 (BExp_BinPred BIExp_SignedLessThan
                    (BExp_BinExp BIExp_Minus
                       (BExp_Den (BVar "R18" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R14" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 0w)))
                 (BExp_BinPred BIExp_SignedLessOrEqual
                    (BExp_Den (BVar "R14" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R18" (BType_Imm Bit64)))));
            BStmt_Assign (BVar "ProcState_Z" (BType_Imm Bit1))
              (BExp_BinPred BIExp_Equal
                 (BExp_Den (BVar "R18" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R14" (BType_Imm Bit64))))];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40001Cw)))|>;
       <|bb_label := BL_Address (Imm64 0x40001Cw);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_Const (Imm64 0x40001Cw)] HD];
         bb_last_statement :=
           BStmt_CJmp (BExp_Den (BVar "ProcState_Z" (BType_Imm Bit1)))
             (BLE_Label (BL_Address (Imm64 0x40003Cw)))
             (BLE_Label (BL_Address (Imm64 0x400020w)))|>;
       <|bb_label := BL_Address (Imm64 0x400020w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_Const (Imm64 0x400020w)] HD;
            BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R18" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 0xFFCC0000w))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R18" (BType_Imm Bit64)))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R18" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 0xFFCCAFF0w))));
            BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R18" (BType_Imm Bit64)))] HD;
            BStmt_Assign (BVar "R24" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R18" (BType_Imm Bit64))))
                 BEnd_LittleEndian Bit64)];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400024w)))|>;
       <|bb_label := BL_Address (Imm64 0x400024w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_Const (Imm64 0x400024w)] HD;
            BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R12" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 7w)))
                 (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 0xFFCC0000w))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R12" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 71w))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R12" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 71w)))
                    (BExp_Const (Imm64 0xFFCCAFF0w))));
            BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "R12" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 71w))] HD;
            BStmt_Assign (BVar "R14" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R12" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 71w))) BEnd_LittleEndian Bit64)];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400028w)))|>;
       <|bb_label := BL_Address (Imm64 0x400028w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_Const (Imm64 0x400028w)] HD;
            BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 6w))) (BExp_Const (Imm64 7w)))
                 (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 0xFFCC0000w))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 46w))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 46w)))
                    (BExp_Const (Imm64 0xFFCCAFF0w))));
            BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 46w))] HD;
            BStmt_Assign (BVar "R7" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 46w))) BEnd_LittleEndian Bit64)];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40002Cw)))|>;
       <|bb_label := BL_Address (Imm64 0x40002Cw);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_Const (Imm64 0x40002Cw)] HD;
            BStmt_Assign (BVar "ProcState_C" (BType_Imm Bit1))
              (BExp_BinPred BIExp_LessOrEqual
                 (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R14" (BType_Imm Bit64))));
            BStmt_Assign (BVar "ProcState_N" (BType_Imm Bit1))
              (BExp_BinPred BIExp_SignedLessThan
                 (BExp_BinExp BIExp_Minus
                    (BExp_Den (BVar "R14" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R1" (BType_Imm Bit64))))
                 (BExp_Const (Imm64 0w)));
            BStmt_Assign (BVar "ProcState_V" (BType_Imm Bit1))
              (BExp_BinPred BIExp_Equal
                 (BExp_BinPred BIExp_SignedLessThan
                    (BExp_BinExp BIExp_Minus
                       (BExp_Den (BVar "R14" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R1" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 0w)))
                 (BExp_BinPred BIExp_SignedLessOrEqual
                    (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R14" (BType_Imm Bit64)))));
            BStmt_Assign (BVar "ProcState_Z" (BType_Imm Bit1))
              (BExp_BinPred BIExp_Equal
                 (BExp_Den (BVar "R14" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R1" (BType_Imm Bit64))))];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400030w)))|>;
       <|bb_label := BL_Address (Imm64 0x400030w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_Const (Imm64 0x400030w)] HD];
         bb_last_statement :=
           BStmt_CJmp (BExp_Den (BVar "ProcState_Z" (BType_Imm Bit1)))
             (BLE_Label (BL_Address (Imm64 0x40003Cw)))
             (BLE_Label (BL_Address (Imm64 0x400034w)))|>;
       <|bb_label := BL_Address (Imm64 0x400034w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_Const (Imm64 0x400034w)] HD;
            BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 4w))) (BExp_Const (Imm64 7w)))
                 (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 0xFFCC0000w))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 60w))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 60w)))
                    (BExp_Const (Imm64 0xFFCCAFF0w))));
            BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 60w))] HD;
            BStmt_Assign (BVar "R26" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 60w))) BEnd_LittleEndian Bit64)];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400038w)))|>;
       <|bb_label := BL_Address (Imm64 0x400038w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_Const (Imm64 0x400038w)] HD];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400040w)))|>;
       <|bb_label := BL_Address (Imm64 0x40003Cw);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_Const (Imm64 0x40003Cw)] HD;
            BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 4w))) (BExp_Const (Imm64 7w)))
                 (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 0xFFCC0000w))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 4w))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 4w)))
                    (BExp_Const (Imm64 0xFFCCAFF0w))));
            BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 4w))] HD;
            BStmt_Assign (BVar "R24" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 4w))) BEnd_LittleEndian Bit64)];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400040w)))|>;
       <|bb_label := BL_Address (Imm64 0x400040w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_Const (Imm64 0x400040w)] HD];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400044w)))|>;
       <|bb_label := BL_Address (Imm64 0x400044w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_Const (Imm64 0x400044w)] HD];
         bb_last_statement := BStmt_Halt (BExp_Const (Imm32 0x400000w))|>;
       <|bb_label := BL_Label "0x40000C*";
         bb_statements :=
           [BStmt_Assert
              (BExp_BinPred BIExp_Equal (BExp_Const (Imm64 41w))
                 (BExp_Const (Imm64 41w)));
            BStmt_Assign (BVar "ProcState_Z*" (BType_Imm Bit1))
              (BExp_Den (BVar "ProcState_Z" (BType_Imm Bit1)));
            BStmt_Assign (BVar "R4*" (BType_Imm Bit64))
              (BExp_Den (BVar "R4" (BType_Imm Bit64)));
            BStmt_Assign (BVar "MEM*" (BType_Mem Bit64 Bit8))
              (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)));
            BStmt_Assign (BVar "R12*" (BType_Imm Bit64))
              (BExp_Den (BVar "R12" (BType_Imm Bit64)));
            BStmt_Assign (BVar "R14*" (BType_Imm Bit64))
              (BExp_Den (BVar "R14" (BType_Imm Bit64)));
            BStmt_Assign (BVar "R18*" (BType_Imm Bit64))
              (BExp_Den (BVar "R18" (BType_Imm Bit64)));
            BStmt_Assign (BVar "R1*" (BType_Imm Bit64))
              (BExp_Den (BVar "R1" (BType_Imm Bit64)));
            BStmt_Assign (BVar "R24*" (BType_Imm Bit64))
              (BExp_Den (BVar "R24" (BType_Imm Bit64)));
            BStmt_Assign (BVar "R0*" (BType_Imm Bit64))
              (BExp_Den (BVar "R0" (BType_Imm Bit64)))];
         bb_last_statement :=
           BStmt_CJmp
             (BExp_UnaryExp BIExp_Not
                (BExp_Den (BVar "ProcState_Z*" (BType_Imm Bit1))))
             (BLE_Label (BL_Label "0x40003C*"))
             (BLE_Label (BL_Label "0x400010*"))|>;
       <|bb_label := BL_Label "0x400010*";
         bb_statements :=
           [BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R4*" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 4w))) (BExp_Const (Imm64 7w)))
                 (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 0xFFCC0000w))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R4*" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 140w))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R4*" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 140w)))
                    (BExp_Const (Imm64 0xFFCCAFF0w))));
            BStmt_Observe 1 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "R4*" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 140w))] HD;
            BStmt_Assign (BVar "R2*" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM*" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R4*" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 140w))) BEnd_LittleEndian Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "0x400014*"))|>;
       <|bb_label := BL_Label "0x400014*";
         bb_statements :=
           [BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R12*" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 4w))) (BExp_Const (Imm64 7w)))
                 (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 0xFFCC0000w))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R12*" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 4w))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R12*" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 4w)))
                    (BExp_Const (Imm64 0xFFCCAFF0w))));
            BStmt_Observe 1 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "R12*" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 4w))] HD;
            BStmt_Assign (BVar "R27*" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM*" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R12*" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 4w))) BEnd_LittleEndian Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "0x400018*"))|>;
       <|bb_label := BL_Label "0x400018*";
         bb_statements :=
           [BStmt_Assign (BVar "ProcState_C*" (BType_Imm Bit1))
              (BExp_BinPred BIExp_LessOrEqual
                 (BExp_Den (BVar "R14*" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R18*" (BType_Imm Bit64))));
            BStmt_Assign (BVar "ProcState_N*" (BType_Imm Bit1))
              (BExp_BinPred BIExp_SignedLessThan
                 (BExp_BinExp BIExp_Minus
                    (BExp_Den (BVar "R18*" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R14*" (BType_Imm Bit64))))
                 (BExp_Const (Imm64 0w)));
            BStmt_Assign (BVar "ProcState_V*" (BType_Imm Bit1))
              (BExp_BinPred BIExp_Equal
                 (BExp_BinPred BIExp_SignedLessThan
                    (BExp_BinExp BIExp_Minus
                       (BExp_Den (BVar "R18*" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R14*" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 0w)))
                 (BExp_BinPred BIExp_SignedLessOrEqual
                    (BExp_Den (BVar "R14*" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R18*" (BType_Imm Bit64)))));
            BStmt_Assign (BVar "ProcState_Z*" (BType_Imm Bit1))
              (BExp_BinPred BIExp_Equal
                 (BExp_Den (BVar "R18*" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R14*" (BType_Imm Bit64))))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "0x40001C*"))|>;
       <|bb_label := BL_Label "0x40001C*"; bb_statements := [];
         bb_last_statement :=
           BStmt_CJmp
             (BExp_UnaryExp BIExp_Not
                (BExp_Den (BVar "ProcState_Z*" (BType_Imm Bit1))))
             (BLE_Label (BL_Label "0x40003C*"))
             (BLE_Label (BL_Label "0x400020*"))|>;
       <|bb_label := BL_Label "0x400020*";
         bb_statements :=
           [BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R1*" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R18*" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 0xFFCC0000w))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R1*" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R18*" (BType_Imm Bit64)))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R1*" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R18*" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 0xFFCCAFF0w))));
            BStmt_Observe 1 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "R1*" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R18*" (BType_Imm Bit64)))] HD;
            BStmt_Assign (BVar "R24*" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM*" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R1*" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R18*" (BType_Imm Bit64))))
                 BEnd_LittleEndian Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "0x400024*"))|>;
       <|bb_label := BL_Label "0x400024*";
         bb_statements :=
           [BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R12*" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 7w)))
                 (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 0xFFCC0000w))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R12*" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 71w))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R12*" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 71w)))
                    (BExp_Const (Imm64 0xFFCCAFF0w))));
            BStmt_Observe 1 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "R12*" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 71w))] HD;
            BStmt_Assign (BVar "R14*" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM*" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R12*" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 71w))) BEnd_LittleEndian Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "0x400028*"))|>;
       <|bb_label := BL_Label "0x400028*";
         bb_statements :=
           [BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R1*" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 6w))) (BExp_Const (Imm64 7w)))
                 (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 0xFFCC0000w))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R1*" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 46w))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R1*" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 46w)))
                    (BExp_Const (Imm64 0xFFCCAFF0w))));
            BStmt_Observe 1 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "R1*" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 46w))] HD;
            BStmt_Assign (BVar "R7*" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM*" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R1*" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 46w))) BEnd_LittleEndian Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "0x40002C*"))|>;
       <|bb_label := BL_Label "0x40002C*";
         bb_statements :=
           [BStmt_Assign (BVar "ProcState_C*" (BType_Imm Bit1))
              (BExp_BinPred BIExp_LessOrEqual
                 (BExp_Den (BVar "R1*" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R14*" (BType_Imm Bit64))));
            BStmt_Assign (BVar "ProcState_N*" (BType_Imm Bit1))
              (BExp_BinPred BIExp_SignedLessThan
                 (BExp_BinExp BIExp_Minus
                    (BExp_Den (BVar "R14*" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R1*" (BType_Imm Bit64))))
                 (BExp_Const (Imm64 0w)));
            BStmt_Assign (BVar "ProcState_V*" (BType_Imm Bit1))
              (BExp_BinPred BIExp_Equal
                 (BExp_BinPred BIExp_SignedLessThan
                    (BExp_BinExp BIExp_Minus
                       (BExp_Den (BVar "R14*" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R1*" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 0w)))
                 (BExp_BinPred BIExp_SignedLessOrEqual
                    (BExp_Den (BVar "R1*" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R14*" (BType_Imm Bit64)))));
            BStmt_Assign (BVar "ProcState_Z*" (BType_Imm Bit1))
              (BExp_BinPred BIExp_Equal
                 (BExp_Den (BVar "R14*" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R1*" (BType_Imm Bit64))))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "0x400030*"))|>;
       <|bb_label := BL_Label "0x400030*"; bb_statements := [];
         bb_last_statement :=
           BStmt_CJmp
             (BExp_UnaryExp BIExp_Not
                (BExp_Den (BVar "ProcState_Z*" (BType_Imm Bit1))))
             (BLE_Label (BL_Label "0x40003C*"))
             (BLE_Label (BL_Label "0x400034*"))|>;
       <|bb_label := BL_Label "0x400034*";
         bb_statements :=
           [BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R24*" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 4w))) (BExp_Const (Imm64 7w)))
                 (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 0xFFCC0000w))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R24*" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 60w))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R24*" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 60w)))
                    (BExp_Const (Imm64 0xFFCCAFF0w))));
            BStmt_Observe 1 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "R24*" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 60w))] HD;
            BStmt_Assign (BVar "R26*" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM*" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R24*" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 60w))) BEnd_LittleEndian Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "0x400038*"))|>;
       <|bb_label := BL_Label "0x400038*"; bb_statements := [];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "0x400040*"))|>;
       <|bb_label := BL_Label "0x400040*"; bb_statements := [];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "0x400044*"))|>;
       <|bb_label := BL_Label "0x400044*";
         bb_statements :=
           [BStmt_Assert
              (BExp_BinPred BIExp_Equal (BExp_Const (Imm64 42w))
                 (BExp_Const (Imm64 42w)))];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40000Cw)))|>;
       <|bb_label := BL_Label "0x40003C*";
         bb_statements :=
           [BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R0*" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 4w))) (BExp_Const (Imm64 7w)))
                 (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 0xFFCC0000w))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R0*" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 4w))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R0*" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 4w)))
                    (BExp_Const (Imm64 0xFFCCAFF0w))));
            BStmt_Observe 1 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "R0*" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 4w))] HD;
            BStmt_Assign (BVar "R24*" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM*" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R0*" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 4w))) BEnd_LittleEndian Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "0x400040*"))|>]
:bir_val_t bir_program_t
``;

val prog_17_cache_speculation_first = ``
F
``;

val prog_17_test =
  ("prog_17 - cache_speculation - nested speculation", prog_17,
     (prog_17_mem_address_pc,
      ``F``,
      prog_17_cache_tag_index,
      prog_17_cache_tag_only,
      prog_17_cache_index_only,
      prog_17_cache_tag_index_part,
      prog_17_cache_tag_index_part_page,
      prog_17_cache_speculation,
      prog_17_cache_speculation_first)
  );
