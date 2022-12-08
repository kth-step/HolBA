(* ========================= prog_14 - cache_speculation =========================== *)

(*
=================================
	mov x4, #8
	str x4, [x3, x1]
	lsl x4, x4, #0x3
	add x5, x4, x2
	ldr x7, [x5, x6]
	cmp x1, x7
	b.mi #0x8
	ldr x10, [x7]
	ret
=================================
*)

val prog_14 = ``
BirProgram
      [<|bb_label :=
           BL_Address_HC (Imm64 0x400000w)
             "D2800104 (mov x4, #0x8                    // #8)";
         bb_statements :=
           [BStmt_Assign (BVar "R4" (BType_Imm Bit64))
              (BExp_Const (Imm64 8w))];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400004w)))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 0x400004w) "F8216864 (str x4, [x3, x1])";
         bb_statements :=
           [BStmt_Assert
              (BExp_Aligned Bit64 3
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R3" (BType_Imm Bit64)))));
            BStmt_Assert
              (BExp_unchanged_mem_interval_distinct Bit64 4194304 4194340
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R3" (BType_Imm Bit64)))) 8);
            BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
              (BExp_Store (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R3" (BType_Imm Bit64))))
                 BEnd_LittleEndian (BExp_Den (BVar "R4" (BType_Imm Bit64))))];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400008w)))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 0x400008w) "D37DF084 (lsl x4, x4, #3)";
         bb_statements :=
           [BStmt_Assign (BVar "R4" (BType_Imm Bit64))
              (BExp_BinExp BIExp_And (BExp_Const (Imm64 0xFFFFFFFFFFFFFFFFw))
                 (BExp_BinExp BIExp_LeftShift
                    (BExp_Den (BVar "R4" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 3w))))];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40000Cw)))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 0x40000Cw) "8B020085 (add x5, x4, x2)";
         bb_statements :=
           [BStmt_Assign (BVar "R5" (BType_Imm Bit64))
              (BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "R2" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R4" (BType_Imm Bit64))))];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400010w)))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 0x400010w) "F86668A7 (ldr x7, [x5, x6])";
         bb_statements :=
           [BStmt_Assert
              (BExp_Aligned Bit64 3
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R5" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R6" (BType_Imm Bit64)))));
            BStmt_Assign (BVar "R7" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R5" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R6" (BType_Imm Bit64))))
                 BEnd_LittleEndian Bit64)];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400014w)))|>;
       <|bb_label := BL_Address_HC (Imm64 0x400014w) "EB07003F (cmp x1, x7)";
         bb_statements :=
           [BStmt_Assign (BVar "ProcState_C" BType_Bool)
              (BExp_nzcv_SUB_C (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R7" (BType_Imm Bit64))));
            BStmt_Assign (BVar "ProcState_N" BType_Bool)
              (BExp_nzcv_SUB_N Bit64 (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R7" (BType_Imm Bit64))));
            BStmt_Assign (BVar "ProcState_V" BType_Bool)
              (BExp_nzcv_SUB_V Bit64 (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R7" (BType_Imm Bit64))));
            BStmt_Assign (BVar "ProcState_Z" BType_Bool)
              (BExp_nzcv_SUB_Z (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R7" (BType_Imm Bit64))))];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400018w)))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 0x400018w)
             "54000044 (b.mi 400020 <_stack+0x380020>  // b.first)";
         bb_statements := [];
         bb_last_statement :=
           BStmt_CJmp (BExp_Den (BVar "ProcState_N" BType_Bool))
             (BLE_Label (BL_Address (Imm64 0x400020w)))
             (BLE_Label (BL_Address (Imm64 0x40001Cw)))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 0x40001Cw) "F94000EA (ldr x10, [x7])";
         bb_statements :=
           [BStmt_Assert
              (BExp_Aligned Bit64 3 (BExp_Den (BVar "R7" (BType_Imm Bit64))));
            BStmt_Assign (BVar "R10" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_Den (BVar "R7" (BType_Imm Bit64))) BEnd_LittleEndian
                 Bit64)];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400020w)))|>;
       <|bb_label := BL_Address_HC (Imm64 0x400020w) "D65F03C0 (ret)";
         bb_statements := [];
         bb_last_statement :=
           BStmt_Jmp (BLE_Exp (BExp_Den (BVar "R30" (BType_Imm Bit64))))|>]
:bir_val_t bir_program_t
``;

val prog_14_mem_address_pc = ``
F
``;

val prog_14_cache_tag_index = ``
F
``;

val prog_14_cache_tag_only = ``
F
``;

val prog_14_cache_index_only = ``
F
``;

val prog_14_cache_tag_index_part = ``
F
``;

val prog_14_cache_tag_index_part_page = ``
F
``;

val prog_14_cache_speculation = ``
BirProgram
      [<|bb_label := BL_Address (Imm64 0x400000w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_Const (Imm64 0x400000w)] HD;
            BStmt_Assign (BVar "R4" (BType_Imm Bit64))
              (BExp_Const (Imm64 8w))];
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
                       (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R3" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R3" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 0xFFFFFFFFFFFFFFF7w)))
                 (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_Or
                       (BExp_BinPred BIExp_LessThan
                          (BExp_Const (Imm64 0x400000w))
                          (BExp_BinExp BIExp_Plus
                             (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                             (BExp_Den (BVar "R3" (BType_Imm Bit64)))))
                       (BExp_BinPred BIExp_LessOrEqual
                          (BExp_BinExp BIExp_Plus (BExp_Const (Imm64 8w))
                             (BExp_BinExp BIExp_Plus
                                (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                                (BExp_Den (BVar "R3" (BType_Imm Bit64)))))
                          (BExp_Const (Imm64 0x400000w))))
                    (BExp_BinExp BIExp_Or
                       (BExp_BinPred BIExp_LessThan
                          (BExp_BinExp BIExp_Plus
                             (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                             (BExp_Den (BVar "R3" (BType_Imm Bit64))))
                          (BExp_Const (Imm64 0x400000w)))
                       (BExp_BinPred BIExp_LessOrEqual
                          (BExp_Const (Imm64 0x400024w))
                          (BExp_BinExp BIExp_Plus
                             (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                             (BExp_Den (BVar "R3" (BType_Imm Bit64))))))));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 0xFFCC0000w))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R3" (BType_Imm Bit64)))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R3" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 0xFFCCFF80w))));
            BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R3" (BType_Imm Bit64)))] HD;
            BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
              (BExp_Store (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R3" (BType_Imm Bit64))))
                 BEnd_LittleEndian (BExp_Den (BVar "R4" (BType_Imm Bit64))))];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400008w)))|>;
       <|bb_label := BL_Address (Imm64 0x400008w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_Const (Imm64 0x400008w)] HD;
            BStmt_Assign (BVar "R4" (BType_Imm Bit64))
              (BExp_BinExp BIExp_And (BExp_Const (Imm64 0xFFFFFFFFFFFFFFFFw))
                 (BExp_BinExp BIExp_LeftShift
                    (BExp_Den (BVar "R4" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 3w))))];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40000Cw)))|>;
       <|bb_label := BL_Address (Imm64 0x40000Cw);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_Const (Imm64 0x40000Cw)] HD;
            BStmt_Assign (BVar "R5" (BType_Imm Bit64))
              (BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "R2" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R4" (BType_Imm Bit64))))];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400010w)))|>;
       <|bb_label := BL_Address (Imm64 0x400010w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_Const (Imm64 0x400010w)] HD;
            BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R5" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R6" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 0xFFCC0000w))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R5" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R6" (BType_Imm Bit64)))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R5" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R6" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 0xFFCCFF80w))));
            BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "R5" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R6" (BType_Imm Bit64)))] HD;
            BStmt_Assign (BVar "R7" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R5" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R6" (BType_Imm Bit64))))
                 BEnd_LittleEndian Bit64)];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400014w)))|>;
       <|bb_label := BL_Address (Imm64 0x400014w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_Const (Imm64 0x400014w)] HD;
            BStmt_Assign (BVar "ProcState_C" (BType_Imm Bit1))
              (BExp_BinPred BIExp_LessOrEqual
                 (BExp_Den (BVar "R7" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R1" (BType_Imm Bit64))));
            BStmt_Assign (BVar "ProcState_N" (BType_Imm Bit1))
              (BExp_BinPred BIExp_SignedLessThan
                 (BExp_BinExp BIExp_Minus
                    (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R7" (BType_Imm Bit64))))
                 (BExp_Const (Imm64 0w)));
            BStmt_Assign (BVar "ProcState_V" (BType_Imm Bit1))
              (BExp_BinPred BIExp_Equal
                 (BExp_BinPred BIExp_SignedLessThan
                    (BExp_BinExp BIExp_Minus
                       (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R7" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 0w)))
                 (BExp_BinPred BIExp_SignedLessOrEqual
                    (BExp_Den (BVar "R7" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R1" (BType_Imm Bit64)))));
            BStmt_Assign (BVar "ProcState_Z" (BType_Imm Bit1))
              (BExp_BinPred BIExp_Equal
                 (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R7" (BType_Imm Bit64))))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "0x400018*"))|>;
       <|bb_label := BL_Address (Imm64 0x400018w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_Const (Imm64 0x400018w)] HD];
         bb_last_statement :=
           BStmt_CJmp (BExp_Den (BVar "ProcState_N" (BType_Imm Bit1)))
             (BLE_Label (BL_Address (Imm64 0x400020w)))
             (BLE_Label (BL_Address (Imm64 0x40001Cw)))|>;
       <|bb_label := BL_Address (Imm64 0x40001Cw);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_Const (Imm64 0x40001Cw)] HD;
            BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_Den (BVar "R7" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 0xFFCC0000w))
                    (BExp_Den (BVar "R7" (BType_Imm Bit64))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_Den (BVar "R7" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 0xFFCCFF80w))));
            BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_Den (BVar "R7" (BType_Imm Bit64))] HD;
            BStmt_Assign (BVar "R10" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_Den (BVar "R7" (BType_Imm Bit64))) BEnd_LittleEndian
                 Bit64)];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400020w)))|>;
       <|bb_label := BL_Address (Imm64 0x400020w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_Const (Imm64 0x400020w)] HD];
         bb_last_statement :=
           BStmt_Jmp (BLE_Exp (BExp_Den (BVar "R30" (BType_Imm Bit64))))|>;
       <|bb_label := BL_Label "0x400018*";
         bb_statements :=
           [BStmt_Assert
              (BExp_BinPred BIExp_Equal (BExp_Const (Imm64 41w))
                 (BExp_Const (Imm64 41w)));
            BStmt_Assign (BVar "ProcState_N*" (BType_Imm Bit1))
              (BExp_Den (BVar "ProcState_N" (BType_Imm Bit1)));
            BStmt_Assign (BVar "R7*" (BType_Imm Bit64))
              (BExp_Den (BVar "R7" (BType_Imm Bit64)));
            BStmt_Assign (BVar "MEM*" (BType_Mem Bit64 Bit8))
              (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))];
         bb_last_statement :=
           BStmt_CJmp
             (BExp_UnaryExp BIExp_Not
                (BExp_Den (BVar "ProcState_N*" (BType_Imm Bit1))))
             (BLE_Label (BL_Label "0x400020*"))
             (BLE_Label (BL_Label "0x40001C*"))|>;
       <|bb_label := BL_Label "0x40001C*";
         bb_statements :=
           [BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_Den (BVar "R7*" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 0xFFCC0000w))
                    (BExp_Den (BVar "R7*" (BType_Imm Bit64))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_Den (BVar "R7*" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 0xFFCCFF80w))));
            BStmt_Observe 1 (BExp_Const (Imm1 1w))
              [BExp_Den (BVar "R7*" (BType_Imm Bit64))] HD;
            BStmt_Assign (BVar "R10*" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM*" (BType_Mem Bit64 Bit8)))
                 (BExp_Den (BVar "R7*" (BType_Imm Bit64))) BEnd_LittleEndian
                 Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "0x400020*"))|>;
       <|bb_label := BL_Label "0x400020*"; bb_statements := [];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400018w)))|>]
:bir_val_t bir_program_t
``;

val prog_14_cache_speculation_first = ``
F
``;

val prog_14_test =
  ("prog_14 - spectre_v1", prog_14,
     (prog_14_mem_address_pc,
      ``F``,
      prog_14_cache_tag_index,
      prog_14_cache_tag_only,
      prog_14_cache_index_only,
      prog_14_cache_tag_index_part,
      prog_14_cache_tag_index_part_page,
      prog_14_cache_speculation,
      prog_14_cache_speculation_first)
  );
