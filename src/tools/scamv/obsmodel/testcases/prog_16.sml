(* ========================= prog_16 - cache_speculation - nested speculation =========================== *)

(*
=================================
  400000:	d10043ff 	sub	sp, sp, #0x10
  400004:	f90007e0 	str	x0, [sp, #8]
  400008:	903fe808 	adrp	x8, 80100000 <publicarray_size>
  40000c:	f9400108 	ldr	x8, [x8]
  400010:	eb080008 	subs	x8, x0, x8
  400014:	540000a2 	b.cs	400028 <simplified_case_5+0x28>  // b.hs, b.nlast
  400018:	14000001 	b	40001c <simplified_case_5+0x1c>
  40001c:	f94007e8 	ldr	x8, [sp, #8]
  400020:	b5000068 	cbnz	x8, 40002c <simplified_case_5+0x2c>
  400024:	14000001 	b	400028 <simplified_case_5+0x28>
  400028:	1400000e 	b	400060 <simplified_case_5+0x60>
  40002c:	f94007e9 	ldr	x9, [sp, #8]
  400030:	903fe808 	adrp	x8, 80100000 <publicarray_size>
  400034:	91002108 	add	x8, x8, #0x8
  400038:	f8697908 	ldr	x8, [x8, x9, lsl #3]
  40003c:	d376d509 	lsl	x9, x8, #10
  400040:	903fe808 	adrp	x8, 80100000 <publicarray_size>
  400044:	91022108 	add	x8, x8, #0x88
  400048:	f869690a 	ldr	x10, [x8, x9]
  40004c:	903fea09 	adrp	x9, 80140000 <publicarray2+0x3ff78>
  400050:	f9404528 	ldr	x8, [x9, #136]
  400054:	8a0a0108 	and	x8, x8, x10
  400058:	f9004528 	str	x8, [x9, #136]
  40005c:	14000001 	b	400060 <simplified_case_5+0x60>
  400060:	910043ff 	add	sp, sp, #0x10
  400064:	d65f03c0 	ret
=================================
*)

val prog_16 = ``
BirProgram
      [<|bb_label :=
           BL_Address_HC (Imm64 0x400000w) "D10043FF (sub sp, sp, #0x10)";
         bb_statements :=
           [BStmt_Assign (BVar "SP_EL0" (BType_Imm Bit64))
              (BExp_BinExp BIExp_Minus
                 (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 16w)))];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400004w)))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 0x400004w) "F90007E0 (str x0, [sp, #8])";
         bb_statements :=
           [BStmt_Assert
              (BExp_Aligned Bit64 3
                 (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
            BStmt_Assert
              (BExp_unchanged_mem_interval_distinct Bit64 4194304 4194408
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 8w))) 8);
            BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
              (BExp_Store (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 8w))) BEnd_LittleEndian
                 (BExp_Den (BVar "R0" (BType_Imm Bit64))))];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400008w)))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 0x400008w)
             "903FE808 (adrp x8, 80100000 <publicarray_size>)";
         bb_statements :=
           [BStmt_Assign (BVar "R8" (BType_Imm Bit64))
              (BExp_Const (Imm64 0x80100000w))];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40000Cw)))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 0x40000Cw) "F9400108 (ldr x8, [x8])";
         bb_statements :=
           [BStmt_Assert
              (BExp_Aligned Bit64 3 (BExp_Den (BVar "R8" (BType_Imm Bit64))));
            BStmt_Assign (BVar "R8" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_Den (BVar "R8" (BType_Imm Bit64))) BEnd_LittleEndian
                 Bit64)];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400010w)))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 0x400010w) "EB080008 (subs x8, x0, x8)";
         bb_statements :=
           [BStmt_Assign (BVar "ProcState_C" BType_Bool)
              (BExp_nzcv_SUB_C (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R8" (BType_Imm Bit64))));
            BStmt_Assign (BVar "ProcState_N" BType_Bool)
              (BExp_nzcv_SUB_N Bit64 (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R8" (BType_Imm Bit64))));
            BStmt_Assign (BVar "ProcState_V" BType_Bool)
              (BExp_nzcv_SUB_V Bit64 (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R8" (BType_Imm Bit64))));
            BStmt_Assign (BVar "ProcState_Z" BType_Bool)
              (BExp_nzcv_SUB_Z (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R8" (BType_Imm Bit64))));
            BStmt_Assign (BVar "R8" (BType_Imm Bit64))
              (BExp_BinExp BIExp_Minus
                 (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R8" (BType_Imm Bit64))))];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400014w)))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 0x400014w)
             "540000A2 (b.cs 400028 <simplified_case_5+0x28>  // b.hs, b.nlast)";
         bb_statements := [];
         bb_last_statement :=
           BStmt_CJmp (BExp_Den (BVar "ProcState_C" BType_Bool))
             (BLE_Label (BL_Address (Imm64 0x400028w)))
             (BLE_Label (BL_Address (Imm64 0x400018w)))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 0x400018w)
             "14000001 (b 40001c <simplified_case_5+0x1c>)";
         bb_statements := [];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40001Cw)))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 0x40001Cw) "F94007E8 (ldr x8, [sp, #8])";
         bb_statements :=
           [BStmt_Assert
              (BExp_Aligned Bit64 3
                 (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
            BStmt_Assign (BVar "R8" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 8w))) BEnd_LittleEndian Bit64)];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400020w)))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 0x400020w)
             "B5000068 (cbnz x8, 40002c <simplified_case_5+0x2c>)";
         bb_statements := [];
         bb_last_statement :=
           BStmt_CJmp
             (BExp_BinPred BIExp_Equal
                (BExp_Den (BVar "R8" (BType_Imm Bit64)))
                (BExp_Const (Imm64 0w)))
             (BLE_Label (BL_Address (Imm64 0x40002Cw)))
             (BLE_Label (BL_Address (Imm64 0x400024w)))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 0x400024w)
             "14000001 (b 40001c <simplified_case_5+0x1c>)";
         bb_statements := [];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400028w)))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 0x400028w)
             "1400000E (b 400060 <simplified_case_5+0x60>)";
         bb_statements := [];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400060w)))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 0x40002Cw) "F94007E9 (ldr x9, [sp, #8])";
         bb_statements :=
           [BStmt_Assert
              (BExp_Aligned Bit64 3
                 (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
            BStmt_Assign (BVar "R9" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 8w))) BEnd_LittleEndian Bit64)];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400030w)))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 0x400030w)
             "903FE808 (adrp x8, 80100000 <publicarray_size>)";
         bb_statements :=
           [BStmt_Assign (BVar "R8" (BType_Imm Bit64))
              (BExp_Const (Imm64 0x80100000w))];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400034w)))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 0x400034w) "91002108 (add x8, x8, #0x8)";
         bb_statements :=
           [BStmt_Assign (BVar "R8" (BType_Imm Bit64))
              (BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "R8" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 8w)))];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400038w)))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 0x400038w)
             "F8697908 (ldr x8, [x8, x9, lsl #3])";
         bb_statements :=
           [BStmt_Assert
              (BExp_Aligned Bit64 3
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R8" (BType_Imm Bit64)))
                    (BExp_BinExp BIExp_LeftShift
                       (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 3w)))));
            BStmt_Assign (BVar "R8" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R8" (BType_Imm Bit64)))
                    (BExp_BinExp BIExp_LeftShift
                       (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 3w)))) BEnd_LittleEndian Bit64)];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40003Cw)))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 0x40003Cw) "D376D509 (lsl x9, x8, #10)";
         bb_statements :=
           [BStmt_Assign (BVar "R9" (BType_Imm Bit64))
              (BExp_BinExp BIExp_And (BExp_Const (Imm64 0xFFFFFFFFFFFFFFFFw))
                 (BExp_BinExp BIExp_LeftShift
                    (BExp_Den (BVar "R8" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 10w))))];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400040w)))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 0x400040w)
             "903FE808 (adrp x8, 80100000 <publicarray_size>)";
         bb_statements :=
           [BStmt_Assign (BVar "R8" (BType_Imm Bit64))
              (BExp_Const (Imm64 0x80100000w))];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400044w)))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 0x400044w) "91022108 (add x8, x8, #0x88)";
         bb_statements :=
           [BStmt_Assign (BVar "R8" (BType_Imm Bit64))
              (BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "R8" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 136w)))];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400048w)))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 0x400048w) "F869690A (ldr x10, [x8, x9])";
         bb_statements :=
           [BStmt_Assert
              (BExp_Aligned Bit64 3
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R8" (BType_Imm Bit64)))));
            BStmt_Assign (BVar "R10" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R8" (BType_Imm Bit64))))
                 BEnd_LittleEndian Bit64)];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40004Cw)))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 0x40004Cw)
             "903FEA09 (adrp x9, 80140000 <publicarray2+0x3ff78>)";
         bb_statements :=
           [BStmt_Assign (BVar "R9" (BType_Imm Bit64))
              (BExp_Const (Imm64 0x80140000w))];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400050w)))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 0x400050w) "F9404528 (ldr x8, [x9, #136])";
         bb_statements :=
           [BStmt_Assert
              (BExp_Aligned Bit64 3 (BExp_Den (BVar "R9" (BType_Imm Bit64))));
            BStmt_Assign (BVar "R8" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 136w))) BEnd_LittleEndian Bit64)];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400054w)))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 0x400054w) "8A0A0108 (and x8, x8, x10)";
         bb_statements :=
           [BStmt_Assign (BVar "R8" (BType_Imm Bit64))
              (BExp_BinExp BIExp_And (BExp_Den (BVar "R8" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R10" (BType_Imm Bit64))))];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400058w)))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 0x400058w) "F9004528 (str x8, [x9, #136])";
         bb_statements :=
           [BStmt_Assert
              (BExp_Aligned Bit64 3 (BExp_Den (BVar "R9" (BType_Imm Bit64))));
            BStmt_Assert
              (BExp_unchanged_mem_interval_distinct Bit64 4194304 4194408
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 136w))) 8);
            BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
              (BExp_Store (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 136w))) BEnd_LittleEndian
                 (BExp_Den (BVar "R8" (BType_Imm Bit64))))];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40005Cw)))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 0x40005Cw)
             "14000001 (b 40001c <simplified_case_5+0x1c>)";
         bb_statements := [];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400060w)))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 0x400060w) "910043FF (add sp, sp, #0x10)";
         bb_statements :=
           [BStmt_Assign (BVar "SP_EL0" (BType_Imm Bit64))
              (BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 16w)))];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400064w)))|>;
       <|bb_label := BL_Address_HC (Imm64 0x400064w) "D65F03C0 (ret)";
         bb_statements := [];
         bb_last_statement :=
           BStmt_Jmp (BLE_Exp (BExp_Den (BVar "R30" (BType_Imm Bit64))))|>]
:bir_val_t bir_program_t
``;

val prog_16_mem_address_pc = ``
F
``;

val prog_16_cache_tag_index = ``
F
``;

val prog_16_cache_tag_only = ``
F
``;

val prog_16_cache_index_only = ``
F
``;

val prog_16_cache_tag_index_part = ``
F
``;

val prog_16_cache_tag_index_part_page = ``
F
``;

val prog_16_cache_speculation = ``
BirProgram
      [<|bb_label := BL_Address (Imm64 0x400000w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_Const (Imm64 0x400000w)] HD;
            BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 15w))) (BExp_Const (Imm64 0w)));
            BStmt_Assign (BVar "SP_EL0" (BType_Imm Bit64))
              (BExp_BinExp BIExp_Minus
                 (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 16w)))];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400004w)))|>;
       <|bb_label := BL_Address (Imm64 0x400004w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_Const (Imm64 0x400004w)] HD;
            BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 8w)))
                    (BExp_Const (Imm64 0xFFFFFFFFFFFFFFF7w)))
                 (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_Or
                       (BExp_BinPred BIExp_LessThan
                          (BExp_Const (Imm64 0x400000w))
                          (BExp_BinExp BIExp_Plus
                             (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                             (BExp_Const (Imm64 8w))))
                       (BExp_BinPred BIExp_LessOrEqual
                          (BExp_BinExp BIExp_Plus (BExp_Const (Imm64 8w))
                             (BExp_BinExp BIExp_Plus
                                (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                                (BExp_Const (Imm64 8w))))
                          (BExp_Const (Imm64 0x400000w))))
                    (BExp_BinExp BIExp_Or
                       (BExp_BinPred BIExp_LessThan
                          (BExp_BinExp BIExp_Plus
                             (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                             (BExp_Const (Imm64 8w)))
                          (BExp_Const (Imm64 0x400000w)))
                       (BExp_BinPred BIExp_LessOrEqual
                          (BExp_Const (Imm64 0x400068w))
                          (BExp_BinExp BIExp_Plus
                             (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                             (BExp_Const (Imm64 8w)))))));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 0xFFCCB000w))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 8w))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 8w)))
                    (BExp_Const (Imm64 0xFFCCFFF0w))));
            BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 8w))] HD;
            BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 15w))) (BExp_Const (Imm64 0w)));
            BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
              (BExp_Store (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 8w))) BEnd_LittleEndian
                 (BExp_Den (BVar "R0" (BType_Imm Bit64))))];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400008w)))|>;
       <|bb_label := BL_Address (Imm64 0x400008w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_Const (Imm64 0x400008w)] HD;
            BStmt_Assign (BVar "R8" (BType_Imm Bit64))
              (BExp_Const (Imm64 0x80100000w))];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40000Cw)))|>;
       <|bb_label := BL_Address (Imm64 0x40000Cw);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_Const (Imm64 0x40000Cw)] HD;
            BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_Den (BVar "R8" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 0xFFCC0000w))
                    (BExp_Den (BVar "R8" (BType_Imm Bit64))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_Den (BVar "R8" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 0xFFCCAFF0w))));
            BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_Den (BVar "R8" (BType_Imm Bit64))] HD;
            BStmt_Assign (BVar "R8" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_Den (BVar "R8" (BType_Imm Bit64))) BEnd_LittleEndian
                 Bit64)];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400010w)))|>;
       <|bb_label := BL_Address (Imm64 0x400010w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_Const (Imm64 0x400010w)] HD;
            BStmt_Assign (BVar "ProcState_C" (BType_Imm Bit1))
              (BExp_BinPred BIExp_LessOrEqual
                 (BExp_Den (BVar "R8" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R0" (BType_Imm Bit64))));
            BStmt_Assign (BVar "ProcState_N" (BType_Imm Bit1))
              (BExp_BinPred BIExp_SignedLessThan
                 (BExp_BinExp BIExp_Minus
                    (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R8" (BType_Imm Bit64))))
                 (BExp_Const (Imm64 0w)));
            BStmt_Assign (BVar "ProcState_V" (BType_Imm Bit1))
              (BExp_BinPred BIExp_Equal
                 (BExp_BinPred BIExp_SignedLessThan
                    (BExp_BinExp BIExp_Minus
                       (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R8" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 0w)))
                 (BExp_BinPred BIExp_SignedLessOrEqual
                    (BExp_Den (BVar "R8" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R0" (BType_Imm Bit64)))));
            BStmt_Assign (BVar "ProcState_Z" (BType_Imm Bit1))
              (BExp_BinPred BIExp_Equal
                 (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R8" (BType_Imm Bit64))));
            BStmt_Assign (BVar "R8" (BType_Imm Bit64))
              (BExp_BinExp BIExp_Minus
                 (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R8" (BType_Imm Bit64))))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "0x400014*"))|>;
       <|bb_label := BL_Address (Imm64 0x400014w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_Const (Imm64 0x400014w)] HD];
         bb_last_statement :=
           BStmt_CJmp (BExp_Den (BVar "ProcState_C" (BType_Imm Bit1)))
             (BLE_Label (BL_Address (Imm64 0x400028w)))
             (BLE_Label (BL_Address (Imm64 0x400018w)))|>;
       <|bb_label := BL_Address (Imm64 0x400018w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_Const (Imm64 0x400018w)] HD];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40001Cw)))|>;
       <|bb_label := BL_Address (Imm64 0x40001Cw);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_Const (Imm64 0x40001Cw)] HD;
            BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 0xFFCCB000w))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 8w))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 8w)))
                    (BExp_Const (Imm64 0xFFCCFFF0w))));
            BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 8w))] HD;
            BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 15w))) (BExp_Const (Imm64 0w)));
            BStmt_Assign (BVar "R8" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 8w))) BEnd_LittleEndian Bit64)];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400020w)))|>;
       <|bb_label := BL_Address (Imm64 0x400020w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_Const (Imm64 0x400020w)] HD];
         bb_last_statement :=
           BStmt_CJmp
             (BExp_BinPred BIExp_Equal
                (BExp_Den (BVar "R8" (BType_Imm Bit64)))
                (BExp_Const (Imm64 0w)))
             (BLE_Label (BL_Address (Imm64 0x40002Cw)))
             (BLE_Label (BL_Address (Imm64 0x400024w)))|>;
       <|bb_label := BL_Address (Imm64 0x400024w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_Const (Imm64 0x400024w)] HD];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400028w)))|>;
       <|bb_label := BL_Address (Imm64 0x400028w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_Const (Imm64 0x400028w)] HD];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400060w)))|>;
       <|bb_label := BL_Address (Imm64 0x40002Cw);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_Const (Imm64 0x40002Cw)] HD;
            BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 0xFFCCB000w))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 8w))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 8w)))
                    (BExp_Const (Imm64 0xFFCCFFF0w))));
            BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 8w))] HD;
            BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 15w))) (BExp_Const (Imm64 0w)));
            BStmt_Assign (BVar "R9" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 8w))) BEnd_LittleEndian Bit64)];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400030w)))|>;
       <|bb_label := BL_Address (Imm64 0x400030w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_Const (Imm64 0x400030w)] HD;
            BStmt_Assign (BVar "R8" (BType_Imm Bit64))
              (BExp_Const (Imm64 0x80100000w))];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400034w)))|>;
       <|bb_label := BL_Address (Imm64 0x400034w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_Const (Imm64 0x400034w)] HD;
            BStmt_Assign (BVar "R8" (BType_Imm Bit64))
              (BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "R8" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 8w)))];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400038w)))|>;
       <|bb_label := BL_Address (Imm64 0x400038w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_Const (Imm64 0x400038w)] HD;
            BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R8" (BType_Imm Bit64)))
                       (BExp_BinExp BIExp_LeftShift
                          (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                          (BExp_Const (Imm64 3w)))) (BExp_Const (Imm64 7w)))
                 (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 0xFFCC0000w))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R8" (BType_Imm Bit64)))
                       (BExp_BinExp BIExp_LeftShift
                          (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                          (BExp_Const (Imm64 3w)))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R8" (BType_Imm Bit64)))
                       (BExp_BinExp BIExp_LeftShift
                          (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                          (BExp_Const (Imm64 3w))))
                    (BExp_Const (Imm64 0xFFCCAFF0w))));
            BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "R8" (BType_Imm Bit64)))
                 (BExp_BinExp BIExp_LeftShift
                    (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 3w)))] HD;
            BStmt_Assign (BVar "R8" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R8" (BType_Imm Bit64)))
                    (BExp_BinExp BIExp_LeftShift
                       (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 3w)))) BEnd_LittleEndian Bit64)];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40003Cw)))|>;
       <|bb_label := BL_Address (Imm64 0x40003Cw);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_Const (Imm64 0x40003Cw)] HD;
            BStmt_Assign (BVar "R9" (BType_Imm Bit64))
              (BExp_BinExp BIExp_And (BExp_Const (Imm64 0xFFFFFFFFFFFFFFFFw))
                 (BExp_BinExp BIExp_LeftShift
                    (BExp_Den (BVar "R8" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 10w))))];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400040w)))|>;
       <|bb_label := BL_Address (Imm64 0x400040w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_Const (Imm64 0x400040w)] HD;
            BStmt_Assign (BVar "R8" (BType_Imm Bit64))
              (BExp_Const (Imm64 0x80100000w))];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400044w)))|>;
       <|bb_label := BL_Address (Imm64 0x400044w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_Const (Imm64 0x400044w)] HD;
            BStmt_Assign (BVar "R8" (BType_Imm Bit64))
              (BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "R8" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 136w)))];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400048w)))|>;
       <|bb_label := BL_Address (Imm64 0x400048w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_Const (Imm64 0x400048w)] HD;
            BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R8" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 0xFFCC0000w))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R8" (BType_Imm Bit64)))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R8" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 0xFFCCAFF0w))));
            BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R8" (BType_Imm Bit64)))] HD;
            BStmt_Assign (BVar "R10" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R8" (BType_Imm Bit64))))
                 BEnd_LittleEndian Bit64)];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40004Cw)))|>;
       <|bb_label := BL_Address (Imm64 0x40004Cw);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_Const (Imm64 0x40004Cw)] HD;
            BStmt_Assign (BVar "R9" (BType_Imm Bit64))
              (BExp_Const (Imm64 0x80140000w))];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400050w)))|>;
       <|bb_label := BL_Address (Imm64 0x400050w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_Const (Imm64 0x400050w)] HD;
            BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 0xFFCC0000w))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 136w))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 136w)))
                    (BExp_Const (Imm64 0xFFCCAFF0w))));
            BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 136w))] HD;
            BStmt_Assign (BVar "R8" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 136w))) BEnd_LittleEndian Bit64)];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400054w)))|>;
       <|bb_label := BL_Address (Imm64 0x400054w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_Const (Imm64 0x400054w)] HD;
            BStmt_Assign (BVar "R8" (BType_Imm Bit64))
              (BExp_BinExp BIExp_And (BExp_Den (BVar "R8" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R10" (BType_Imm Bit64))))];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400058w)))|>;
       <|bb_label := BL_Address (Imm64 0x400058w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_Const (Imm64 0x400058w)] HD;
            BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 136w)))
                    (BExp_Const (Imm64 0xFFFFFFFFFFFFFFF7w)))
                 (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_Or
                       (BExp_BinPred BIExp_LessThan
                          (BExp_Const (Imm64 0x400000w))
                          (BExp_BinExp BIExp_Plus
                             (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                             (BExp_Const (Imm64 136w))))
                       (BExp_BinPred BIExp_LessOrEqual
                          (BExp_BinExp BIExp_Plus (BExp_Const (Imm64 8w))
                             (BExp_BinExp BIExp_Plus
                                (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                                (BExp_Const (Imm64 136w))))
                          (BExp_Const (Imm64 0x400000w))))
                    (BExp_BinExp BIExp_Or
                       (BExp_BinPred BIExp_LessThan
                          (BExp_BinExp BIExp_Plus
                             (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                             (BExp_Const (Imm64 136w)))
                          (BExp_Const (Imm64 0x400000w)))
                       (BExp_BinPred BIExp_LessOrEqual
                          (BExp_Const (Imm64 0x400068w))
                          (BExp_BinExp BIExp_Plus
                             (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                             (BExp_Const (Imm64 136w)))))));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 0xFFCC0000w))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 136w))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 136w)))
                    (BExp_Const (Imm64 0xFFCCAFF0w))));
            BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 136w))] HD;
            BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
              (BExp_Store (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 136w))) BEnd_LittleEndian
                 (BExp_Den (BVar "R8" (BType_Imm Bit64))))];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40005Cw)))|>;
       <|bb_label := BL_Address (Imm64 0x40005Cw);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_Const (Imm64 0x40005Cw)] HD];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400060w)))|>;
       <|bb_label := BL_Address (Imm64 0x400060w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_Const (Imm64 0x400060w)] HD;
            BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 15w))) (BExp_Const (Imm64 0w)));
            BStmt_Assign (BVar "SP_EL0" (BType_Imm Bit64))
              (BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 16w)))];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400064w)))|>;
       <|bb_label := BL_Address (Imm64 0x400064w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_Const (Imm64 0x400064w)] HD];
         bb_last_statement :=
           BStmt_Jmp (BLE_Exp (BExp_Den (BVar "R30" (BType_Imm Bit64))))|>;
       <|bb_label := BL_Label "0x400014*";
         bb_statements :=
           [BStmt_Assert
              (BExp_BinPred BIExp_Equal (BExp_Const (Imm64 41w))
                 (BExp_Const (Imm64 41w)));
            BStmt_Assign (BVar "ProcState_C*" (BType_Imm Bit1))
              (BExp_Den (BVar "ProcState_C" (BType_Imm Bit1)));
            BStmt_Assign (BVar "SP_EL0*" (BType_Imm Bit64))
              (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)));
            BStmt_Assign (BVar "MEM*" (BType_Mem Bit64 Bit8))
              (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)));
            BStmt_Assign (BVar "R8*" (BType_Imm Bit64))
              (BExp_Den (BVar "R8" (BType_Imm Bit64)));
            BStmt_Assign (BVar "R9*" (BType_Imm Bit64))
              (BExp_Den (BVar "R9" (BType_Imm Bit64)));
            BStmt_Assign (BVar "R10*" (BType_Imm Bit64))
              (BExp_Den (BVar "R10" (BType_Imm Bit64)))];
         bb_last_statement :=
           BStmt_CJmp
             (BExp_UnaryExp BIExp_Not
                (BExp_Den (BVar "ProcState_C*" (BType_Imm Bit1))))
             (BLE_Label (BL_Label "0x400028*"))
             (BLE_Label (BL_Label "0x400018*"))|>;
       <|bb_label := BL_Label "0x400018*"; bb_statements := [];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "0x40001C*"))|>;
       <|bb_label := BL_Label "0x40001C*";
         bb_statements :=
           [BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_Den (BVar "SP_EL0*" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 0xFFCCB000w))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "SP_EL0*" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 8w))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "SP_EL0*" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 8w)))
                    (BExp_Const (Imm64 0xFFCCFFF0w))));
            BStmt_Observe 1 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "SP_EL0*" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 8w))] HD;
            BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_Den (BVar "SP_EL0*" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 15w))) (BExp_Const (Imm64 0w)));
            BStmt_Assign (BVar "R8*" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM*" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "SP_EL0*" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 8w))) BEnd_LittleEndian Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "0x400020*"))|>;
       <|bb_label := BL_Label "0x400020*"; bb_statements := [];
         bb_last_statement :=
           BStmt_CJmp
             (BExp_UnaryExp BIExp_Not
                (BExp_BinPred BIExp_Equal
                   (BExp_Den (BVar "R8*" (BType_Imm Bit64)))
                   (BExp_Const (Imm64 0w))))
             (BLE_Label (BL_Label "0x40002C*"))
             (BLE_Label (BL_Label "0x400024*"))|>;
       <|bb_label := BL_Label "0x400024*"; bb_statements := [];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "0x400028*"))|>;
       <|bb_label := BL_Label "0x400028*"; bb_statements := [];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "0x400060*"))|>;
       <|bb_label := BL_Label "0x400060*";
         bb_statements :=
           [BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_Den (BVar "SP_EL0*" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 15w))) (BExp_Const (Imm64 0w)));
            BStmt_Assign (BVar "SP_EL0*" (BType_Imm Bit64))
              (BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "SP_EL0*" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 16w)))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "0x400064*"))|>;
       <|bb_label := BL_Label "0x400064*";
         bb_statements :=
           [BStmt_Assert
              (BExp_BinPred BIExp_Equal (BExp_Const (Imm64 42w))
                 (BExp_Const (Imm64 42w)))];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400014w)))|>;
       <|bb_label := BL_Label "0x40002C*";
         bb_statements :=
           [BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_Den (BVar "SP_EL0*" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 0xFFCCB000w))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "SP_EL0*" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 8w))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "SP_EL0*" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 8w)))
                    (BExp_Const (Imm64 0xFFCCFFF0w))));
            BStmt_Observe 1 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "SP_EL0*" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 8w))] HD;
            BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_Den (BVar "SP_EL0*" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 15w))) (BExp_Const (Imm64 0w)));
            BStmt_Assign (BVar "R9*" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM*" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "SP_EL0*" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 8w))) BEnd_LittleEndian Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "0x400030*"))|>;
       <|bb_label := BL_Label "0x400030*";
         bb_statements :=
           [BStmt_Assign (BVar "R8*" (BType_Imm Bit64))
              (BExp_Const (Imm64 0x80100000w))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "0x400034*"))|>;
       <|bb_label := BL_Label "0x400034*";
         bb_statements :=
           [BStmt_Assign (BVar "R8*" (BType_Imm Bit64))
              (BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "R8*" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 8w)))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "0x400038*"))|>;
       <|bb_label := BL_Label "0x400038*";
         bb_statements :=
           [BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R8*" (BType_Imm Bit64)))
                       (BExp_BinExp BIExp_LeftShift
                          (BExp_Den (BVar "R9*" (BType_Imm Bit64)))
                          (BExp_Const (Imm64 3w)))) (BExp_Const (Imm64 7w)))
                 (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 0xFFCC0000w))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R8*" (BType_Imm Bit64)))
                       (BExp_BinExp BIExp_LeftShift
                          (BExp_Den (BVar "R9*" (BType_Imm Bit64)))
                          (BExp_Const (Imm64 3w)))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R8*" (BType_Imm Bit64)))
                       (BExp_BinExp BIExp_LeftShift
                          (BExp_Den (BVar "R9*" (BType_Imm Bit64)))
                          (BExp_Const (Imm64 3w))))
                    (BExp_Const (Imm64 0xFFCCAFF0w))));
            BStmt_Observe 1 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "R8*" (BType_Imm Bit64)))
                 (BExp_BinExp BIExp_LeftShift
                    (BExp_Den (BVar "R9*" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 3w)))] HD;
            BStmt_Assign (BVar "R8*" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM*" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R8*" (BType_Imm Bit64)))
                    (BExp_BinExp BIExp_LeftShift
                       (BExp_Den (BVar "R9*" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 3w)))) BEnd_LittleEndian Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "0x40003C*"))|>;
       <|bb_label := BL_Label "0x40003C*";
         bb_statements :=
           [BStmt_Assign (BVar "R9*" (BType_Imm Bit64))
              (BExp_BinExp BIExp_And (BExp_Const (Imm64 0xFFFFFFFFFFFFFFFFw))
                 (BExp_BinExp BIExp_LeftShift
                    (BExp_Den (BVar "R8*" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 10w))))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "0x400040*"))|>;
       <|bb_label := BL_Label "0x400040*";
         bb_statements :=
           [BStmt_Assign (BVar "R8*" (BType_Imm Bit64))
              (BExp_Const (Imm64 0x80100000w))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "0x400044*"))|>;
       <|bb_label := BL_Label "0x400044*";
         bb_statements :=
           [BStmt_Assign (BVar "R8*" (BType_Imm Bit64))
              (BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "R8*" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 136w)))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "0x400048*"))|>;
       <|bb_label := BL_Label "0x400048*";
         bb_statements :=
           [BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R9*" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R8*" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 0xFFCC0000w))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R9*" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R8*" (BType_Imm Bit64)))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R9*" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R8*" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 0xFFCCAFF0w))));
            BStmt_Observe 1 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "R9*" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R8*" (BType_Imm Bit64)))] HD;
            BStmt_Assign (BVar "R10*" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM*" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R9*" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R8*" (BType_Imm Bit64))))
                 BEnd_LittleEndian Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "0x40004C*"))|>;
       <|bb_label := BL_Label "0x40004C*";
         bb_statements :=
           [BStmt_Assign (BVar "R9*" (BType_Imm Bit64))
              (BExp_Const (Imm64 0x80140000w))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "0x400050*"))|>;
       <|bb_label := BL_Label "0x400050*";
         bb_statements :=
           [BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_Den (BVar "R9*" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 0xFFCC0000w))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R9*" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 136w))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R9*" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 136w)))
                    (BExp_Const (Imm64 0xFFCCAFF0w))));
            BStmt_Observe 1 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "R9*" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 136w))] HD;
            BStmt_Assign (BVar "R8*" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM*" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R9*" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 136w))) BEnd_LittleEndian Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "0x400054*"))|>;
       <|bb_label := BL_Label "0x400054*";
         bb_statements :=
           [BStmt_Assign (BVar "R8*" (BType_Imm Bit64))
              (BExp_BinExp BIExp_And
                 (BExp_Den (BVar "R8*" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R10*" (BType_Imm Bit64))))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "0x400058*"))|>;
       <|bb_label := BL_Label "0x400058*";
         bb_statements :=
           [BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_Den (BVar "R9*" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R9*" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 136w)))
                    (BExp_Const (Imm64 0xFFFFFFFFFFFFFFF7w)))
                 (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_Or
                       (BExp_BinPred BIExp_LessThan
                          (BExp_Const (Imm64 0x400000w))
                          (BExp_BinExp BIExp_Plus
                             (BExp_Den (BVar "R9*" (BType_Imm Bit64)))
                             (BExp_Const (Imm64 136w))))
                       (BExp_BinPred BIExp_LessOrEqual
                          (BExp_BinExp BIExp_Plus (BExp_Const (Imm64 8w))
                             (BExp_BinExp BIExp_Plus
                                (BExp_Den (BVar "R9*" (BType_Imm Bit64)))
                                (BExp_Const (Imm64 136w))))
                          (BExp_Const (Imm64 0x400000w))))
                    (BExp_BinExp BIExp_Or
                       (BExp_BinPred BIExp_LessThan
                          (BExp_BinExp BIExp_Plus
                             (BExp_Den (BVar "R9*" (BType_Imm Bit64)))
                             (BExp_Const (Imm64 136w)))
                          (BExp_Const (Imm64 0x400000w)))
                       (BExp_BinPred BIExp_LessOrEqual
                          (BExp_Const (Imm64 0x400068w))
                          (BExp_BinExp BIExp_Plus
                             (BExp_Den (BVar "R9*" (BType_Imm Bit64)))
                             (BExp_Const (Imm64 136w)))))));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 0xFFCC0000w))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R9*" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 136w))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R9*" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 136w)))
                    (BExp_Const (Imm64 0xFFCCAFF0w))));
            BStmt_Observe 1 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "R9*" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 136w))] HD;
            BStmt_Assign (BVar "MEM*" (BType_Mem Bit64 Bit8))
              (BExp_Store (BExp_Den (BVar "MEM*" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R9*" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 136w))) BEnd_LittleEndian
                 (BExp_Den (BVar "R8*" (BType_Imm Bit64))))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "0x40005C*"))|>;
       <|bb_label := BL_Label "0x40005C*"; bb_statements := [];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "0x400060*"))|>]
:bir_val_t bir_program_t
``;

val prog_16_cache_speculation_first = ``
F
``;

val prog_16_test =
  ("prog_16 - cache_speculation - nested speculation", prog_16,
     (prog_16_mem_address_pc,
      ``F``,
      prog_16_cache_tag_index,
      prog_16_cache_tag_only,
      prog_16_cache_index_only,
      prog_16_cache_tag_index_part,
      prog_16_cache_tag_index_part_page,
      prog_16_cache_speculation,
      prog_16_cache_speculation_first)
  );
