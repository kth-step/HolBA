(* ========================= prog_9 - program with shadow function call =========================== *)

(*
=================================
.section .text
    .global main

main:
  b	f

g:
  stp	x29, x30, [sp, #-128]!
  mov	x29, sp
  ldp	x29, x30, [sp], #128
  ret

f:
  mov	w4, #0x14
  b.gt	f+0x14
  ldr	w0, [sp, #12]
  mov	w0, #0x0
  bl	g
  ldr	w0, [sp, #14]
  ret
=================================
Disassembly of section .text:

0000000000000000 <main>:
   0:	14000005 	b	14 <f>

0000000000000004 <g>:
   4:	a9b87bfd 	stp	x29, x30, [sp, #-128]!
   8:	910003fd 	mov	x29, sp
   c:	a8c87bfd 	ldp	x29, x30, [sp], #128
  10:	d65f03c0 	ret

0000000000000014 <f>:
  14:	52800284 	mov	w4, #0x14                  	// #20
  18:	5400008c 	b.gt	28 <f+0x14>
  1c:	b9400fe0 	ldr	w0, [sp, #12]
  20:	52800000 	mov	w0, #0x0                   	// #0
  24:	97fffff8 	bl	4 <g>
  28:	b840e3e0 	ldur	w0, [sp, #14]
  2c:	d65f03c0 	ret
=================================
*)

val prog_9 = ``
BirProgram
      [<|bb_label := BL_Address_HC (Imm64 0w) "14000005 (b 14 <f>)";
         bb_statements := [];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 20w)))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 4w) "A9B87BFD (stp x29, x30, [sp, #-128]!)";
         bb_statements :=
           [BStmt_Assert
              (BExp_Aligned Bit64 3
                 (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
            BStmt_Assert
              (BExp_unchanged_mem_interval_distinct Bit64 0 16777216
                 (BExp_BinExp BIExp_Minus
                    (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 128w))) 16);
            BStmt_Assign (BVar "tmp_SP_EL0" (BType_Imm Bit64))
              (BExp_BinExp BIExp_Minus
                 (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 128w)));
            BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
              (BExp_Store
                 (BExp_Store (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                    (BExp_BinExp BIExp_Minus
                       (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 128w))) BEnd_LittleEndian
                    (BExp_Den (BVar "R29" (BType_Imm Bit64))))
                 (BExp_BinExp BIExp_Minus
                    (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 120w))) BEnd_LittleEndian
                 (BExp_Den (BVar "R30" (BType_Imm Bit64))));
            BStmt_Assign (BVar "SP_EL0" (BType_Imm Bit64))
              (BExp_Den (BVar "tmp_SP_EL0" (BType_Imm Bit64)))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 8w)))|>;
       <|bb_label := BL_Address_HC (Imm64 8w) "910003FD (mov x29, sp)";
         bb_statements :=
           [BStmt_Assign (BVar "R29" (BType_Imm Bit64))
              (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 12w)))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 12w) "A8C87BFD (ldp x29, x30, [sp], #128)";
         bb_statements :=
           [BStmt_Assert
              (BExp_Aligned Bit64 3
                 (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
            BStmt_Assign (BVar "R29" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                 BEnd_LittleEndian Bit64);
            BStmt_Assign (BVar "R30" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 8w))) BEnd_LittleEndian Bit64);
            BStmt_Assign (BVar "SP_EL0" (BType_Imm Bit64))
              (BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 128w)))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 16w)))|>;
       <|bb_label := BL_Address_HC (Imm64 16w) "D65F03C0 (ret)";
         bb_statements := [];
         bb_last_statement :=
           BStmt_Jmp (BLE_Exp (BExp_Den (BVar "R30" (BType_Imm Bit64))))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 20w)
             "52800284 (mov w4, #0x14                   // #20)";
         bb_statements :=
           [BStmt_Assign (BVar "R4" (BType_Imm Bit64))
              (BExp_Const (Imm64 20w))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 24w)))|>;
       <|bb_label := BL_Address_HC (Imm64 24w) "5400008C (b.gt 28 <f+0x14>)";
         bb_statements := [];
         bb_last_statement :=
           BStmt_CJmp
             (BExp_BinPred BIExp_LessOrEqual
                (BExp_BinPred BIExp_Equal
                   (BExp_Den (BVar "ProcState_N" BType_Bool))
                   (BExp_Den (BVar "ProcState_V" BType_Bool)))
                (BExp_Den (BVar "ProcState_Z" BType_Bool)))
             (BLE_Label (BL_Address (Imm64 28w)))
             (BLE_Label (BL_Address (Imm64 40w)))|>;
       <|bb_label := BL_Address_HC (Imm64 28w) "B9400FE0 (ldr w0, [sp, #12])";
         bb_statements :=
           [BStmt_Assert
              (BExp_Aligned Bit64 2
                 (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
            BStmt_Assign (BVar "R0" (BType_Imm Bit64))
              (BExp_Cast BIExp_UnsignedCast
                 (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 12w))) BEnd_LittleEndian Bit32)
                 Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 32w)))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 32w)
             "52800000 (mov w0, #0x0                    // #0)";
         bb_statements :=
           [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
              (BExp_Const (Imm64 0w))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 36w)))|>;
       <|bb_label := BL_Address_HC (Imm64 36w) "97FFFFF8 (bl 4 <g>)";
         bb_statements :=
           [BStmt_Assign (BVar "R30" (BType_Imm Bit64))
              (BExp_Const (Imm64 40w))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 4w)))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 40w) "B840E3E0 (ldur w0, [sp, #14])";
         bb_statements :=
           [BStmt_Assert
              (BExp_Aligned Bit64 2
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 2w))));
            BStmt_Assign (BVar "R0" (BType_Imm Bit64))
              (BExp_Cast BIExp_UnsignedCast
                 (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 14w))) BEnd_LittleEndian Bit32)
                 Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 44w)))|>;
       <|bb_label := BL_Address_HC (Imm64 44w) "D65F03C0 (ret)";
         bb_statements := [];
         bb_last_statement :=
           BStmt_Jmp (BLE_Exp (BExp_Den (BVar "R30" (BType_Imm Bit64))))|>]
:bir_val_t bir_program_t
``;

val prog_9_mem_address_pc = ``
F
``;

val prog_9_mem_address_pc_lspc = ``
F
``;

val prog_9_cache_tag_index = ``
F
``;

val prog_9_cache_tag_only = ``
F
``;

val prog_9_cache_index_only = ``
F
``;

val prog_9_cache_tag_index_part = ``
F
``;

val prog_9_cache_tag_index_part_page = ``
F
``;

val prog_9_cache_speculation = ``
BirProgram
      [<|bb_label := BL_Address (Imm64 0w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w)) [BExp_Const (Imm64 0w)] HD];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 20w)))|>;
       <|bb_label := BL_Address (Imm64 4w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w)) [BExp_Const (Imm64 4w)] HD;
            BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_BinExp BIExp_Minus
                       (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 128w)))
                    (BExp_Const (Imm64 0xFFFFFFFFFFFFFFEFw)))
                 (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_Or
                       (BExp_BinPred BIExp_LessThan (BExp_Const (Imm64 0w))
                          (BExp_BinExp BIExp_Minus
                             (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                             (BExp_Const (Imm64 128w))))
                       (BExp_BinPred BIExp_LessOrEqual
                          (BExp_BinExp BIExp_Plus (BExp_Const (Imm64 16w))
                             (BExp_BinExp BIExp_Minus
                                (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                                (BExp_Const (Imm64 128w))))
                          (BExp_Const (Imm64 0w))))
                    (BExp_BinExp BIExp_Or
                       (BExp_BinPred BIExp_LessThan
                          (BExp_BinExp BIExp_Minus
                             (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                             (BExp_Const (Imm64 128w)))
                          (BExp_Const (Imm64 0w)))
                       (BExp_BinPred BIExp_LessOrEqual
                          (BExp_Const (Imm64 0x1000000w))
                          (BExp_BinExp BIExp_Minus
                             (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                             (BExp_Const (Imm64 128w)))))));
            BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 15w))) (BExp_Const (Imm64 0w)));
            BStmt_Assign (BVar "tmp_SP_EL0" (BType_Imm Bit64))
              (BExp_BinExp BIExp_Minus
                 (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 128w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 0xFFCC0000w))
                    (BExp_BinExp BIExp_Minus
                       (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 120w))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Minus
                       (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 120w)))
                    (BExp_Const (Imm64 0xFFCCFF80w))));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 0xFFCC0000w))
                    (BExp_BinExp BIExp_Minus
                       (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 128w))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Minus
                       (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 128w)))
                    (BExp_Const (Imm64 0xFFCCFF80w))));
            BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_Minus
                 (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 120w))] HD;
            BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_Minus
                 (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 128w))] HD;
            BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 15w))) (BExp_Const (Imm64 0w)));
            BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
              (BExp_Store
                 (BExp_Store (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                    (BExp_BinExp BIExp_Minus
                       (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 128w))) BEnd_LittleEndian
                    (BExp_Den (BVar "R29" (BType_Imm Bit64))))
                 (BExp_BinExp BIExp_Minus
                    (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 120w))) BEnd_LittleEndian
                 (BExp_Den (BVar "R30" (BType_Imm Bit64))));
            BStmt_Assign (BVar "SP_EL0" (BType_Imm Bit64))
              (BExp_Den (BVar "tmp_SP_EL0" (BType_Imm Bit64)))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 8w)))|>;
       <|bb_label := BL_Address (Imm64 8w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w)) [BExp_Const (Imm64 8w)] HD;
            BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 15w))) (BExp_Const (Imm64 0w)));
            BStmt_Assign (BVar "R29" (BType_Imm Bit64))
              (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 12w)))|>;
       <|bb_label := BL_Address (Imm64 12w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w)) [BExp_Const (Imm64 12w)]
              HD;
            BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 0xFFCC0000w))
                    (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 0xFFCCFF80w))));
            BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))] HD;
            BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 15w))) (BExp_Const (Imm64 0w)));
            BStmt_Assign (BVar "R29" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                 BEnd_LittleEndian Bit64);
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 0xFFCC0000w))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 8w))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 8w)))
                    (BExp_Const (Imm64 0xFFCCFF80w))));
            BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 8w))] HD;
            BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 15w))) (BExp_Const (Imm64 0w)));
            BStmt_Assign (BVar "R30" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 8w))) BEnd_LittleEndian Bit64);
            BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 15w))) (BExp_Const (Imm64 0w)));
            BStmt_Assign (BVar "SP_EL0" (BType_Imm Bit64))
              (BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 128w)))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 16w)))|>;
       <|bb_label := BL_Address (Imm64 16w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w)) [BExp_Const (Imm64 16w)]
              HD];
         bb_last_statement :=
           BStmt_Jmp (BLE_Exp (BExp_Den (BVar "R30" (BType_Imm Bit64))))|>;
       <|bb_label := BL_Address (Imm64 20w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w)) [BExp_Const (Imm64 20w)]
              HD;
            BStmt_Assign (BVar "R4" (BType_Imm Bit64))
              (BExp_Const (Imm64 20w))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 24w)))|>;
       <|bb_label := BL_Address (Imm64 24w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w)) [BExp_Const (Imm64 24w)]
              HD];
         bb_last_statement :=
           BStmt_CJmp
             (BExp_BinPred BIExp_LessOrEqual
                (BExp_BinPred BIExp_Equal
                   (BExp_Den (BVar "ProcState_N" (BType_Imm Bit1)))
                   (BExp_Den (BVar "ProcState_V" (BType_Imm Bit1))))
                (BExp_Den (BVar "ProcState_Z" (BType_Imm Bit1))))
             (BLE_Label (BL_Address (Imm64 28w)))
             (BLE_Label (BL_Address (Imm64 40w)))|>;
       <|bb_label := BL_Address (Imm64 28w);
         bb_statements :=
           [BStmt_Assert
              (BExp_BinPred BIExp_Equal (BExp_Const (Imm64 41w))
                 (BExp_Const (Imm64 41w)));
            BStmt_Assign (BVar "SP_EL0*" (BType_Imm Bit64))
              (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)));
            BStmt_Assign (BVar "R0*" (BType_Imm Bit64))
              (BExp_Den (BVar "R0" (BType_Imm Bit64)));
            BStmt_Assign (BVar "MEM*" (BType_Mem Bit64 Bit8))
              (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)));
            BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "SP_EL0*" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 2w))) (BExp_Const (Imm64 3w)))
                 (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 0xFFCC0000w))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "SP_EL0*" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 14w))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "SP_EL0*" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 14w)))
                    (BExp_Const (Imm64 0xFFCCFF80w))));
            BStmt_Observe 1 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "SP_EL0*" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 14w))] HD;
            BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_Den (BVar "SP_EL0*" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 15w))) (BExp_Const (Imm64 0w)));
            BStmt_Assign (BVar "R0*" (BType_Imm Bit64))
              (BExp_Cast BIExp_UnsignedCast
                 (BExp_Load (BExp_Den (BVar "MEM*" (BType_Mem Bit64 Bit8)))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "SP_EL0*" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 14w))) BEnd_LittleEndian Bit32)
                 Bit64);
            BStmt_Assert
              (BExp_BinPred BIExp_Equal (BExp_Const (Imm64 42w))
                 (BExp_Const (Imm64 42w)));
            BStmt_Observe 0 (BExp_Const (Imm1 1w)) [BExp_Const (Imm64 28w)]
              HD;
            BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 3w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 0xFFCC0000w))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 12w))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 12w)))
                    (BExp_Const (Imm64 0xFFCCFF80w))));
            BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 12w))] HD;
            BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 15w))) (BExp_Const (Imm64 0w)));
            BStmt_Assign (BVar "R0" (BType_Imm Bit64))
              (BExp_Cast BIExp_UnsignedCast
                 (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 12w))) BEnd_LittleEndian Bit32)
                 Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 32w)))|>;
       <|bb_label := BL_Address (Imm64 32w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w)) [BExp_Const (Imm64 32w)]
              HD;
            BStmt_Assign (BVar "R0" (BType_Imm Bit64))
              (BExp_Const (Imm64 0w))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 36w)))|>;
       <|bb_label := BL_Address (Imm64 36w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w)) [BExp_Const (Imm64 36w)]
              HD;
            BStmt_Assign (BVar "R30" (BType_Imm Bit64))
              (BExp_Const (Imm64 40w))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 4w)))|>;
       <|bb_label := BL_Address (Imm64 40w);
         bb_statements :=
           [BStmt_Assert
              (BExp_BinPred BIExp_Equal (BExp_Const (Imm64 41w))
                 (BExp_Const (Imm64 41w)));
            BStmt_Assign (BVar "SP_EL0*" (BType_Imm Bit64))
              (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)));
            BStmt_Assign (BVar "R0*" (BType_Imm Bit64))
              (BExp_Den (BVar "R0" (BType_Imm Bit64)));
            BStmt_Assign (BVar "MEM*" (BType_Mem Bit64 Bit8))
              (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)));
            BStmt_Assign (BVar "R30*" (BType_Imm Bit64))
              (BExp_Den (BVar "R30" (BType_Imm Bit64)));
            BStmt_Assign (BVar "tmp_SP_EL0*" (BType_Imm Bit64))
              (BExp_Den (BVar "tmp_SP_EL0" (BType_Imm Bit64)));
            BStmt_Assign (BVar "R29*" (BType_Imm Bit64))
              (BExp_Den (BVar "R29" (BType_Imm Bit64)));
            BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_Den (BVar "SP_EL0*" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 3w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 0xFFCC0000w))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "SP_EL0*" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 12w))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "SP_EL0*" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 12w)))
                    (BExp_Const (Imm64 0xFFCCFF80w))));
            BStmt_Observe 1 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "SP_EL0*" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 12w))] HD;
            BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_Den (BVar "SP_EL0*" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 15w))) (BExp_Const (Imm64 0w)));
            BStmt_Assign (BVar "R0*" (BType_Imm Bit64))
              (BExp_Cast BIExp_UnsignedCast
                 (BExp_Load (BExp_Den (BVar "MEM*" (BType_Mem Bit64 Bit8)))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "SP_EL0*" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 12w))) BEnd_LittleEndian Bit32)
                 Bit64);
            BStmt_Assign (BVar "R0*" (BType_Imm Bit64))
              (BExp_Const (Imm64 0w));
            BStmt_Assign (BVar "R30*" (BType_Imm Bit64))
              (BExp_Const (Imm64 40w));
            BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_Den (BVar "SP_EL0*" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_BinExp BIExp_Minus
                       (BExp_Den (BVar "SP_EL0*" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 128w)))
                    (BExp_Const (Imm64 0xFFFFFFFFFFFFFFEFw)))
                 (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_Or
                       (BExp_BinPred BIExp_LessThan (BExp_Const (Imm64 0w))
                          (BExp_BinExp BIExp_Minus
                             (BExp_Den (BVar "SP_EL0*" (BType_Imm Bit64)))
                             (BExp_Const (Imm64 128w))))
                       (BExp_BinPred BIExp_LessOrEqual
                          (BExp_BinExp BIExp_Plus (BExp_Const (Imm64 16w))
                             (BExp_BinExp BIExp_Minus
                                (BExp_Den (BVar "SP_EL0*" (BType_Imm Bit64)))
                                (BExp_Const (Imm64 128w))))
                          (BExp_Const (Imm64 0w))))
                    (BExp_BinExp BIExp_Or
                       (BExp_BinPred BIExp_LessThan
                          (BExp_BinExp BIExp_Minus
                             (BExp_Den (BVar "SP_EL0*" (BType_Imm Bit64)))
                             (BExp_Const (Imm64 128w)))
                          (BExp_Const (Imm64 0w)))
                       (BExp_BinPred BIExp_LessOrEqual
                          (BExp_Const (Imm64 0x1000000w))
                          (BExp_BinExp BIExp_Minus
                             (BExp_Den (BVar "SP_EL0*" (BType_Imm Bit64)))
                             (BExp_Const (Imm64 128w)))))));
            BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_Den (BVar "SP_EL0*" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 15w))) (BExp_Const (Imm64 0w)));
            BStmt_Assign (BVar "tmp_SP_EL0*" (BType_Imm Bit64))
              (BExp_BinExp BIExp_Minus
                 (BExp_Den (BVar "SP_EL0*" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 128w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 0xFFCC0000w))
                    (BExp_BinExp BIExp_Minus
                       (BExp_Den (BVar "SP_EL0*" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 120w))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Minus
                       (BExp_Den (BVar "SP_EL0*" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 120w)))
                    (BExp_Const (Imm64 0xFFCCFF80w))));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 0xFFCC0000w))
                    (BExp_BinExp BIExp_Minus
                       (BExp_Den (BVar "SP_EL0*" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 128w))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Minus
                       (BExp_Den (BVar "SP_EL0*" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 128w)))
                    (BExp_Const (Imm64 0xFFCCFF80w))));
            BStmt_Observe 1 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_Minus
                 (BExp_Den (BVar "SP_EL0*" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 120w))] HD;
            BStmt_Observe 1 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_Minus
                 (BExp_Den (BVar "SP_EL0*" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 128w))] HD;
            BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_Den (BVar "SP_EL0*" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 15w))) (BExp_Const (Imm64 0w)));
            BStmt_Assign (BVar "MEM*" (BType_Mem Bit64 Bit8))
              (BExp_Store
                 (BExp_Store (BExp_Den (BVar "MEM*" (BType_Mem Bit64 Bit8)))
                    (BExp_BinExp BIExp_Minus
                       (BExp_Den (BVar "SP_EL0*" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 128w))) BEnd_LittleEndian
                    (BExp_Den (BVar "R29*" (BType_Imm Bit64))))
                 (BExp_BinExp BIExp_Minus
                    (BExp_Den (BVar "SP_EL0*" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 120w))) BEnd_LittleEndian
                 (BExp_Den (BVar "R30*" (BType_Imm Bit64))));
            BStmt_Assign (BVar "SP_EL0*" (BType_Imm Bit64))
              (BExp_Den (BVar "tmp_SP_EL0*" (BType_Imm Bit64)));
            BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_Den (BVar "SP_EL0*" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 15w))) (BExp_Const (Imm64 0w)));
            BStmt_Assign (BVar "R29*" (BType_Imm Bit64))
              (BExp_Den (BVar "SP_EL0*" (BType_Imm Bit64)));
            BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_Den (BVar "SP_EL0*" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 0xFFCC0000w))
                    (BExp_Den (BVar "SP_EL0*" (BType_Imm Bit64))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_Den (BVar "SP_EL0*" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 0xFFCCFF80w))));
            BStmt_Observe 1 (BExp_Const (Imm1 1w))
              [BExp_Den (BVar "SP_EL0*" (BType_Imm Bit64))] HD;
            BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_Den (BVar "SP_EL0*" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 15w))) (BExp_Const (Imm64 0w)));
            BStmt_Assign (BVar "R29*" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM*" (BType_Mem Bit64 Bit8)))
                 (BExp_Den (BVar "SP_EL0*" (BType_Imm Bit64)))
                 BEnd_LittleEndian Bit64);
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 0xFFCC0000w))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "SP_EL0*" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 8w))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "SP_EL0*" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 8w)))
                    (BExp_Const (Imm64 0xFFCCFF80w))));
            BStmt_Observe 1 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "SP_EL0*" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 8w))] HD;
            BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_Den (BVar "SP_EL0*" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 15w))) (BExp_Const (Imm64 0w)));
            BStmt_Assign (BVar "R30*" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM*" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "SP_EL0*" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 8w))) BEnd_LittleEndian Bit64);
            BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_Den (BVar "SP_EL0*" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 15w))) (BExp_Const (Imm64 0w)));
            BStmt_Assign (BVar "SP_EL0*" (BType_Imm Bit64))
              (BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "SP_EL0*" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 128w)));
            BStmt_Assert
              (BExp_BinPred BIExp_Equal (BExp_Const (Imm64 42w))
                 (BExp_Const (Imm64 42w)));
            BStmt_Observe 0 (BExp_Const (Imm1 1w)) [BExp_Const (Imm64 40w)]
              HD;
            BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 2w))) (BExp_Const (Imm64 3w)))
                 (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 0xFFCC0000w))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 14w))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 14w)))
                    (BExp_Const (Imm64 0xFFCCFF80w))));
            BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 14w))] HD;
            BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 15w))) (BExp_Const (Imm64 0w)));
            BStmt_Assign (BVar "R0" (BType_Imm Bit64))
              (BExp_Cast BIExp_UnsignedCast
                 (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 14w))) BEnd_LittleEndian Bit32)
                 Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 44w)))|>;
       <|bb_label := BL_Address (Imm64 44w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w)) [BExp_Const (Imm64 44w)]
              HD];
         bb_last_statement :=
           BStmt_Jmp (BLE_Exp (BExp_Den (BVar "R30" (BType_Imm Bit64))))|>]
:bir_val_t bir_program_t
``;

val prog_9_cache_speculation_first = ``
F
``;

val prog_9_test =
  ("prog_9 - program with shadow function call", prog_9,
     (prog_9_mem_address_pc,
      prog_9_mem_address_pc_lspc,
      prog_9_cache_tag_index,
      prog_9_cache_tag_only,
      prog_9_cache_index_only,
      prog_9_cache_tag_index_part,
      prog_9_cache_tag_index_part_page,
      prog_9_cache_speculation,
      prog_9_cache_speculation_first)
  );
