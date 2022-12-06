(* ========================= prog_13 - nested branch =========================== *)

(*
=================================
	add x21, x1, x2
	ldr x14, [x13, x21]
	cmp x14, x22
	b.hs #0x20
	str x14, [x5, x4]
	cmp x2, x9
	b.lt #0xC
	lsl x14, x14, #0x8
	b #0x8
	ldr x14, [x5, x4]
	ret
	cmp x1, x17
	b.eq #0xC
	add x21, x1, x2
	b #0xC
	nop
	b #0x8
	ret
	ldr x2, [x21]
        ret
=================================
*)
(*
           0
	   |
	   4
	   |
	   8
	   |
	   12*
	 /     \
         |      16*
         |      |
         |      20*
         |      |
         |      24*
         |    /     \
         |  36*      28*
         |   |       |
         |   |       32*
         |    \      |
         |     \     /  
         |       40* 
         44*       |
         |         |
         48*       |
       /     \     |
     60*      52*  |
     |        |    |
     64*      56*  |
     |        |    |
     72*      68*  |
     |        |    |
     76*      |    |
     |        |    /
     \        |   /
      \       |  /
       —————  12
	    /     \
            |      16
            |      |
            |      20
            |      |
            |      24
            |    /     \
            |  36       28
            |   |       |
            |   |       32
            |    \      |
            |     \     /  
            |       40 
            44
            |
            48
          /    \
        60      52
        |       |
        64      56
        |       |
        72      68
        |
        76

*)

val prog_13 = ``
BirProgram
      [<|bb_label := BL_Address_HC (Imm64 0w) "8B020035 (add x21, x1, x2)";
         bb_statements :=
           [BStmt_Assign (BVar "R21" (BType_Imm Bit64))
              (BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R2" (BType_Imm Bit64))))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 4w)))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 4w) "F87569AE (ldr x14, [x13, x21])";
         bb_statements :=
           [BStmt_Assert
              (BExp_Aligned Bit64 3
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R13" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R21" (BType_Imm Bit64)))));
            BStmt_Assign (BVar "R14" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R13" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R21" (BType_Imm Bit64))))
                 BEnd_LittleEndian Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 8w)))|>;
       <|bb_label := BL_Address_HC (Imm64 8w) "EB1601DF (cmp x14, x22)";
         bb_statements :=
           [BStmt_Assign (BVar "ProcState_C" BType_Bool)
              (BExp_nzcv_SUB_C (BExp_Den (BVar "R14" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R22" (BType_Imm Bit64))));
            BStmt_Assign (BVar "ProcState_N" BType_Bool)
              (BExp_nzcv_SUB_N Bit64
                 (BExp_Den (BVar "R14" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R22" (BType_Imm Bit64))));
            BStmt_Assign (BVar "ProcState_V" BType_Bool)
              (BExp_nzcv_SUB_V Bit64
                 (BExp_Den (BVar "R14" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R22" (BType_Imm Bit64))));
            BStmt_Assign (BVar "ProcState_Z" BType_Bool)
              (BExp_nzcv_SUB_Z (BExp_Den (BVar "R14" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R22" (BType_Imm Bit64))))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 12w)))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 12w)
             "54000102 (b.cs 2c <.text+0x2c>  // b.hs, b.nlast)";
         bb_statements := [];
         bb_last_statement :=
           BStmt_CJmp (BExp_Den (BVar "ProcState_C" BType_Bool))
             (BLE_Label (BL_Address (Imm64 44w)))
             (BLE_Label (BL_Address (Imm64 16w)))|>;
       <|bb_label := BL_Address_HC (Imm64 16w) "F82468AE (str x14, [x5, x4])";
         bb_statements :=
           [BStmt_Assert
              (BExp_Aligned Bit64 3
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R5" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R4" (BType_Imm Bit64)))));
            BStmt_Assert
              (BExp_unchanged_mem_interval_distinct Bit64 0 80
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R5" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R4" (BType_Imm Bit64)))) 8);
            BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
              (BExp_Store (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R5" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R4" (BType_Imm Bit64))))
                 BEnd_LittleEndian (BExp_Den (BVar "R14" (BType_Imm Bit64))))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 20w)))|>;
       <|bb_label := BL_Address_HC (Imm64 20w) "EB09005F (cmp x2, x9)";
         bb_statements :=
           [BStmt_Assign (BVar "ProcState_C" BType_Bool)
              (BExp_nzcv_SUB_C (BExp_Den (BVar "R2" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R9" (BType_Imm Bit64))));
            BStmt_Assign (BVar "ProcState_N" BType_Bool)
              (BExp_nzcv_SUB_N Bit64 (BExp_Den (BVar "R2" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R9" (BType_Imm Bit64))));
            BStmt_Assign (BVar "ProcState_V" BType_Bool)
              (BExp_nzcv_SUB_V Bit64 (BExp_Den (BVar "R2" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R9" (BType_Imm Bit64))));
            BStmt_Assign (BVar "ProcState_Z" BType_Bool)
              (BExp_nzcv_SUB_Z (BExp_Den (BVar "R2" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R9" (BType_Imm Bit64))))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 24w)))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 24w)
             "5400006B (b.lt 24 <.text+0x24>  // b.tstop)";
         bb_statements := [];
         bb_last_statement :=
           BStmt_CJmp
             (BExp_BinPred BIExp_Equal
                (BExp_Den (BVar "ProcState_N" BType_Bool))
                (BExp_Den (BVar "ProcState_V" BType_Bool)))
             (BLE_Label (BL_Address (Imm64 28w)))
             (BLE_Label (BL_Address (Imm64 36w)))|>;
       <|bb_label := BL_Address_HC (Imm64 28w) "D378DDCE (lsl x14, x14, #8)";
         bb_statements :=
           [BStmt_Assign (BVar "R14" (BType_Imm Bit64))
              (BExp_BinExp BIExp_And (BExp_Const (Imm64 0xFFFFFFFFFFFFFFFFw))
                 (BExp_BinExp BIExp_LeftShift
                    (BExp_Den (BVar "R14" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 8w))))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 32w)))|>;
       <|bb_label := BL_Address_HC (Imm64 32w) "14000002 (b 28 <.text+0x28>)";
         bb_statements := [];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 40w)))|>;
       <|bb_label := BL_Address_HC (Imm64 36w) "F86468AE (ldr x14, [x5, x4])";
         bb_statements :=
           [BStmt_Assert
              (BExp_Aligned Bit64 3
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R5" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R4" (BType_Imm Bit64)))));
            BStmt_Assign (BVar "R14" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R5" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R4" (BType_Imm Bit64))))
                 BEnd_LittleEndian Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 40w)))|>;
       <|bb_label := BL_Address_HC (Imm64 40w) "D65F03C0 (ret)";
         bb_statements := [];
         bb_last_statement :=
           BStmt_Jmp (BLE_Exp (BExp_Den (BVar "R30" (BType_Imm Bit64))))|>;
       <|bb_label := BL_Address_HC (Imm64 44w) "EB11003F (cmp x1, x17)";
         bb_statements :=
           [BStmt_Assign (BVar "ProcState_C" BType_Bool)
              (BExp_nzcv_SUB_C (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R17" (BType_Imm Bit64))));
            BStmt_Assign (BVar "ProcState_N" BType_Bool)
              (BExp_nzcv_SUB_N Bit64 (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R17" (BType_Imm Bit64))));
            BStmt_Assign (BVar "ProcState_V" BType_Bool)
              (BExp_nzcv_SUB_V Bit64 (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R17" (BType_Imm Bit64))));
            BStmt_Assign (BVar "ProcState_Z" BType_Bool)
              (BExp_nzcv_SUB_Z (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R17" (BType_Imm Bit64))))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 48w)))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 48w)
             "54000060 (b.eq 3c <.text+0x3c>  // b.none)";
         bb_statements := [];
         bb_last_statement :=
           BStmt_CJmp (BExp_Den (BVar "ProcState_Z" BType_Bool))
             (BLE_Label (BL_Address (Imm64 60w)))
             (BLE_Label (BL_Address (Imm64 52w)))|>;
       <|bb_label := BL_Address_HC (Imm64 52w) "8B020035 (add x21, x1, x2)";
         bb_statements :=
           [BStmt_Assign (BVar "R21" (BType_Imm Bit64))
              (BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R2" (BType_Imm Bit64))))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 56w)))|>;
       <|bb_label := BL_Address_HC (Imm64 56w) "14000003 (b 44 <.text+0x44>)";
         bb_statements := [];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 68w)))|>;
       <|bb_label := BL_Address_HC (Imm64 60w) "D503201F (nop)";
         bb_statements := [];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 64w)))|>;
       <|bb_label := BL_Address_HC (Imm64 64w) "14000002 (b 28 <.text+0x28>)";
         bb_statements := [];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 72w)))|>;
       <|bb_label := BL_Address_HC (Imm64 68w) "D65F03C0 (ret)";
         bb_statements := [];
         bb_last_statement :=
           BStmt_Jmp (BLE_Exp (BExp_Den (BVar "R30" (BType_Imm Bit64))))|>;
       <|bb_label := BL_Address_HC (Imm64 72w) "F94002A2 (ldr x2, [x21])";
         bb_statements :=
           [BStmt_Assert
              (BExp_Aligned Bit64 3 (BExp_Den (BVar "R21" (BType_Imm Bit64))));
            BStmt_Assign (BVar "R2" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_Den (BVar "R21" (BType_Imm Bit64))) BEnd_LittleEndian
                 Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 76w)))|>;
       <|bb_label := BL_Address_HC (Imm64 76w) "D65F03C0 (ret)";
         bb_statements := [];
         bb_last_statement :=
           BStmt_Jmp (BLE_Exp (BExp_Den (BVar "R30" (BType_Imm Bit64))))|>]
:bir_val_t bir_program_t
``;

val prog_13_mem_address_pc = ``
F
``;

val prog_13_cache_tag_index = ``
F
``;

val prog_13_cache_tag_only = ``
F
``;

val prog_13_cache_index_only = ``
F
``;

val prog_13_cache_tag_index_part = ``
F
``;

val prog_13_cache_tag_index_part_page = ``
F
``;

val prog_13_cache_speculation = ``
BirProgram
      [<|bb_label := BL_Address (Imm64 0w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w)) [BExp_Const (Imm64 0w)] HD;
            BStmt_Assign (BVar "R21" (BType_Imm Bit64))
              (BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R2" (BType_Imm Bit64))))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 4w)))|>;
       <|bb_label := BL_Address (Imm64 4w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w)) [BExp_Const (Imm64 4w)] HD;
            BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R13" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R21" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 0x80100000w))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R13" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R21" (BType_Imm Bit64)))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R13" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R21" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 0x801FFF80w))));
            BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "R13" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R21" (BType_Imm Bit64)))] HD;
            BStmt_Assign (BVar "R14" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R13" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R21" (BType_Imm Bit64))))
                 BEnd_LittleEndian Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 8w)))|>;
       <|bb_label := BL_Address (Imm64 8w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w)) [BExp_Const (Imm64 8w)] HD;
            BStmt_Assign (BVar "ProcState_C" (BType_Imm Bit1))
              (BExp_BinPred BIExp_LessOrEqual
                 (BExp_Den (BVar "R22" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R14" (BType_Imm Bit64))));
            BStmt_Assign (BVar "ProcState_N" (BType_Imm Bit1))
              (BExp_BinPred BIExp_SignedLessThan
                 (BExp_BinExp BIExp_Minus
                    (BExp_Den (BVar "R14" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R22" (BType_Imm Bit64))))
                 (BExp_Const (Imm64 0w)));
            BStmt_Assign (BVar "ProcState_V" (BType_Imm Bit1))
              (BExp_BinPred BIExp_Equal
                 (BExp_BinPred BIExp_SignedLessThan
                    (BExp_BinExp BIExp_Minus
                       (BExp_Den (BVar "R14" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R22" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 0w)))
                 (BExp_BinPred BIExp_SignedLessOrEqual
                    (BExp_Den (BVar "R22" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R14" (BType_Imm Bit64)))));
            BStmt_Assign (BVar "ProcState_Z" (BType_Imm Bit1))
              (BExp_BinPred BIExp_Equal
                 (BExp_Den (BVar "R14" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R22" (BType_Imm Bit64))))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "12*"))|>;
       <|bb_label := BL_Address (Imm64 12w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w)) [BExp_Const (Imm64 12w)]
              HD];
         bb_last_statement :=
           BStmt_CJmp (BExp_Den (BVar "ProcState_C" (BType_Imm Bit1)))
             (BLE_Label (BL_Address (Imm64 44w)))
             (BLE_Label (BL_Address (Imm64 16w)))|>;
       <|bb_label := BL_Address (Imm64 16w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w)) [BExp_Const (Imm64 16w)]
              HD;
            BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R5" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R4" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R5" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R4" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 0xFFFFFFFFFFFFFFF7w)))
                 (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_Or
                       (BExp_BinPred BIExp_LessThan (BExp_Const (Imm64 0w))
                          (BExp_BinExp BIExp_Plus
                             (BExp_Den (BVar "R5" (BType_Imm Bit64)))
                             (BExp_Den (BVar "R4" (BType_Imm Bit64)))))
                       (BExp_BinPred BIExp_LessOrEqual
                          (BExp_BinExp BIExp_Plus (BExp_Const (Imm64 8w))
                             (BExp_BinExp BIExp_Plus
                                (BExp_Den (BVar "R5" (BType_Imm Bit64)))
                                (BExp_Den (BVar "R4" (BType_Imm Bit64)))))
                          (BExp_Const (Imm64 0w))))
                    (BExp_BinExp BIExp_Or
                       (BExp_BinPred BIExp_LessThan
                          (BExp_BinExp BIExp_Plus
                             (BExp_Den (BVar "R5" (BType_Imm Bit64)))
                             (BExp_Den (BVar "R4" (BType_Imm Bit64))))
                          (BExp_Const (Imm64 0w)))
                       (BExp_BinPred BIExp_LessOrEqual
                          (BExp_Const (Imm64 80w))
                          (BExp_BinExp BIExp_Plus
                             (BExp_Den (BVar "R5" (BType_Imm Bit64)))
                             (BExp_Den (BVar "R4" (BType_Imm Bit64))))))));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 0x80100000w))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R5" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R4" (BType_Imm Bit64)))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R5" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R4" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 0x801FFF80w))));
            BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "R5" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R4" (BType_Imm Bit64)))] HD;
            BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
              (BExp_Store (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R5" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R4" (BType_Imm Bit64))))
                 BEnd_LittleEndian (BExp_Den (BVar "R14" (BType_Imm Bit64))))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 20w)))|>;
       <|bb_label := BL_Address (Imm64 20w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w)) [BExp_Const (Imm64 20w)]
              HD;
            BStmt_Assign (BVar "ProcState_C" (BType_Imm Bit1))
              (BExp_BinPred BIExp_LessOrEqual
                 (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R2" (BType_Imm Bit64))));
            BStmt_Assign (BVar "ProcState_N" (BType_Imm Bit1))
              (BExp_BinPred BIExp_SignedLessThan
                 (BExp_BinExp BIExp_Minus
                    (BExp_Den (BVar "R2" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R9" (BType_Imm Bit64))))
                 (BExp_Const (Imm64 0w)));
            BStmt_Assign (BVar "ProcState_V" (BType_Imm Bit1))
              (BExp_BinPred BIExp_Equal
                 (BExp_BinPred BIExp_SignedLessThan
                    (BExp_BinExp BIExp_Minus
                       (BExp_Den (BVar "R2" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R9" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 0w)))
                 (BExp_BinPred BIExp_SignedLessOrEqual
                    (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R2" (BType_Imm Bit64)))));
            BStmt_Assign (BVar "ProcState_Z" (BType_Imm Bit1))
              (BExp_BinPred BIExp_Equal
                 (BExp_Den (BVar "R2" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R9" (BType_Imm Bit64))))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 24w)))|>;
       <|bb_label := BL_Address (Imm64 24w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w)) [BExp_Const (Imm64 24w)]
              HD];
         bb_last_statement :=
           BStmt_CJmp
             (BExp_BinPred BIExp_Equal
                (BExp_Den (BVar "ProcState_N" (BType_Imm Bit1)))
                (BExp_Den (BVar "ProcState_V" (BType_Imm Bit1))))
             (BLE_Label (BL_Address (Imm64 28w)))
             (BLE_Label (BL_Address (Imm64 36w)))|>;
       <|bb_label := BL_Address (Imm64 28w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w)) [BExp_Const (Imm64 28w)]
              HD;
            BStmt_Assign (BVar "R14" (BType_Imm Bit64))
              (BExp_BinExp BIExp_And (BExp_Const (Imm64 0xFFFFFFFFFFFFFFFFw))
                 (BExp_BinExp BIExp_LeftShift
                    (BExp_Den (BVar "R14" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 8w))))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 32w)))|>;
       <|bb_label := BL_Address (Imm64 32w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w)) [BExp_Const (Imm64 32w)]
              HD];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 40w)))|>;
       <|bb_label := BL_Address (Imm64 36w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w)) [BExp_Const (Imm64 36w)]
              HD;
            BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R5" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R4" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 0x80100000w))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R5" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R4" (BType_Imm Bit64)))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R5" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R4" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 0x801FFF80w))));
            BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "R5" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R4" (BType_Imm Bit64)))] HD;
            BStmt_Assign (BVar "R14" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R5" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R4" (BType_Imm Bit64))))
                 BEnd_LittleEndian Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 40w)))|>;
       <|bb_label := BL_Address (Imm64 40w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w)) [BExp_Const (Imm64 40w)]
              HD];
         bb_last_statement :=
           BStmt_Jmp (BLE_Exp (BExp_Den (BVar "R30" (BType_Imm Bit64))))|>;
       <|bb_label := BL_Address (Imm64 44w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w)) [BExp_Const (Imm64 44w)]
              HD;
            BStmt_Assign (BVar "ProcState_C" (BType_Imm Bit1))
              (BExp_BinPred BIExp_LessOrEqual
                 (BExp_Den (BVar "R17" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R1" (BType_Imm Bit64))));
            BStmt_Assign (BVar "ProcState_N" (BType_Imm Bit1))
              (BExp_BinPred BIExp_SignedLessThan
                 (BExp_BinExp BIExp_Minus
                    (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R17" (BType_Imm Bit64))))
                 (BExp_Const (Imm64 0w)));
            BStmt_Assign (BVar "ProcState_V" (BType_Imm Bit1))
              (BExp_BinPred BIExp_Equal
                 (BExp_BinPred BIExp_SignedLessThan
                    (BExp_BinExp BIExp_Minus
                       (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R17" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 0w)))
                 (BExp_BinPred BIExp_SignedLessOrEqual
                    (BExp_Den (BVar "R17" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R1" (BType_Imm Bit64)))));
            BStmt_Assign (BVar "ProcState_Z" (BType_Imm Bit1))
              (BExp_BinPred BIExp_Equal
                 (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R17" (BType_Imm Bit64))))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 48w)))|>;
       <|bb_label := BL_Address (Imm64 48w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w)) [BExp_Const (Imm64 48w)]
              HD];
         bb_last_statement :=
           BStmt_CJmp (BExp_Den (BVar "ProcState_Z" (BType_Imm Bit1)))
             (BLE_Label (BL_Address (Imm64 60w)))
             (BLE_Label (BL_Address (Imm64 52w)))|>;
       <|bb_label := BL_Address (Imm64 52w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w)) [BExp_Const (Imm64 52w)]
              HD;
            BStmt_Assign (BVar "R21" (BType_Imm Bit64))
              (BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R2" (BType_Imm Bit64))))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 56w)))|>;
       <|bb_label := BL_Address (Imm64 56w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w)) [BExp_Const (Imm64 56w)]
              HD];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 68w)))|>;
       <|bb_label := BL_Address (Imm64 60w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w)) [BExp_Const (Imm64 60w)]
              HD];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 64w)))|>;
       <|bb_label := BL_Address (Imm64 64w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w)) [BExp_Const (Imm64 64w)]
              HD];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 72w)))|>;
       <|bb_label := BL_Address (Imm64 68w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w)) [BExp_Const (Imm64 68w)]
              HD];
         bb_last_statement :=
           BStmt_Jmp (BLE_Exp (BExp_Den (BVar "R30" (BType_Imm Bit64))))|>;
       <|bb_label := BL_Address (Imm64 72w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w)) [BExp_Const (Imm64 72w)]
              HD;
            BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_Den (BVar "R21" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 0x80100000w))
                    (BExp_Den (BVar "R21" (BType_Imm Bit64))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_Den (BVar "R21" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 0x801FFF80w))));
            BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_Den (BVar "R21" (BType_Imm Bit64))] HD;
            BStmt_Assign (BVar "R2" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_Den (BVar "R21" (BType_Imm Bit64))) BEnd_LittleEndian
                 Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 76w)))|>;
       <|bb_label := BL_Address (Imm64 76w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w)) [BExp_Const (Imm64 76w)]
              HD];
         bb_last_statement :=
           BStmt_Jmp (BLE_Exp (BExp_Den (BVar "R30" (BType_Imm Bit64))))|>;
       <|bb_label := BL_Label "12*";
         bb_statements :=
           [BStmt_Assert
              (BExp_BinPred BIExp_Equal (BExp_Const (Imm64 41w))
                 (BExp_Const (Imm64 41w)));
            BStmt_Assign (BVar "ProcState_C*" (BType_Imm Bit1))
              (BExp_Den (BVar "ProcState_C" (BType_Imm Bit1)));
            BStmt_Assign (BVar "R17*" (BType_Imm Bit64))
              (BExp_Den (BVar "R17" (BType_Imm Bit64)));
            BStmt_Assign (BVar "R1*" (BType_Imm Bit64))
              (BExp_Den (BVar "R1" (BType_Imm Bit64)));
            BStmt_Assign (BVar "ProcState_Z*" (BType_Imm Bit1))
              (BExp_Den (BVar "ProcState_Z" (BType_Imm Bit1)));
            BStmt_Assign (BVar "R21*" (BType_Imm Bit64))
              (BExp_Den (BVar "R21" (BType_Imm Bit64)));
            BStmt_Assign (BVar "MEM*" (BType_Mem Bit64 Bit8))
              (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)));
            BStmt_Assign (BVar "R2*" (BType_Imm Bit64))
              (BExp_Den (BVar "R2" (BType_Imm Bit64)));
            BStmt_Assign (BVar "R5*" (BType_Imm Bit64))
              (BExp_Den (BVar "R5" (BType_Imm Bit64)));
            BStmt_Assign (BVar "R4*" (BType_Imm Bit64))
              (BExp_Den (BVar "R4" (BType_Imm Bit64)));
            BStmt_Assign (BVar "R14*" (BType_Imm Bit64))
              (BExp_Den (BVar "R14" (BType_Imm Bit64)));
            BStmt_Assign (BVar "R9*" (BType_Imm Bit64))
              (BExp_Den (BVar "R9" (BType_Imm Bit64)));
            BStmt_Assign (BVar "ProcState_N*" (BType_Imm Bit1))
              (BExp_Den (BVar "ProcState_N" (BType_Imm Bit1)));
            BStmt_Assign (BVar "ProcState_V*" (BType_Imm Bit1))
              (BExp_Den (BVar "ProcState_V" (BType_Imm Bit1)))];
         bb_last_statement :=
           BStmt_CJmp
             (BExp_UnaryExp BIExp_Not
                (BExp_Den (BVar "ProcState_C*" (BType_Imm Bit1))))
             (BLE_Label (BL_Label "44*")) (BLE_Label (BL_Label "16*"))|>;
       <|bb_label := BL_Label "44*";
         bb_statements :=
           [BStmt_Assign (BVar "ProcState_C*" (BType_Imm Bit1))
              (BExp_BinPred BIExp_LessOrEqual
                 (BExp_Den (BVar "R17*" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R1*" (BType_Imm Bit64))));
            BStmt_Assign (BVar "ProcState_N*" (BType_Imm Bit1))
              (BExp_BinPred BIExp_SignedLessThan
                 (BExp_BinExp BIExp_Minus
                    (BExp_Den (BVar "R1*" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R17*" (BType_Imm Bit64))))
                 (BExp_Const (Imm64 0w)));
            BStmt_Assign (BVar "ProcState_V*" (BType_Imm Bit1))
              (BExp_BinPred BIExp_Equal
                 (BExp_BinPred BIExp_SignedLessThan
                    (BExp_BinExp BIExp_Minus
                       (BExp_Den (BVar "R1*" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R17*" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 0w)))
                 (BExp_BinPred BIExp_SignedLessOrEqual
                    (BExp_Den (BVar "R17*" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R1*" (BType_Imm Bit64)))));
            BStmt_Assign (BVar "ProcState_Z*" (BType_Imm Bit1))
              (BExp_BinPred BIExp_Equal
                 (BExp_Den (BVar "R1*" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R17*" (BType_Imm Bit64))))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "48*"))|>;
       <|bb_label := BL_Label "48*"; bb_statements := [];
         bb_last_statement :=
           BStmt_CJmp
             (BExp_UnaryExp BIExp_Not
                (BExp_Den (BVar "ProcState_Z*" (BType_Imm Bit1))))
             (BLE_Label (BL_Label "60*")) (BLE_Label (BL_Label "52*"))|>;
       <|bb_label := BL_Label "60*"; bb_statements := [];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "64*"))|>;
       <|bb_label := BL_Label "64*"; bb_statements := [];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "72*"))|>;
       <|bb_label := BL_Label "72*";
         bb_statements :=
           [BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_Den (BVar "R21*" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 0x80100000w))
                    (BExp_Den (BVar "R21*" (BType_Imm Bit64))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_Den (BVar "R21*" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 0x801FFF80w))));
            BStmt_Observe 1 (BExp_Const (Imm1 1w))
              [BExp_Den (BVar "R21*" (BType_Imm Bit64))] HD;
            BStmt_Assign (BVar "R2*" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM*" (BType_Mem Bit64 Bit8)))
                 (BExp_Den (BVar "R21*" (BType_Imm Bit64))) BEnd_LittleEndian
                 Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "76*"))|>;
       <|bb_label := BL_Label "76*"; bb_statements := [];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 12w)))|>;
       <|bb_label := BL_Label "52*";
         bb_statements :=
           [BStmt_Assign (BVar "R21*" (BType_Imm Bit64))
              (BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "R1*" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R2*" (BType_Imm Bit64))))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "56*"))|>;
       <|bb_label := BL_Label "56*"; bb_statements := [];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "68*"))|>;
       <|bb_label := BL_Label "68*"; bb_statements := [];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 12w)))|>;
       <|bb_label := BL_Label "16*";
         bb_statements :=
           [BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R5*" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R4*" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R5*" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R4*" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 0xFFFFFFFFFFFFFFF7w)))
                 (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_Or
                       (BExp_BinPred BIExp_LessThan (BExp_Const (Imm64 0w))
                          (BExp_BinExp BIExp_Plus
                             (BExp_Den (BVar "R5*" (BType_Imm Bit64)))
                             (BExp_Den (BVar "R4*" (BType_Imm Bit64)))))
                       (BExp_BinPred BIExp_LessOrEqual
                          (BExp_BinExp BIExp_Plus (BExp_Const (Imm64 8w))
                             (BExp_BinExp BIExp_Plus
                                (BExp_Den (BVar "R5*" (BType_Imm Bit64)))
                                (BExp_Den (BVar "R4*" (BType_Imm Bit64)))))
                          (BExp_Const (Imm64 0w))))
                    (BExp_BinExp BIExp_Or
                       (BExp_BinPred BIExp_LessThan
                          (BExp_BinExp BIExp_Plus
                             (BExp_Den (BVar "R5*" (BType_Imm Bit64)))
                             (BExp_Den (BVar "R4*" (BType_Imm Bit64))))
                          (BExp_Const (Imm64 0w)))
                       (BExp_BinPred BIExp_LessOrEqual
                          (BExp_Const (Imm64 80w))
                          (BExp_BinExp BIExp_Plus
                             (BExp_Den (BVar "R5*" (BType_Imm Bit64)))
                             (BExp_Den (BVar "R4*" (BType_Imm Bit64))))))));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 0x80100000w))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R5*" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R4*" (BType_Imm Bit64)))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R5*" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R4*" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 0x801FFF80w))));
            BStmt_Observe 1 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "R5*" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R4*" (BType_Imm Bit64)))] HD;
            BStmt_Assign (BVar "MEM*" (BType_Mem Bit64 Bit8))
              (BExp_Store (BExp_Den (BVar "MEM*" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R5*" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R4*" (BType_Imm Bit64))))
                 BEnd_LittleEndian (BExp_Den (BVar "R14*" (BType_Imm Bit64))))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "20*"))|>;
       <|bb_label := BL_Label "20*";
         bb_statements :=
           [BStmt_Assign (BVar "ProcState_C*" (BType_Imm Bit1))
              (BExp_BinPred BIExp_LessOrEqual
                 (BExp_Den (BVar "R9*" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R2*" (BType_Imm Bit64))));
            BStmt_Assign (BVar "ProcState_N*" (BType_Imm Bit1))
              (BExp_BinPred BIExp_SignedLessThan
                 (BExp_BinExp BIExp_Minus
                    (BExp_Den (BVar "R2*" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R9*" (BType_Imm Bit64))))
                 (BExp_Const (Imm64 0w)));
            BStmt_Assign (BVar "ProcState_V*" (BType_Imm Bit1))
              (BExp_BinPred BIExp_Equal
                 (BExp_BinPred BIExp_SignedLessThan
                    (BExp_BinExp BIExp_Minus
                       (BExp_Den (BVar "R2*" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R9*" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 0w)))
                 (BExp_BinPred BIExp_SignedLessOrEqual
                    (BExp_Den (BVar "R9*" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R2*" (BType_Imm Bit64)))));
            BStmt_Assign (BVar "ProcState_Z*" (BType_Imm Bit1))
              (BExp_BinPred BIExp_Equal
                 (BExp_Den (BVar "R2*" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R9*" (BType_Imm Bit64))))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "24*"))|>;
       <|bb_label := BL_Label "24*"; bb_statements := [];
         bb_last_statement :=
           BStmt_CJmp
             (BExp_UnaryExp BIExp_Not
                (BExp_BinPred BIExp_Equal
                   (BExp_Den (BVar "ProcState_N*" (BType_Imm Bit1)))
                   (BExp_Den (BVar "ProcState_V*" (BType_Imm Bit1)))))
             (BLE_Label (BL_Label "28*")) (BLE_Label (BL_Label "36*"))|>;
       <|bb_label := BL_Label "28*";
         bb_statements :=
           [BStmt_Assign (BVar "R14*" (BType_Imm Bit64))
              (BExp_BinExp BIExp_And (BExp_Const (Imm64 0xFFFFFFFFFFFFFFFFw))
                 (BExp_BinExp BIExp_LeftShift
                    (BExp_Den (BVar "R14*" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 8w))))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "32*"))|>;
       <|bb_label := BL_Label "32*"; bb_statements := [];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "40*"))|>;
       <|bb_label := BL_Label "40*"; bb_statements := [];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 12w)))|>;
       <|bb_label := BL_Label "36*";
         bb_statements :=
           [BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R5*" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R4*" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 0x80100000w))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R5*" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R4*" (BType_Imm Bit64)))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R5*" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R4*" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 0x801FFF80w))));
            BStmt_Observe 1 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "R5*" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R4*" (BType_Imm Bit64)))] HD;
            BStmt_Assign (BVar "R14*" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM*" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R5*" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R4*" (BType_Imm Bit64))))
                 BEnd_LittleEndian Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Label "40*"))|>]
:bir_val_t bir_program_t
``;

val prog_13_cache_speculation_first =``
F
``;

val prog_13_test =
  ("prog_13 - nested branch", prog_13,
     (prog_13_mem_address_pc,
      ``F``,
      prog_13_cache_tag_index,
      prog_13_cache_tag_only,
      prog_13_cache_index_only,
      prog_13_cache_tag_index_part,
      prog_13_cache_tag_index_part_page,
      prog_13_cache_speculation,
      prog_13_cache_speculation_first)
  );
