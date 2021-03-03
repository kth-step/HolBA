(* ========================= prog_2 - branch and merge (spectre) =========================== *)

(*
=================================
	ldr x26, [x14,x24]
	ldr x15, [x17, #0]
	cmp x14, x15
	b.eq #0xC
	ldr x10, [x26, #76]
	b #0x8
	ldr x14, [x9]
=================================
*)

val prog_2 = ``
BirProgram
       [<|bb_label :=
            BL_Address_HC (Imm64 0w) "F87869DA (ldr x26, [x14, x24])";
          bb_statements :=
            [BStmt_Assert
               (BExp_Aligned Bit64 3
                  (BExp_BinExp BIExp_Plus
                     (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                     (BExp_Den (BVar "R14" (BType_Imm Bit64)))));
             BStmt_Assign (BVar "R26" (BType_Imm Bit64))
               (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                  (BExp_BinExp BIExp_Plus
                     (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                     (BExp_Den (BVar "R14" (BType_Imm Bit64))))
                  BEnd_LittleEndian Bit64)];
          bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 4w)))|>;
        <|bb_label := BL_Address_HC (Imm64 4w) "F940022F (ldr x15, [x17])";
          bb_statements :=
            [BStmt_Assert
               (BExp_Aligned Bit64 3
                  (BExp_Den (BVar "R17" (BType_Imm Bit64))));
             BStmt_Assign (BVar "R15" (BType_Imm Bit64))
               (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                  (BExp_Den (BVar "R17" (BType_Imm Bit64))) BEnd_LittleEndian
                  Bit64)];
          bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 8w)))|>;
        <|bb_label := BL_Address_HC (Imm64 8w) "EB0F01DF (cmp x14, x15)";
          bb_statements :=
            [BStmt_Assign (BVar "ProcState_C" BType_Bool)
               (BExp_nzcv_SUB_C (BExp_Den (BVar "R14" (BType_Imm Bit64)))
                  (BExp_Den (BVar "R15" (BType_Imm Bit64))));
             BStmt_Assign (BVar "ProcState_N" BType_Bool)
               (BExp_nzcv_SUB_N Bit64
                  (BExp_Den (BVar "R14" (BType_Imm Bit64)))
                  (BExp_Den (BVar "R15" (BType_Imm Bit64))));
             BStmt_Assign (BVar "ProcState_V" BType_Bool)
               (BExp_nzcv_SUB_V Bit64
                  (BExp_Den (BVar "R14" (BType_Imm Bit64)))
                  (BExp_Den (BVar "R15" (BType_Imm Bit64))));
             BStmt_Assign (BVar "ProcState_Z" BType_Bool)
               (BExp_nzcv_SUB_Z (BExp_Den (BVar "R14" (BType_Imm Bit64)))
                  (BExp_Den (BVar "R15" (BType_Imm Bit64))))];
          bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 12w)))|>;
        <|bb_label :=
            BL_Address_HC (Imm64 12w)
              "54000060 (b.eq 18 <.text+0x18>  // b.none)";
          bb_statements := [];
          bb_last_statement :=
            BStmt_CJmp (BExp_Den (BVar "ProcState_Z" BType_Bool))
              (BLE_Label (BL_Address (Imm64 24w)))
              (BLE_Label (BL_Address (Imm64 16w)))|>;
        <|bb_label :=
            BL_Address_HC (Imm64 16w) "F844C34A (ldur x10, [x26, #76])";
          bb_statements :=
            [BStmt_Assert
               (BExp_Aligned Bit64 3
                  (BExp_BinExp BIExp_Plus
                     (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                     (BExp_Const (Imm64 4w))));
             BStmt_Assign (BVar "R10" (BType_Imm Bit64))
               (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                  (BExp_BinExp BIExp_Plus
                     (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                     (BExp_Const (Imm64 76w))) BEnd_LittleEndian Bit64)];
          bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 20w)))|>;
        <|bb_label :=
            BL_Address_HC (Imm64 20w) "14000002 (b 1c <.text+0x1c>)";
          bb_statements := [];
          bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 28w)))|>;
        <|bb_label := BL_Address_HC (Imm64 24w) "F940012E (ldr x14, [x9])";
          bb_statements :=
            [BStmt_Assert
               (BExp_Aligned Bit64 3 (BExp_Den (BVar "R9" (BType_Imm Bit64))));
             BStmt_Assign (BVar "R14" (BType_Imm Bit64))
               (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                  (BExp_Den (BVar "R9" (BType_Imm Bit64))) BEnd_LittleEndian
                  Bit64)];
          bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 28w)))|>;
        <|bb_label := BL_Address (Imm64 28w); bb_statements := [];
          bb_last_statement := BStmt_Halt (BExp_Const (Imm32 0w))|>]
:bir_val_t bir_program_t
``;

val prog_2_mem_address_pc = ``
BirProgram
      [<|bb_label := BL_Address (Imm64 0w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w)) [BExp_Const (Imm64 0w)] HD;
            BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R14" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 4291559424w))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R14" (BType_Imm Bit64)))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R14" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 4291624832w))));
            BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R14" (BType_Imm Bit64)))] HD;
            BStmt_Assign (BVar "R26" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R14" (BType_Imm Bit64))))
                 BEnd_LittleEndian Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 4w)))|>;
       <|bb_label := BL_Address (Imm64 4w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w)) [BExp_Const (Imm64 4w)] HD;
            BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_Den (BVar "R17" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 4291559424w))
                    (BExp_Den (BVar "R17" (BType_Imm Bit64))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_Den (BVar "R17" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 4291624832w))));
            BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_Den (BVar "R17" (BType_Imm Bit64))] HD;
            BStmt_Assign (BVar "R15" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_Den (BVar "R17" (BType_Imm Bit64))) BEnd_LittleEndian
                 Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 8w)))|>;
       <|bb_label := BL_Address (Imm64 8w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w)) [BExp_Const (Imm64 8w)] HD;
            BStmt_Assign (BVar "ProcState_C" (BType_Imm Bit1))
              (BExp_BinPred BIExp_LessOrEqual
                 (BExp_Den (BVar "R15" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R14" (BType_Imm Bit64))));
            BStmt_Assign (BVar "ProcState_N" (BType_Imm Bit1))
              (BExp_BinPred BIExp_SignedLessThan
                 (BExp_BinExp BIExp_Minus
                    (BExp_Den (BVar "R14" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R15" (BType_Imm Bit64))))
                 (BExp_Const (Imm64 0w)));
            BStmt_Assign (BVar "ProcState_V" (BType_Imm Bit1))
              (BExp_BinPred BIExp_Equal
                 (BExp_BinPred BIExp_SignedLessThan
                    (BExp_BinExp BIExp_Minus
                       (BExp_Den (BVar "R14" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R15" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 0w)))
                 (BExp_BinPred BIExp_SignedLessOrEqual
                    (BExp_Den (BVar "R15" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R14" (BType_Imm Bit64)))));
            BStmt_Assign (BVar "ProcState_Z" (BType_Imm Bit1))
              (BExp_BinPred BIExp_Equal
                 (BExp_Den (BVar "R14" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R15" (BType_Imm Bit64))))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 12w)))|>;
       <|bb_label := BL_Address (Imm64 12w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w)) [BExp_Const (Imm64 12w)]
              HD];
         bb_last_statement :=
           BStmt_CJmp (BExp_Den (BVar "ProcState_Z" (BType_Imm Bit1)))
             (BLE_Label (BL_Address (Imm64 24w)))
             (BLE_Label (BL_Address (Imm64 16w)))|>;
       <|bb_label := BL_Address (Imm64 16w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w)) [BExp_Const (Imm64 16w)]
              HD;
            BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 4w))) (BExp_Const (Imm64 7w)))
                 (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 4291559424w))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 76w))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 76w)))
                    (BExp_Const (Imm64 4291624832w))));
            BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 76w))] HD;
            BStmt_Assign (BVar "R10" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 76w))) BEnd_LittleEndian Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 20w)))|>;
       <|bb_label := BL_Address (Imm64 20w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w)) [BExp_Const (Imm64 20w)]
              HD];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 28w)))|>;
       <|bb_label := BL_Address (Imm64 24w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w)) [BExp_Const (Imm64 24w)]
              HD;
            BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 4291559424w))
                    (BExp_Den (BVar "R9" (BType_Imm Bit64))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 4291624832w))));
            BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_Den (BVar "R9" (BType_Imm Bit64))] HD;
            BStmt_Assign (BVar "R14" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_Den (BVar "R9" (BType_Imm Bit64))) BEnd_LittleEndian
                 Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 28w)))|>;
       <|bb_label := BL_Address (Imm64 28w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w)) [BExp_Const (Imm64 28w)]
              HD]; bb_last_statement := BStmt_Halt (BExp_Const (Imm32 0w))|>]
:bir_val_t bir_program_t
``;

val prog_2_cache_tag_index = ``
BirProgram
      [<|bb_label := BL_Address (Imm64 0w);
         bb_statements :=
           [BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R14" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 4291559424w))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R14" (BType_Imm Bit64)))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R14" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 4291624832w))));
            BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_RightShift
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R14" (BType_Imm Bit64))))
                 (BExp_Const (Imm64 6w))] HD;
            BStmt_Assign (BVar "R26" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R14" (BType_Imm Bit64))))
                 BEnd_LittleEndian Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 4w)))|>;
       <|bb_label := BL_Address (Imm64 4w);
         bb_statements :=
           [BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_Den (BVar "R17" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 4291559424w))
                    (BExp_Den (BVar "R17" (BType_Imm Bit64))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_Den (BVar "R17" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 4291624832w))));
            BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_RightShift
                 (BExp_Den (BVar "R17" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 6w))] HD;
            BStmt_Assign (BVar "R15" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_Den (BVar "R17" (BType_Imm Bit64))) BEnd_LittleEndian
                 Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 8w)))|>;
       <|bb_label := BL_Address (Imm64 8w);
         bb_statements :=
           [BStmt_Assign (BVar "ProcState_C" (BType_Imm Bit1))
              (BExp_BinPred BIExp_LessOrEqual
                 (BExp_Den (BVar "R15" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R14" (BType_Imm Bit64))));
            BStmt_Assign (BVar "ProcState_N" (BType_Imm Bit1))
              (BExp_BinPred BIExp_SignedLessThan
                 (BExp_BinExp BIExp_Minus
                    (BExp_Den (BVar "R14" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R15" (BType_Imm Bit64))))
                 (BExp_Const (Imm64 0w)));
            BStmt_Assign (BVar "ProcState_V" (BType_Imm Bit1))
              (BExp_BinPred BIExp_Equal
                 (BExp_BinPred BIExp_SignedLessThan
                    (BExp_BinExp BIExp_Minus
                       (BExp_Den (BVar "R14" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R15" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 0w)))
                 (BExp_BinPred BIExp_SignedLessOrEqual
                    (BExp_Den (BVar "R15" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R14" (BType_Imm Bit64)))));
            BStmt_Assign (BVar "ProcState_Z" (BType_Imm Bit1))
              (BExp_BinPred BIExp_Equal
                 (BExp_Den (BVar "R14" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R15" (BType_Imm Bit64))))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 12w)))|>;
       <|bb_label := BL_Address (Imm64 12w); bb_statements := [];
         bb_last_statement :=
           BStmt_CJmp (BExp_Den (BVar "ProcState_Z" (BType_Imm Bit1)))
             (BLE_Label (BL_Address (Imm64 24w)))
             (BLE_Label (BL_Address (Imm64 16w)))|>;
       <|bb_label := BL_Address (Imm64 16w);
         bb_statements :=
           [BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 4w))) (BExp_Const (Imm64 7w)))
                 (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 4291559424w))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 76w))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 76w)))
                    (BExp_Const (Imm64 4291624832w))));
            BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_RightShift
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 76w))) (BExp_Const (Imm64 6w))] HD;
            BStmt_Assign (BVar "R10" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 76w))) BEnd_LittleEndian Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 20w)))|>;
       <|bb_label := BL_Address (Imm64 20w); bb_statements := [];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 28w)))|>;
       <|bb_label := BL_Address (Imm64 24w);
         bb_statements :=
           [BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 4291559424w))
                    (BExp_Den (BVar "R9" (BType_Imm Bit64))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 4291624832w))));
            BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_RightShift
                 (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 6w))] HD;
            BStmt_Assign (BVar "R14" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_Den (BVar "R9" (BType_Imm Bit64))) BEnd_LittleEndian
                 Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 28w)))|>;
       <|bb_label := BL_Address (Imm64 28w); bb_statements := [];
         bb_last_statement := BStmt_Halt (BExp_Const (Imm32 0w))|>]
:bir_val_t bir_program_t
``;

val prog_2_cache_tag_only = ``
BirProgram
      [<|bb_label := BL_Address (Imm64 0w);
         bb_statements :=
           [BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R14" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 4291559424w))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R14" (BType_Imm Bit64)))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R14" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 4291624832w))));
            BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_RightShift
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R14" (BType_Imm Bit64))))
                 (BExp_Const (Imm64 13w))] HD;
            BStmt_Assign (BVar "R26" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R14" (BType_Imm Bit64))))
                 BEnd_LittleEndian Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 4w)))|>;
       <|bb_label := BL_Address (Imm64 4w);
         bb_statements :=
           [BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_Den (BVar "R17" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 4291559424w))
                    (BExp_Den (BVar "R17" (BType_Imm Bit64))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_Den (BVar "R17" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 4291624832w))));
            BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_RightShift
                 (BExp_Den (BVar "R17" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 13w))] HD;
            BStmt_Assign (BVar "R15" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_Den (BVar "R17" (BType_Imm Bit64))) BEnd_LittleEndian
                 Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 8w)))|>;
       <|bb_label := BL_Address (Imm64 8w);
         bb_statements :=
           [BStmt_Assign (BVar "ProcState_C" (BType_Imm Bit1))
              (BExp_BinPred BIExp_LessOrEqual
                 (BExp_Den (BVar "R15" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R14" (BType_Imm Bit64))));
            BStmt_Assign (BVar "ProcState_N" (BType_Imm Bit1))
              (BExp_BinPred BIExp_SignedLessThan
                 (BExp_BinExp BIExp_Minus
                    (BExp_Den (BVar "R14" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R15" (BType_Imm Bit64))))
                 (BExp_Const (Imm64 0w)));
            BStmt_Assign (BVar "ProcState_V" (BType_Imm Bit1))
              (BExp_BinPred BIExp_Equal
                 (BExp_BinPred BIExp_SignedLessThan
                    (BExp_BinExp BIExp_Minus
                       (BExp_Den (BVar "R14" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R15" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 0w)))
                 (BExp_BinPred BIExp_SignedLessOrEqual
                    (BExp_Den (BVar "R15" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R14" (BType_Imm Bit64)))));
            BStmt_Assign (BVar "ProcState_Z" (BType_Imm Bit1))
              (BExp_BinPred BIExp_Equal
                 (BExp_Den (BVar "R14" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R15" (BType_Imm Bit64))))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 12w)))|>;
       <|bb_label := BL_Address (Imm64 12w); bb_statements := [];
         bb_last_statement :=
           BStmt_CJmp (BExp_Den (BVar "ProcState_Z" (BType_Imm Bit1)))
             (BLE_Label (BL_Address (Imm64 24w)))
             (BLE_Label (BL_Address (Imm64 16w)))|>;
       <|bb_label := BL_Address (Imm64 16w);
         bb_statements :=
           [BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 4w))) (BExp_Const (Imm64 7w)))
                 (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 4291559424w))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 76w))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 76w)))
                    (BExp_Const (Imm64 4291624832w))));
            BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_RightShift
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 76w))) (BExp_Const (Imm64 13w))] HD;
            BStmt_Assign (BVar "R10" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 76w))) BEnd_LittleEndian Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 20w)))|>;
       <|bb_label := BL_Address (Imm64 20w); bb_statements := [];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 28w)))|>;
       <|bb_label := BL_Address (Imm64 24w);
         bb_statements :=
           [BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 4291559424w))
                    (BExp_Den (BVar "R9" (BType_Imm Bit64))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 4291624832w))));
            BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_RightShift
                 (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 13w))] HD;
            BStmt_Assign (BVar "R14" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_Den (BVar "R9" (BType_Imm Bit64))) BEnd_LittleEndian
                 Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 28w)))|>;
       <|bb_label := BL_Address (Imm64 28w); bb_statements := [];
         bb_last_statement := BStmt_Halt (BExp_Const (Imm32 0w))|>]
:bir_val_t bir_program_t
``;

val prog_2_cache_index_only = ``
BirProgram
      [<|bb_label := BL_Address (Imm64 0w);
         bb_statements :=
           [BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R14" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 4291559424w))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R14" (BType_Imm Bit64)))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R14" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 4291624832w))));
            BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_And (BExp_Const (Imm64 127w))
                 (BExp_BinExp BIExp_RightShift
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R14" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 6w)))] HD;
            BStmt_Assign (BVar "R26" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R14" (BType_Imm Bit64))))
                 BEnd_LittleEndian Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 4w)))|>;
       <|bb_label := BL_Address (Imm64 4w);
         bb_statements :=
           [BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_Den (BVar "R17" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 4291559424w))
                    (BExp_Den (BVar "R17" (BType_Imm Bit64))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_Den (BVar "R17" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 4291624832w))));
            BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_And (BExp_Const (Imm64 127w))
                 (BExp_BinExp BIExp_RightShift
                    (BExp_Den (BVar "R17" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 6w)))] HD;
            BStmt_Assign (BVar "R15" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_Den (BVar "R17" (BType_Imm Bit64))) BEnd_LittleEndian
                 Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 8w)))|>;
       <|bb_label := BL_Address (Imm64 8w);
         bb_statements :=
           [BStmt_Assign (BVar "ProcState_C" (BType_Imm Bit1))
              (BExp_BinPred BIExp_LessOrEqual
                 (BExp_Den (BVar "R15" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R14" (BType_Imm Bit64))));
            BStmt_Assign (BVar "ProcState_N" (BType_Imm Bit1))
              (BExp_BinPred BIExp_SignedLessThan
                 (BExp_BinExp BIExp_Minus
                    (BExp_Den (BVar "R14" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R15" (BType_Imm Bit64))))
                 (BExp_Const (Imm64 0w)));
            BStmt_Assign (BVar "ProcState_V" (BType_Imm Bit1))
              (BExp_BinPred BIExp_Equal
                 (BExp_BinPred BIExp_SignedLessThan
                    (BExp_BinExp BIExp_Minus
                       (BExp_Den (BVar "R14" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R15" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 0w)))
                 (BExp_BinPred BIExp_SignedLessOrEqual
                    (BExp_Den (BVar "R15" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R14" (BType_Imm Bit64)))));
            BStmt_Assign (BVar "ProcState_Z" (BType_Imm Bit1))
              (BExp_BinPred BIExp_Equal
                 (BExp_Den (BVar "R14" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R15" (BType_Imm Bit64))))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 12w)))|>;
       <|bb_label := BL_Address (Imm64 12w); bb_statements := [];
         bb_last_statement :=
           BStmt_CJmp (BExp_Den (BVar "ProcState_Z" (BType_Imm Bit1)))
             (BLE_Label (BL_Address (Imm64 24w)))
             (BLE_Label (BL_Address (Imm64 16w)))|>;
       <|bb_label := BL_Address (Imm64 16w);
         bb_statements :=
           [BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 4w))) (BExp_Const (Imm64 7w)))
                 (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 4291559424w))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 76w))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 76w)))
                    (BExp_Const (Imm64 4291624832w))));
            BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_And (BExp_Const (Imm64 127w))
                 (BExp_BinExp BIExp_RightShift
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 76w))) (BExp_Const (Imm64 6w)))] HD;
            BStmt_Assign (BVar "R10" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 76w))) BEnd_LittleEndian Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 20w)))|>;
       <|bb_label := BL_Address (Imm64 20w); bb_statements := [];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 28w)))|>;
       <|bb_label := BL_Address (Imm64 24w);
         bb_statements :=
           [BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 4291559424w))
                    (BExp_Den (BVar "R9" (BType_Imm Bit64))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 4291624832w))));
            BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_And (BExp_Const (Imm64 127w))
                 (BExp_BinExp BIExp_RightShift
                    (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 6w)))] HD;
            BStmt_Assign (BVar "R14" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_Den (BVar "R9" (BType_Imm Bit64))) BEnd_LittleEndian
                 Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 28w)))|>;
       <|bb_label := BL_Address (Imm64 28w); bb_statements := [];
         bb_last_statement := BStmt_Halt (BExp_Const (Imm32 0w))|>]
:bir_val_t bir_program_t
``;

val prog_2_cache_tag_index_part = ``
BirProgram
      [<|bb_label := BL_Address (Imm64 0w);
         bb_statements :=
           [BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R14" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 4291559424w))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R14" (BType_Imm Bit64)))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R14" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 4291624832w))));
            BStmt_Observe 0
              (BExp_BinPred BIExp_LessThan (BExp_Const (Imm64 60w))
                 (BExp_BinExp BIExp_Mod
                    (BExp_BinExp BIExp_RightShift
                       (BExp_BinExp BIExp_Plus
                          (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                          (BExp_Den (BVar "R14" (BType_Imm Bit64))))
                       (BExp_Const (Imm64 6w))) (BExp_Const (Imm64 128w))))
              [BExp_BinExp BIExp_RightShift
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R14" (BType_Imm Bit64))))
                 (BExp_Const (Imm64 6w))] HD;
            BStmt_Assign (BVar "R26" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R14" (BType_Imm Bit64))))
                 BEnd_LittleEndian Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 4w)))|>;
       <|bb_label := BL_Address (Imm64 4w);
         bb_statements :=
           [BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_Den (BVar "R17" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 4291559424w))
                    (BExp_Den (BVar "R17" (BType_Imm Bit64))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_Den (BVar "R17" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 4291624832w))));
            BStmt_Observe 0
              (BExp_BinPred BIExp_LessThan (BExp_Const (Imm64 60w))
                 (BExp_BinExp BIExp_Mod
                    (BExp_BinExp BIExp_RightShift
                       (BExp_Den (BVar "R17" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 6w))) (BExp_Const (Imm64 128w))))
              [BExp_BinExp BIExp_RightShift
                 (BExp_Den (BVar "R17" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 6w))] HD;
            BStmt_Assign (BVar "R15" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_Den (BVar "R17" (BType_Imm Bit64))) BEnd_LittleEndian
                 Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 8w)))|>;
       <|bb_label := BL_Address (Imm64 8w);
         bb_statements :=
           [BStmt_Assign (BVar "ProcState_C" (BType_Imm Bit1))
              (BExp_BinPred BIExp_LessOrEqual
                 (BExp_Den (BVar "R15" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R14" (BType_Imm Bit64))));
            BStmt_Assign (BVar "ProcState_N" (BType_Imm Bit1))
              (BExp_BinPred BIExp_SignedLessThan
                 (BExp_BinExp BIExp_Minus
                    (BExp_Den (BVar "R14" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R15" (BType_Imm Bit64))))
                 (BExp_Const (Imm64 0w)));
            BStmt_Assign (BVar "ProcState_V" (BType_Imm Bit1))
              (BExp_BinPred BIExp_Equal
                 (BExp_BinPred BIExp_SignedLessThan
                    (BExp_BinExp BIExp_Minus
                       (BExp_Den (BVar "R14" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R15" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 0w)))
                 (BExp_BinPred BIExp_SignedLessOrEqual
                    (BExp_Den (BVar "R15" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R14" (BType_Imm Bit64)))));
            BStmt_Assign (BVar "ProcState_Z" (BType_Imm Bit1))
              (BExp_BinPred BIExp_Equal
                 (BExp_Den (BVar "R14" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R15" (BType_Imm Bit64))))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 12w)))|>;
       <|bb_label := BL_Address (Imm64 12w); bb_statements := [];
         bb_last_statement :=
           BStmt_CJmp (BExp_Den (BVar "ProcState_Z" (BType_Imm Bit1)))
             (BLE_Label (BL_Address (Imm64 24w)))
             (BLE_Label (BL_Address (Imm64 16w)))|>;
       <|bb_label := BL_Address (Imm64 16w);
         bb_statements :=
           [BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 4w))) (BExp_Const (Imm64 7w)))
                 (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 4291559424w))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 76w))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 76w)))
                    (BExp_Const (Imm64 4291624832w))));
            BStmt_Observe 0
              (BExp_BinPred BIExp_LessThan (BExp_Const (Imm64 60w))
                 (BExp_BinExp BIExp_Mod
                    (BExp_BinExp BIExp_RightShift
                       (BExp_BinExp BIExp_Plus
                          (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                          (BExp_Const (Imm64 76w))) (BExp_Const (Imm64 6w)))
                    (BExp_Const (Imm64 128w))))
              [BExp_BinExp BIExp_RightShift
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 76w))) (BExp_Const (Imm64 6w))] HD;
            BStmt_Assign (BVar "R10" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 76w))) BEnd_LittleEndian Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 20w)))|>;
       <|bb_label := BL_Address (Imm64 20w); bb_statements := [];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 28w)))|>;
       <|bb_label := BL_Address (Imm64 24w);
         bb_statements :=
           [BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 4291559424w))
                    (BExp_Den (BVar "R9" (BType_Imm Bit64))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 4291624832w))));
            BStmt_Observe 0
              (BExp_BinPred BIExp_LessThan (BExp_Const (Imm64 60w))
                 (BExp_BinExp BIExp_Mod
                    (BExp_BinExp BIExp_RightShift
                       (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 6w))) (BExp_Const (Imm64 128w))))
              [BExp_BinExp BIExp_RightShift
                 (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 6w))] HD;
            BStmt_Assign (BVar "R14" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_Den (BVar "R9" (BType_Imm Bit64))) BEnd_LittleEndian
                 Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 28w)))|>;
       <|bb_label := BL_Address (Imm64 28w); bb_statements := [];
         bb_last_statement := BStmt_Halt (BExp_Const (Imm32 0w))|>]
:bir_val_t bir_program_t
``;

val prog_2_cache_tag_index_part_page = ``
BirProgram
      [<|bb_label := BL_Address (Imm64 0w);
         bb_statements :=
           [BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R14" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 4291559424w))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R14" (BType_Imm Bit64)))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R14" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 4291624832w))));
            BStmt_Observe 0
              (BExp_BinPred BIExp_LessThan (BExp_Const (Imm64 63w))
                 (BExp_BinExp BIExp_Mod
                    (BExp_BinExp BIExp_RightShift
                       (BExp_BinExp BIExp_Plus
                          (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                          (BExp_Den (BVar "R14" (BType_Imm Bit64))))
                       (BExp_Const (Imm64 6w))) (BExp_Const (Imm64 128w))))
              [BExp_BinExp BIExp_RightShift
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R14" (BType_Imm Bit64))))
                 (BExp_Const (Imm64 6w))] HD;
            BStmt_Assign (BVar "R26" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R14" (BType_Imm Bit64))))
                 BEnd_LittleEndian Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 4w)))|>;
       <|bb_label := BL_Address (Imm64 4w);
         bb_statements :=
           [BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_Den (BVar "R17" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 4291559424w))
                    (BExp_Den (BVar "R17" (BType_Imm Bit64))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_Den (BVar "R17" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 4291624832w))));
            BStmt_Observe 0
              (BExp_BinPred BIExp_LessThan (BExp_Const (Imm64 63w))
                 (BExp_BinExp BIExp_Mod
                    (BExp_BinExp BIExp_RightShift
                       (BExp_Den (BVar "R17" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 6w))) (BExp_Const (Imm64 128w))))
              [BExp_BinExp BIExp_RightShift
                 (BExp_Den (BVar "R17" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 6w))] HD;
            BStmt_Assign (BVar "R15" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_Den (BVar "R17" (BType_Imm Bit64))) BEnd_LittleEndian
                 Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 8w)))|>;
       <|bb_label := BL_Address (Imm64 8w);
         bb_statements :=
           [BStmt_Assign (BVar "ProcState_C" (BType_Imm Bit1))
              (BExp_BinPred BIExp_LessOrEqual
                 (BExp_Den (BVar "R15" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R14" (BType_Imm Bit64))));
            BStmt_Assign (BVar "ProcState_N" (BType_Imm Bit1))
              (BExp_BinPred BIExp_SignedLessThan
                 (BExp_BinExp BIExp_Minus
                    (BExp_Den (BVar "R14" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R15" (BType_Imm Bit64))))
                 (BExp_Const (Imm64 0w)));
            BStmt_Assign (BVar "ProcState_V" (BType_Imm Bit1))
              (BExp_BinPred BIExp_Equal
                 (BExp_BinPred BIExp_SignedLessThan
                    (BExp_BinExp BIExp_Minus
                       (BExp_Den (BVar "R14" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R15" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 0w)))
                 (BExp_BinPred BIExp_SignedLessOrEqual
                    (BExp_Den (BVar "R15" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R14" (BType_Imm Bit64)))));
            BStmt_Assign (BVar "ProcState_Z" (BType_Imm Bit1))
              (BExp_BinPred BIExp_Equal
                 (BExp_Den (BVar "R14" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R15" (BType_Imm Bit64))))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 12w)))|>;
       <|bb_label := BL_Address (Imm64 12w); bb_statements := [];
         bb_last_statement :=
           BStmt_CJmp (BExp_Den (BVar "ProcState_Z" (BType_Imm Bit1)))
             (BLE_Label (BL_Address (Imm64 24w)))
             (BLE_Label (BL_Address (Imm64 16w)))|>;
       <|bb_label := BL_Address (Imm64 16w);
         bb_statements :=
           [BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 4w))) (BExp_Const (Imm64 7w)))
                 (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 4291559424w))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 76w))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 76w)))
                    (BExp_Const (Imm64 4291624832w))));
            BStmt_Observe 0
              (BExp_BinPred BIExp_LessThan (BExp_Const (Imm64 63w))
                 (BExp_BinExp BIExp_Mod
                    (BExp_BinExp BIExp_RightShift
                       (BExp_BinExp BIExp_Plus
                          (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                          (BExp_Const (Imm64 76w))) (BExp_Const (Imm64 6w)))
                    (BExp_Const (Imm64 128w))))
              [BExp_BinExp BIExp_RightShift
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 76w))) (BExp_Const (Imm64 6w))] HD;
            BStmt_Assign (BVar "R10" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 76w))) BEnd_LittleEndian Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 20w)))|>;
       <|bb_label := BL_Address (Imm64 20w); bb_statements := [];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 28w)))|>;
       <|bb_label := BL_Address (Imm64 24w);
         bb_statements :=
           [BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 4291559424w))
                    (BExp_Den (BVar "R9" (BType_Imm Bit64))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 4291624832w))));
            BStmt_Observe 0
              (BExp_BinPred BIExp_LessThan (BExp_Const (Imm64 63w))
                 (BExp_BinExp BIExp_Mod
                    (BExp_BinExp BIExp_RightShift
                       (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 6w))) (BExp_Const (Imm64 128w))))
              [BExp_BinExp BIExp_RightShift
                 (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 6w))] HD;
            BStmt_Assign (BVar "R14" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_Den (BVar "R9" (BType_Imm Bit64))) BEnd_LittleEndian
                 Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 28w)))|>;
       <|bb_label := BL_Address (Imm64 28w); bb_statements := [];
         bb_last_statement := BStmt_Halt (BExp_Const (Imm32 0w))|>]
:bir_val_t bir_program_t
``;

(*
=================================
	ldr x26, [x14,x24]
obs0 0x0
obs0 x14+x24
	ldr x15, [x17, #0]
obs0 0x4
obs0 x17
	cmp x14, x15
obs0 0x8
	b.eq #0xC
obs0 0xC
	ldr x10, [x26, #76]
obs1 x9*
obs0 0x10
obs0 x26+76
	b #0x8
obs0 0x14
	ldr x14, [x9]
obs1 x26*+76
obs0 0x18
obs0 x9
	HALT
obs0 0x1C

=================================
*)

val prog_2_cache_speculation = ``
 BirProgram
  [<|bb_label := BL_Address (Imm64 (0w :word64));
     bb_statements :=
       [BStmt_Observe (0 :num) (BExp_Const (Imm1 (1w :word1)))
          [BExp_Const (Imm64 (0w :word64))] (HD :bir_val_t list -> bir_val_t);
        (BStmt_Assert
           (BExp_BinPred BIExp_Equal
              (BExp_BinExp BIExp_And
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R14" (BType_Imm Bit64))))
                 (BExp_Const (Imm64 (7w :word64))))
              (BExp_Const (Imm64 (0w :word64)))) :bir_val_t bir_stmt_basic_t);
        (BStmt_Assert
           (BExp_BinExp BIExp_And
              (BExp_BinPred BIExp_LessOrEqual
                 (BExp_Const (Imm64 (0xFFCC0000w :word64)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R14" (BType_Imm Bit64)))))
              (BExp_BinPred BIExp_LessThan
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R14" (BType_Imm Bit64))))
                 (BExp_Const (Imm64 (0xFFCCFF80w :word64))))) :
         bir_val_t bir_stmt_basic_t);
        BStmt_Observe (0 :num) (BExp_Const (Imm1 (1w :word1)))
          [BExp_BinExp BIExp_Plus (BExp_Den (BVar "R24" (BType_Imm Bit64)))
             (BExp_Den (BVar "R14" (BType_Imm Bit64)))]
          (HD :bir_val_t list -> bir_val_t);
        (BStmt_Assign (BVar "R26" (BType_Imm Bit64))
           (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
              (BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R14" (BType_Imm Bit64)))) BEnd_LittleEndian
              Bit64) :bir_val_t bir_stmt_basic_t)];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 (4w :word64))))|>;
   <|bb_label := BL_Address (Imm64 (4w :word64));
     bb_statements :=
       [BStmt_Observe (0 :num) (BExp_Const (Imm1 (1w :word1)))
          [BExp_Const (Imm64 (4w :word64))] (HD :bir_val_t list -> bir_val_t);
        (BStmt_Assert
           (BExp_BinPred BIExp_Equal
              (BExp_BinExp BIExp_And
                 (BExp_Den (BVar "R17" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 (7w :word64))))
              (BExp_Const (Imm64 (0w :word64)))) :bir_val_t bir_stmt_basic_t);
        (BStmt_Assert
           (BExp_BinExp BIExp_And
              (BExp_BinPred BIExp_LessOrEqual
                 (BExp_Const (Imm64 (0xFFCC0000w :word64)))
                 (BExp_Den (BVar "R17" (BType_Imm Bit64))))
              (BExp_BinPred BIExp_LessThan
                 (BExp_Den (BVar "R17" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 (0xFFCCFF80w :word64))))) :
         bir_val_t bir_stmt_basic_t);
        BStmt_Observe (0 :num) (BExp_Const (Imm1 (1w :word1)))
          [BExp_Den (BVar "R17" (BType_Imm Bit64))]
          (HD :bir_val_t list -> bir_val_t);
        (BStmt_Assign (BVar "R15" (BType_Imm Bit64))
           (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
              (BExp_Den (BVar "R17" (BType_Imm Bit64))) BEnd_LittleEndian
              Bit64) :bir_val_t bir_stmt_basic_t)];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 (8w :word64))))|>;
   <|bb_label := BL_Address (Imm64 (8w :word64));
     bb_statements :=
       [BStmt_Observe (0 :num) (BExp_Const (Imm1 (1w :word1)))
          [BExp_Const (Imm64 (8w :word64))] (HD :bir_val_t list -> bir_val_t);
        (BStmt_Assign (BVar "ProcState_C" (BType_Imm Bit1))
           (BExp_BinPred BIExp_LessOrEqual
              (BExp_Den (BVar "R15" (BType_Imm Bit64)))
              (BExp_Den (BVar "R14" (BType_Imm Bit64)))) :
         bir_val_t bir_stmt_basic_t);
        (BStmt_Assign (BVar "ProcState_N" (BType_Imm Bit1))
           (BExp_BinPred BIExp_SignedLessThan
              (BExp_BinExp BIExp_Minus
                 (BExp_Den (BVar "R14" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R15" (BType_Imm Bit64))))
              (BExp_Const (Imm64 (0w :word64)))) :bir_val_t bir_stmt_basic_t);
        (BStmt_Assign (BVar "ProcState_V" (BType_Imm Bit1))
           (BExp_BinPred BIExp_Equal
              (BExp_BinPred BIExp_SignedLessThan
                 (BExp_BinExp BIExp_Minus
                    (BExp_Den (BVar "R14" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R15" (BType_Imm Bit64))))
                 (BExp_Const (Imm64 (0w :word64))))
              (BExp_BinPred BIExp_SignedLessOrEqual
                 (BExp_Den (BVar "R15" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R14" (BType_Imm Bit64))))) :
         bir_val_t bir_stmt_basic_t);
        (BStmt_Assign (BVar "ProcState_Z" (BType_Imm Bit1))
           (BExp_BinPred BIExp_Equal
              (BExp_Den (BVar "R14" (BType_Imm Bit64)))
              (BExp_Den (BVar "R15" (BType_Imm Bit64)))) :
         bir_val_t bir_stmt_basic_t)];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 (12w :word64))))|>;
   <|bb_label := BL_Address (Imm64 (12w :word64));
     bb_statements :=
       [BStmt_Observe (0 :num) (BExp_Const (Imm1 (1w :word1)))
          [BExp_Const (Imm64 (12w :word64))]
          (HD :bir_val_t list -> bir_val_t)];
     bb_last_statement :=
       BStmt_CJmp (BExp_Den (BVar "ProcState_Z" (BType_Imm Bit1)))
         (BLE_Label (BL_Address (Imm64 (24w :word64))))
         (BLE_Label (BL_Address (Imm64 (16w :word64))))|>;
   <|bb_label := BL_Address (Imm64 (16w :word64));
     bb_statements :=
       [(BStmt_Assign (BVar "R9*" (BType_Imm Bit64))
           (BExp_Den (BVar "R9" (BType_Imm Bit64))) :
         bir_val_t bir_stmt_basic_t);
        (BStmt_Assign (BVar "MEM*" (BType_Mem Bit64 Bit8))
           (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8))) :
         bir_val_t bir_stmt_basic_t);
        (BStmt_Assert
           (BExp_BinPred BIExp_Equal
              (BExp_BinExp BIExp_And
                 (BExp_Den (BVar "R9*" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 (7w :word64))))
              (BExp_Const (Imm64 (0w :word64)))) :bir_val_t bir_stmt_basic_t);
        (BStmt_Assert
           (BExp_BinExp BIExp_And
              (BExp_BinPred BIExp_LessOrEqual
                 (BExp_Const (Imm64 (0xFFCC0000w :word64)))
                 (BExp_Den (BVar "R9*" (BType_Imm Bit64))))
              (BExp_BinPred BIExp_LessThan
                 (BExp_Den (BVar "R9*" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 (0xFFCCFF80w :word64))))) :
         bir_val_t bir_stmt_basic_t);
        BStmt_Observe (1 :num) (BExp_Const (Imm1 (1w :word1)))
          [BExp_Den (BVar "R9*" (BType_Imm Bit64))]
          (HD :bir_val_t list -> bir_val_t);
        (BStmt_Assign (BVar "R14" (BType_Imm Bit64))
           (BExp_Load (BExp_Den (BVar "MEM*" (BType_Mem Bit64 Bit8)))
              (BExp_Den (BVar "R9*" (BType_Imm Bit64))) BEnd_LittleEndian
              Bit64) :bir_val_t bir_stmt_basic_t);
        BStmt_Observe (0 :num) (BExp_Const (Imm1 (1w :word1)))
          [BExp_Const (Imm64 (16w :word64))]
          (HD :bir_val_t list -> bir_val_t);
        (BStmt_Assert
           (BExp_BinPred BIExp_Equal
              (BExp_BinExp BIExp_And
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 (4w :word64))))
                 (BExp_Const (Imm64 (7w :word64))))
              (BExp_Const (Imm64 (0w :word64)))) :bir_val_t bir_stmt_basic_t);
        (BStmt_Assert
           (BExp_BinExp BIExp_And
              (BExp_BinPred BIExp_LessOrEqual
                 (BExp_Const (Imm64 (0xFFCC0000w :word64)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 (76w :word64)))))
              (BExp_BinPred BIExp_LessThan
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 (76w :word64))))
                 (BExp_Const (Imm64 (0xFFCCFF80w :word64))))) :
         bir_val_t bir_stmt_basic_t);
        BStmt_Observe (0 :num) (BExp_Const (Imm1 (1w :word1)))
          [BExp_BinExp BIExp_Plus (BExp_Den (BVar "R26" (BType_Imm Bit64)))
             (BExp_Const (Imm64 (76w :word64)))]
          (HD :bir_val_t list -> bir_val_t);
        (BStmt_Assign (BVar "R10" (BType_Imm Bit64))
           (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
              (BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 (76w :word64)))) BEnd_LittleEndian Bit64) :
         bir_val_t bir_stmt_basic_t)];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 (20w :word64))))|>;
   <|bb_label := BL_Address (Imm64 (20w :word64));
     bb_statements :=
       [BStmt_Observe (0 :num) (BExp_Const (Imm1 (1w :word1)))
          [BExp_Const (Imm64 (20w :word64))]
          (HD :bir_val_t list -> bir_val_t)];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 (28w :word64))))|>;
   <|bb_label := BL_Address (Imm64 (24w :word64));
     bb_statements :=
       [(BStmt_Assign (BVar "R26*" (BType_Imm Bit64))
           (BExp_Den (BVar "R26" (BType_Imm Bit64))) :
         bir_val_t bir_stmt_basic_t);
        (BStmt_Assign (BVar "MEM*" (BType_Mem Bit64 Bit8))
           (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8))) :
         bir_val_t bir_stmt_basic_t);
        (BStmt_Assert
           (BExp_BinPred BIExp_Equal
              (BExp_BinExp BIExp_And
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R26*" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 (4w :word64))))
                 (BExp_Const (Imm64 (7w :word64))))
              (BExp_Const (Imm64 (0w :word64)))) :bir_val_t bir_stmt_basic_t);
        (BStmt_Assert
           (BExp_BinExp BIExp_And
              (BExp_BinPred BIExp_LessOrEqual
                 (BExp_Const (Imm64 (0xFFCC0000w :word64)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R26*" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 (76w :word64)))))
              (BExp_BinPred BIExp_LessThan
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R26*" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 (76w :word64))))
                 (BExp_Const (Imm64 (0xFFCCFF80w :word64))))) :
         bir_val_t bir_stmt_basic_t);
        BStmt_Observe (1 :num) (BExp_Const (Imm1 (1w :word1)))
          [BExp_BinExp BIExp_Plus (BExp_Den (BVar "R26*" (BType_Imm Bit64)))
             (BExp_Const (Imm64 (76w :word64)))]
          (HD :bir_val_t list -> bir_val_t);
        (BStmt_Assign (BVar "R10" (BType_Imm Bit64))
           (BExp_Load (BExp_Den (BVar "MEM*" (BType_Mem Bit64 Bit8)))
              (BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "R26*" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 (76w :word64)))) BEnd_LittleEndian Bit64) :
         bir_val_t bir_stmt_basic_t);
        BStmt_Observe (0 :num) (BExp_Const (Imm1 (1w :word1)))
          [BExp_Const (Imm64 (24w :word64))]
          (HD :bir_val_t list -> bir_val_t);
        (BStmt_Assert
           (BExp_BinPred BIExp_Equal
              (BExp_BinExp BIExp_And (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 (7w :word64))))
              (BExp_Const (Imm64 (0w :word64)))) :bir_val_t bir_stmt_basic_t);
        (BStmt_Assert
           (BExp_BinExp BIExp_And
              (BExp_BinPred BIExp_LessOrEqual
                 (BExp_Const (Imm64 (0xFFCC0000w :word64)))
                 (BExp_Den (BVar "R9" (BType_Imm Bit64))))
              (BExp_BinPred BIExp_LessThan
                 (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 (0xFFCCFF80w :word64))))) :
         bir_val_t bir_stmt_basic_t);
        BStmt_Observe (0 :num) (BExp_Const (Imm1 (1w :word1)))
          [BExp_Den (BVar "R9" (BType_Imm Bit64))]
          (HD :bir_val_t list -> bir_val_t);
        (BStmt_Assign (BVar "R14" (BType_Imm Bit64))
           (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
              (BExp_Den (BVar "R9" (BType_Imm Bit64))) BEnd_LittleEndian
              Bit64) :bir_val_t bir_stmt_basic_t)];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 (28w :word64))))|>;
   <|bb_label := BL_Address (Imm64 (28w :word64));
     bb_statements :=
       [BStmt_Observe (0 :num) (BExp_Const (Imm1 (1w :word1)))
          [BExp_Const (Imm64 (28w :word64))]
          (HD :bir_val_t list -> bir_val_t)];
     bb_last_statement := BStmt_Halt (BExp_Const (Imm32 (0w :word32)))|>]
:bir_val_t bir_program_t
``;

val prog_2_cache_speculation_first = ``
F
``;

val prog_2_test =
  ("prog_2 - branch and merge", prog_2,
     (prog_2_mem_address_pc,
      prog_2_cache_tag_index,
      prog_2_cache_tag_only,
      prog_2_cache_index_only,
      prog_2_cache_tag_index_part,
      prog_2_cache_tag_index_part_page,
      prog_2_cache_speculation,
      prog_2_cache_speculation_first)
  );
