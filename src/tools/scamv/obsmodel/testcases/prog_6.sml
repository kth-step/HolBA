(* ========================= prog_6 - xld_br_yld_mod1 =========================== *)

(*
=================================
	ldr x12, [x27]
	cmp x15, x16
	b.gt #0xC
	ldr x8, [x8, #8]
	b #0x8
	nop
=================================
*)

val prog_6 = ``
BirProgram
       [<|bb_label :=
            BL_Address_HC (Imm64 (0w :word64)) "F940036C (ldr x12, [x27])";
          bb_atomic := F;
          bb_statements :=
            [(BStmt_Assert
                (BExp_Aligned Bit64 (3 :num)
                   (BExp_Den (BVar "R27" (BType_Imm Bit64)))) :
              bir_val_t bir_stmt_basic_t);
             (BStmt_Assign (BVar "R12" (BType_Imm Bit64))
                (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                   (BExp_Den (BVar "R27" (BType_Imm Bit64)))
                   BEnd_LittleEndian Bit64) :bir_val_t bir_stmt_basic_t)];
          bb_last_statement :=
            BStmt_Jmp (BLE_Label (BL_Address (Imm64 (4w :word64))))|>;
        <|bb_label :=
            BL_Address_HC (Imm64 (4w :word64)) "EB1001FF (cmp x15, x16)";
          bb_atomic := F;
          bb_statements :=
            [(BStmt_Assign (BVar "ProcState_C" BType_Bool)
                (BExp_nzcv_SUB_C (BExp_Den (BVar "R15" (BType_Imm Bit64)))
                   (BExp_Den (BVar "R16" (BType_Imm Bit64)))) :
              bir_val_t bir_stmt_basic_t);
             (BStmt_Assign (BVar "ProcState_N" BType_Bool)
                (BExp_nzcv_SUB_N Bit64
                   (BExp_Den (BVar "R15" (BType_Imm Bit64)))
                   (BExp_Den (BVar "R16" (BType_Imm Bit64)))) :
              bir_val_t bir_stmt_basic_t);
             (BStmt_Assign (BVar "ProcState_V" BType_Bool)
                (BExp_nzcv_SUB_V Bit64
                   (BExp_Den (BVar "R15" (BType_Imm Bit64)))
                   (BExp_Den (BVar "R16" (BType_Imm Bit64)))) :
              bir_val_t bir_stmt_basic_t);
             (BStmt_Assign (BVar "ProcState_Z" BType_Bool)
                (BExp_nzcv_SUB_Z (BExp_Den (BVar "R15" (BType_Imm Bit64)))
                   (BExp_Den (BVar "R16" (BType_Imm Bit64)))) :
              bir_val_t bir_stmt_basic_t)];
          bb_last_statement :=
            BStmt_Jmp (BLE_Label (BL_Address (Imm64 (8w :word64))))|>;
        <|bb_label :=
            BL_Address_HC (Imm64 (8w :word64))
              "5400006C (b.gt 14 <.text+0x14>)";
          bb_atomic := F;
          bb_statements := ([] :bir_val_t bir_stmt_basic_t list );
          bb_last_statement :=
            BStmt_CJmp
              (BExp_BinExp BIExp_Or
                 (BExp_UnaryExp BIExp_Not
                    (BExp_BinPred BIExp_Equal
                       (BExp_Den (BVar "ProcState_N" BType_Bool))
                       (BExp_Den (BVar "ProcState_V" BType_Bool))))
                 (BExp_Den (BVar "ProcState_Z" BType_Bool)))
              (BLE_Label (BL_Address (Imm64 (12w :word64))))
              (BLE_Label (BL_Address (Imm64 (20w :word64))))|>;
        <|bb_label :=
            BL_Address_HC (Imm64 (12w :word64)) "F9400508 (ldr x8, [x8, #8])";
          bb_atomic := F;
          bb_statements :=
            [(BStmt_Assert
                (BExp_Aligned Bit64 (3 :num)
                   (BExp_Den (BVar "R8" (BType_Imm Bit64)))) :
              bir_val_t bir_stmt_basic_t);
             (BStmt_Assign (BVar "R8" (BType_Imm Bit64))
                (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                   (BExp_BinExp BIExp_Plus
                      (BExp_Den (BVar "R8" (BType_Imm Bit64)))
                      (BExp_Const (Imm64 (8w :word64)))) BEnd_LittleEndian
                   Bit64) :bir_val_t bir_stmt_basic_t)];
          bb_last_statement :=
            BStmt_Jmp (BLE_Label (BL_Address (Imm64 (16w :word64))))|>;
        <|bb_label :=
            BL_Address_HC (Imm64 (16w :word64))
              "14000002 (b 18 <.text+0x18>)";
          bb_atomic := F;
          bb_statements := ([] :bir_val_t bir_stmt_basic_t list );
          bb_last_statement :=
            BStmt_Jmp (BLE_Label (BL_Address (Imm64 (24w :word64))))|>;
        <|bb_label := BL_Address_HC (Imm64 (20w :word64)) "D503201F (nop)";
          bb_atomic := F;
          bb_statements := ([] :bir_val_t bir_stmt_basic_t list );
          bb_last_statement :=
            BStmt_Jmp (BLE_Label (BL_Address (Imm64 (24w :word64))))|>;
        <|bb_label := BL_Address (Imm64 (24w :word64));
          bb_atomic := F;
          bb_statements := ([] :bir_val_t bir_stmt_basic_t list );
          bb_last_statement := BStmt_Halt (BExp_Const (Imm32 (0w :word32)))|>]
:bir_val_t bir_program_t
``;

val prog_6_mem_address_pc = ``
F
``;

val prog_6_cache_tag_index = ``
F
``;

val prog_6_cache_tag_only = ``
F
``;

val prog_6_cache_index_only = ``
F
``;

val prog_6_cache_tag_index_part = ``
F
``;

val prog_6_cache_tag_index_part_page = ``
F
``;


(*
=================================
	ldr x12, [x27]
obs0 0x0
obs0 x27
	cmp x15, x16
obs0 0x4
	b.gt #0xC
obs0 0x8
	ldr x8, [x8, #8]
obs0 0xC
obs0 x8+8
	b #0x8
obs0 0x10
	nop
obs1 x8*+8
obs0 0x14
	HALT
obs0 0x18
=================================
*)
val prog_6_cache_speculation = ``
BirProgram
      [<|bb_label := BL_Address (Imm64 (0w :word64));
         bb_atomic := F;
         bb_statements :=
           [BStmt_Observe (0 :num) (BExp_Const (Imm1 (1w :word1)))
              [BExp_Const (Imm64 (0w :word64))]
              (HD :bir_val_t list -> bir_val_t );
            (BStmt_Assert
               (BExp_BinPred BIExp_Equal
                  (BExp_BinExp BIExp_And
                     (BExp_Den (BVar "R27" (BType_Imm Bit64)))
                     (BExp_Const (Imm64 (7w :word64))))
                  (BExp_Const (Imm64 (0w :word64)))) :
             bir_val_t bir_stmt_basic_t);
            (BStmt_Assert
               (BExp_BinExp BIExp_And
                  (BExp_BinPred BIExp_LessOrEqual
                     (BExp_Const (Imm64 (4291559424w :word64)))
                     (BExp_Den (BVar "R27" (BType_Imm Bit64))))
                  (BExp_BinPred BIExp_LessThan
                     (BExp_Den (BVar "R27" (BType_Imm Bit64)))
                     (BExp_Const (Imm64 (4291624832w :word64))))) :
             bir_val_t bir_stmt_basic_t);
            BStmt_Observe (0 :num) (BExp_Const (Imm1 (1w :word1)))
              [BExp_Den (BVar "R27" (BType_Imm Bit64))]
              (HD :bir_val_t list -> bir_val_t );
            (BStmt_Assign (BVar "R12" (BType_Imm Bit64))
               (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                  (BExp_Den (BVar "R27" (BType_Imm Bit64))) BEnd_LittleEndian
                  Bit64) :bir_val_t bir_stmt_basic_t)];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 (4w :word64))))|>;
       <|bb_label := BL_Address (Imm64 (4w :word64));
         bb_atomic := F;
         bb_statements :=
           [BStmt_Observe (0 :num) (BExp_Const (Imm1 (1w :word1)))
              [BExp_Const (Imm64 (4w :word64))]
              (HD :bir_val_t list -> bir_val_t );
            (BStmt_Assign (BVar "ProcState_C" (BType_Imm Bit1))
               (BExp_BinPred BIExp_LessOrEqual
                  (BExp_Den (BVar "R16" (BType_Imm Bit64)))
                  (BExp_Den (BVar "R15" (BType_Imm Bit64)))) :
             bir_val_t bir_stmt_basic_t);
            (BStmt_Assign (BVar "ProcState_N" (BType_Imm Bit1))
               (BExp_BinPred BIExp_SignedLessThan
                  (BExp_BinExp BIExp_Minus
                     (BExp_Den (BVar "R15" (BType_Imm Bit64)))
                     (BExp_Den (BVar "R16" (BType_Imm Bit64))))
                  (BExp_Const (Imm64 (0w :word64)))) :
             bir_val_t bir_stmt_basic_t);
            (BStmt_Assign (BVar "ProcState_V" (BType_Imm Bit1))
               (BExp_BinPred BIExp_Equal
                  (BExp_BinPred BIExp_SignedLessThan
                     (BExp_BinExp BIExp_Minus
                        (BExp_Den (BVar "R15" (BType_Imm Bit64)))
                        (BExp_Den (BVar "R16" (BType_Imm Bit64))))
                     (BExp_Const (Imm64 (0w :word64))))
                  (BExp_BinPred BIExp_SignedLessOrEqual
                     (BExp_Den (BVar "R16" (BType_Imm Bit64)))
                     (BExp_Den (BVar "R15" (BType_Imm Bit64))))) :
             bir_val_t bir_stmt_basic_t);
            (BStmt_Assign (BVar "ProcState_Z" (BType_Imm Bit1))
               (BExp_BinPred BIExp_Equal
                  (BExp_Den (BVar "R15" (BType_Imm Bit64)))
                  (BExp_Den (BVar "R16" (BType_Imm Bit64)))) :
             bir_val_t bir_stmt_basic_t)];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 (8w :word64))))|>;
       <|bb_label := BL_Address (Imm64 (8w :word64));
         bb_atomic := F;
         bb_statements :=
           [BStmt_Observe (0 :num) (BExp_Const (Imm1 (1w :word1)))
              [BExp_Const (Imm64 (8w :word64))]
              (HD :bir_val_t list -> bir_val_t )];
         bb_last_statement :=
           BStmt_CJmp
             (BExp_BinExp BIExp_Or
                (BExp_UnaryExp BIExp_Not
                   (BExp_BinPred BIExp_Equal
                      (BExp_Den (BVar "ProcState_N" (BType_Imm Bit1)))
                      (BExp_Den (BVar "ProcState_V" (BType_Imm Bit1)))))
                (BExp_Den (BVar "ProcState_Z" (BType_Imm Bit1))))
             (BLE_Label (BL_Address (Imm64 (12w :word64))))
             (BLE_Label (BL_Address (Imm64 (20w :word64))))|>;
       <|bb_label := BL_Address (Imm64 (12w :word64));
         bb_atomic := F;
         bb_statements :=
           [BStmt_Observe (0 :num) (BExp_Const (Imm1 (1w :word1)))
              [BExp_Const (Imm64 (12w :word64))]
              (HD :bir_val_t list -> bir_val_t );
            (BStmt_Assert
               (BExp_BinPred BIExp_Equal
                  (BExp_BinExp BIExp_And
                     (BExp_Den (BVar "R8" (BType_Imm Bit64)))
                     (BExp_Const (Imm64 (7w :word64))))
                  (BExp_Const (Imm64 (0w :word64)))) :
             bir_val_t bir_stmt_basic_t);
            (BStmt_Assert
               (BExp_BinExp BIExp_And
                  (BExp_BinPred BIExp_LessOrEqual
                     (BExp_Const (Imm64 (4291559424w :word64)))
                     (BExp_BinExp BIExp_Plus
                        (BExp_Den (BVar "R8" (BType_Imm Bit64)))
                        (BExp_Const (Imm64 (8w :word64)))))
                  (BExp_BinPred BIExp_LessThan
                     (BExp_BinExp BIExp_Plus
                        (BExp_Den (BVar "R8" (BType_Imm Bit64)))
                        (BExp_Const (Imm64 (8w :word64))))
                     (BExp_Const (Imm64 (4291624832w :word64))))) :
             bir_val_t bir_stmt_basic_t);
            BStmt_Observe (0 :num) (BExp_Const (Imm1 (1w :word1)))
              [BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "R8" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 (8w :word64)))]
              (HD :bir_val_t list -> bir_val_t );
            (BStmt_Assign (BVar "R8" (BType_Imm Bit64))
               (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                  (BExp_BinExp BIExp_Plus
                     (BExp_Den (BVar "R8" (BType_Imm Bit64)))
                     (BExp_Const (Imm64 (8w :word64)))) BEnd_LittleEndian
                  Bit64) :bir_val_t bir_stmt_basic_t)];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 (16w :word64))))|>;
       <|bb_label := BL_Address (Imm64 (16w :word64));
         bb_atomic := F;
         bb_statements :=
           [BStmt_Observe (0 :num) (BExp_Const (Imm1 (1w :word1)))
              [BExp_Const (Imm64 (16w :word64))]
              (HD :bir_val_t list -> bir_val_t )];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 (24w :word64))))|>;
       <|bb_label := BL_Address (Imm64 (20w :word64));
         bb_atomic := F;
         bb_statements :=
           [(BStmt_Assign (BVar "R8*" (BType_Imm Bit64))
               (BExp_Den (BVar "R8" (BType_Imm Bit64))) :
             bir_val_t bir_stmt_basic_t);
            (BStmt_Assert
               (BExp_BinExp BIExp_And
                  (BExp_BinPred BIExp_LessOrEqual
                     (BExp_Const (Imm64 (2148532224w :word64)))
                     (BExp_BinExp BIExp_Plus
                        (BExp_Den (BVar "R8*" (BType_Imm Bit64)))
                        (BExp_Const (Imm64 (8w :word64)))))
                  (BExp_BinPred BIExp_LessThan
                     (BExp_BinExp BIExp_Plus
                        (BExp_Den (BVar "R8*" (BType_Imm Bit64)))
                        (BExp_Const (Imm64 (8w :word64))))
                     (BExp_Const (Imm64 (2148794240w :word64))))) :
             bir_val_t bir_stmt_basic_t);
            BStmt_Observe (1 :num) (BExp_Const (Imm1 (1w :word1)))
              [BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "R8*" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 (8w :word64)))]
              (HD :bir_val_t list -> bir_val_t );
            BStmt_Observe (0 :num) (BExp_Const (Imm1 (1w :word1)))
              [BExp_Const (Imm64 (20w :word64))]
              (HD :bir_val_t list -> bir_val_t )];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 (24w :word64))))|>;
       <|bb_label := BL_Address (Imm64 (24w :word64));
         bb_atomic := F;
         bb_statements :=
           [BStmt_Observe (0 :num) (BExp_Const (Imm1 (1w :word1)))
              [BExp_Const (Imm64 (24w :word64))]
              (HD :bir_val_t list -> bir_val_t )];
         bb_last_statement := BStmt_Halt (BExp_Const (Imm32 (0w :word32)))|>]
:bir_val_t bir_program_t
``;

val prog_6_cache_speculation_first = ``
F
``;

val prog_6_test =
  ("prog_6 - xld_br_yld_mod1", prog_6,
     (prog_6_mem_address_pc,
      prog_6_cache_tag_index,
      prog_6_cache_tag_only,
      prog_6_cache_index_only,
      prog_6_cache_tag_index_part,
      prog_6_cache_tag_index_part_page,
      prog_6_cache_speculation,
      prog_6_cache_speculation_first)
  );
