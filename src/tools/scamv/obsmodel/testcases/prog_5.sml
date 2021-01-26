(* ========================= prog_5 - spectre_v1_mod1 =========================== *)

(*
=================================
	cmp x1, x2
	b.hs #0x14
	ldr x4, [x3, x1]
	lsl x4, x4, #0x6
	ldr x6, [x5, x4]
	b #0x8
	nop
=================================
*)

val prog_5 = ``
BirProgram
       [<|bb_label :=
            BL_Address_HC (Imm64 (0w :word64)) "EB02003F (cmp x1, x2)";
          bb_statements :=
            [(BStmt_Assign (BVar "ProcState_C" BType_Bool)
                (BExp_nzcv_SUB_C (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                   (BExp_Den (BVar "R2" (BType_Imm Bit64)))) :
              bir_val_t bir_stmt_basic_t);
             (BStmt_Assign (BVar "ProcState_N" BType_Bool)
                (BExp_nzcv_SUB_N Bit64
                   (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                   (BExp_Den (BVar "R2" (BType_Imm Bit64)))) :
              bir_val_t bir_stmt_basic_t);
             (BStmt_Assign (BVar "ProcState_V" BType_Bool)
                (BExp_nzcv_SUB_V Bit64
                   (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                   (BExp_Den (BVar "R2" (BType_Imm Bit64)))) :
              bir_val_t bir_stmt_basic_t);
             (BStmt_Assign (BVar "ProcState_Z" BType_Bool)
                (BExp_nzcv_SUB_Z (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                   (BExp_Den (BVar "R2" (BType_Imm Bit64)))) :
              bir_val_t bir_stmt_basic_t)];
          bb_last_statement :=
            BStmt_Jmp (BLE_Label (BL_Address (Imm64 (4w :word64))))|>;
        <|bb_label :=
            BL_Address_HC (Imm64 (4w :word64))
              "540000A2 (b.cs 18 <.text+0x18>  // b.hs, b.nlast)";
          bb_statements := ([] :bir_val_t bir_stmt_basic_t list );
          bb_last_statement :=
            BStmt_CJmp (BExp_Den (BVar "ProcState_C" BType_Bool))
              (BLE_Label (BL_Address (Imm64 (24w :word64))))
              (BLE_Label (BL_Address (Imm64 (8w :word64))))|>;
        <|bb_label :=
            BL_Address_HC (Imm64 (8w :word64)) "F8616864 (ldr x4, [x3, x1])";
          bb_statements :=
            [(BStmt_Assert
                (BExp_Aligned Bit64 (3 :num)
                   (BExp_BinExp BIExp_Plus
                      (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                      (BExp_Den (BVar "R3" (BType_Imm Bit64))))) :
              bir_val_t bir_stmt_basic_t);
             (BStmt_Assign (BVar "R4" (BType_Imm Bit64))
                (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                   (BExp_BinExp BIExp_Plus
                      (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                      (BExp_Den (BVar "R3" (BType_Imm Bit64))))
                   BEnd_LittleEndian Bit64) :bir_val_t bir_stmt_basic_t)];
          bb_last_statement :=
            BStmt_Jmp (BLE_Label (BL_Address (Imm64 (12w :word64))))|>;
        <|bb_label :=
            BL_Address_HC (Imm64 (12w :word64)) "D37AE484 (lsl x4, x4, #6)";
          bb_statements :=
            [(BStmt_Assign (BVar "R4" (BType_Imm Bit64))
                (BExp_BinExp BIExp_And
                   (BExp_Const (Imm64 (18446744073709551615w :word64)))
                   (BExp_BinExp BIExp_LeftShift
                      (BExp_Den (BVar "R4" (BType_Imm Bit64)))
                      (BExp_Const (Imm64 (6w :word64))))) :
              bir_val_t bir_stmt_basic_t)];
          bb_last_statement :=
            BStmt_Jmp (BLE_Label (BL_Address (Imm64 (16w :word64))))|>;
        <|bb_label :=
            BL_Address_HC (Imm64 (16w :word64)) "F86468A6 (ldr x6, [x5, x4])";
          bb_statements :=
            [(BStmt_Assert
                (BExp_Aligned Bit64 (3 :num)
                   (BExp_BinExp BIExp_Plus
                      (BExp_Den (BVar "R5" (BType_Imm Bit64)))
                      (BExp_Den (BVar "R4" (BType_Imm Bit64))))) :
              bir_val_t bir_stmt_basic_t);
             (BStmt_Assign (BVar "R6" (BType_Imm Bit64))
                (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                   (BExp_BinExp BIExp_Plus
                      (BExp_Den (BVar "R5" (BType_Imm Bit64)))
                      (BExp_Den (BVar "R4" (BType_Imm Bit64))))
                   BEnd_LittleEndian Bit64) :bir_val_t bir_stmt_basic_t)];
          bb_last_statement :=
            BStmt_Jmp (BLE_Label (BL_Address (Imm64 (20w :word64))))|>;
        <|bb_label :=
            BL_Address_HC (Imm64 (20w :word64))
              "14000002 (b 1c <.text+0x1c>)";
          bb_statements := ([] :bir_val_t bir_stmt_basic_t list );
          bb_last_statement :=
            BStmt_Jmp (BLE_Label (BL_Address (Imm64 (28w :word64))))|>;
        <|bb_label := BL_Address_HC (Imm64 (24w :word64)) "D503201F (nop)";
          bb_statements := ([] :bir_val_t bir_stmt_basic_t list );
          bb_last_statement :=
            BStmt_Jmp (BLE_Label (BL_Address (Imm64 (28w :word64))))|>;
        <|bb_label := BL_Address (Imm64 (28w :word64));
          bb_statements := ([] :bir_val_t bir_stmt_basic_t list );
          bb_last_statement := BStmt_Halt (BExp_Const (Imm32 (0w :word32)))|>]
:bir_val_t bir_program_t
``;

val prog_5_mem_address_pc = ``
F
``;

val prog_5_cache_tag_index = ``
F
``;

val prog_5_cache_tag_only = ``
F
``;

val prog_5_cache_index_only = ``
F
``;

val prog_5_cache_tag_index_part = ``
F
``;

val prog_5_cache_tag_index_part_page = ``
F
``;

val prog_5_cache_speculation = ``
F
``;


(*
=================================
	cmp x1, x2
obs0 0x0
	b.hs #0x14
obs0 0x4
	ldr x4, [x3, x1]
obs0 0x8
obs0 x1+x3
	lsl x4, x4, #0x6
obs0 0xC
	ldr x6, [x5, x4]
obs0 0x10
obs0 x5+x4
	b #0x8
obs0 0x14
	nop
obs0 x1*+x3*
obs1 x5*+x4*
obs0 0x18
	HALT
obs0 0x1C
=================================
*)
val prog_5_cache_speculation_first = ``
 BirProgram
  [<|bb_label := BL_Address (Imm64 (0w :word64));
     bb_statements :=
       [BStmt_Observe (0 :num) (BExp_Const (Imm1 (1w :word1)))
          [BExp_Const (Imm64 (0w :word64))]
          (HD :bir_val_t list -> bir_val_t );
        (BStmt_Assign (BVar "ProcState_C" (BType_Imm Bit1))
           (BExp_BinPred BIExp_LessOrEqual
              (BExp_Den (BVar "R2" (BType_Imm Bit64)))
              (BExp_Den (BVar "R1" (BType_Imm Bit64)))) :
         bir_val_t bir_stmt_basic_t);
        (BStmt_Assign (BVar "ProcState_N" (BType_Imm Bit1))
           (BExp_BinPred BIExp_SignedLessThan
              (BExp_BinExp BIExp_Minus
                 (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R2" (BType_Imm Bit64))))
              (BExp_Const (Imm64 (0w :word64)))) :bir_val_t bir_stmt_basic_t);
        (BStmt_Assign (BVar "ProcState_V" (BType_Imm Bit1))
           (BExp_BinPred BIExp_Equal
              (BExp_BinPred BIExp_SignedLessThan
                 (BExp_BinExp BIExp_Minus
                    (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R2" (BType_Imm Bit64))))
                 (BExp_Const (Imm64 (0w :word64))))
              (BExp_BinPred BIExp_SignedLessOrEqual
                 (BExp_Den (BVar "R2" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R1" (BType_Imm Bit64))))) :
         bir_val_t bir_stmt_basic_t);
        (BStmt_Assign (BVar "ProcState_Z" (BType_Imm Bit1))
           (BExp_BinPred BIExp_Equal (BExp_Den (BVar "R1" (BType_Imm Bit64)))
              (BExp_Den (BVar "R2" (BType_Imm Bit64)))) :
         bir_val_t bir_stmt_basic_t)];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 (4w :word64))))|>;
   <|bb_label := BL_Address (Imm64 (4w :word64));
     bb_statements :=
       [BStmt_Observe (0 :num) (BExp_Const (Imm1 (1w :word1)))
          [BExp_Const (Imm64 (4w :word64))]
          (HD :bir_val_t list -> bir_val_t )];
     bb_last_statement :=
       BStmt_CJmp (BExp_Den (BVar "ProcState_C" (BType_Imm Bit1)))
         (BLE_Label (BL_Address (Imm64 (24w :word64))))
         (BLE_Label (BL_Address (Imm64 (8w :word64))))|>;
   <|bb_label := BL_Address (Imm64 (8w :word64));
     bb_statements :=
       [BStmt_Observe (0 :num) (BExp_Const (Imm1 (1w :word1)))
          [BExp_Const (Imm64 (8w :word64))]
          (HD :bir_val_t list -> bir_val_t );
        (BStmt_Assert
           (BExp_BinPred BIExp_Equal
              (BExp_BinExp BIExp_And
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R3" (BType_Imm Bit64))))
                 (BExp_Const (Imm64 (7w :word64))))
              (BExp_Const (Imm64 (0w :word64)))) :bir_val_t bir_stmt_basic_t);
        (BStmt_Assert
           (BExp_BinExp BIExp_And
              (BExp_BinPred BIExp_LessOrEqual
                 (BExp_Const (Imm64 (4291559424w :word64)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R3" (BType_Imm Bit64)))))
              (BExp_BinPred BIExp_LessThan
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R3" (BType_Imm Bit64))))
                 (BExp_Const (Imm64 (4291624832w :word64))))) :
         bir_val_t bir_stmt_basic_t);
        BStmt_Observe (0 :num) (BExp_Const (Imm1 (1w :word1)))
          [BExp_BinExp BIExp_Plus (BExp_Den (BVar "R1" (BType_Imm Bit64)))
             (BExp_Den (BVar "R3" (BType_Imm Bit64)))]
          (HD :bir_val_t list -> bir_val_t );
        (BStmt_Assign (BVar "R4" (BType_Imm Bit64))
           (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
              (BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R3" (BType_Imm Bit64)))) BEnd_LittleEndian
              Bit64) :bir_val_t bir_stmt_basic_t)];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 (12w :word64))))|>;
   <|bb_label := BL_Address (Imm64 (12w :word64));
     bb_statements :=
       [BStmt_Observe (0 :num) (BExp_Const (Imm1 (1w :word1)))
          [BExp_Const (Imm64 (12w :word64))]
          (HD :bir_val_t list -> bir_val_t );
        (BStmt_Assign (BVar "R4" (BType_Imm Bit64))
           (BExp_BinExp BIExp_And
              (BExp_Const (Imm64 (18446744073709551615w :word64)))
              (BExp_BinExp BIExp_LeftShift
                 (BExp_Den (BVar "R4" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 (6w :word64))))) :
         bir_val_t bir_stmt_basic_t)];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 (16w :word64))))|>;
   <|bb_label := BL_Address (Imm64 (16w :word64));
     bb_statements :=
       [BStmt_Observe (0 :num) (BExp_Const (Imm1 (1w :word1)))
          [BExp_Const (Imm64 (16w :word64))]
          (HD :bir_val_t list -> bir_val_t );
        (BStmt_Assert
           (BExp_BinPred BIExp_Equal
              (BExp_BinExp BIExp_And
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R5" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R4" (BType_Imm Bit64))))
                 (BExp_Const (Imm64 (7w :word64))))
              (BExp_Const (Imm64 (0w :word64)))) :bir_val_t bir_stmt_basic_t);
        (BStmt_Assert
           (BExp_BinExp BIExp_And
              (BExp_BinPred BIExp_LessOrEqual
                 (BExp_Const (Imm64 (4291559424w :word64)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R5" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R4" (BType_Imm Bit64)))))
              (BExp_BinPred BIExp_LessThan
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R5" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R4" (BType_Imm Bit64))))
                 (BExp_Const (Imm64 (4291624832w :word64))))) :
         bir_val_t bir_stmt_basic_t);
        BStmt_Observe (0 :num) (BExp_Const (Imm1 (1w :word1)))
          [BExp_BinExp BIExp_Plus (BExp_Den (BVar "R5" (BType_Imm Bit64)))
             (BExp_Den (BVar "R4" (BType_Imm Bit64)))]
          (HD :bir_val_t list -> bir_val_t );
        (BStmt_Assign (BVar "R6" (BType_Imm Bit64))
           (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
              (BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "R5" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R4" (BType_Imm Bit64)))) BEnd_LittleEndian
              Bit64) :bir_val_t bir_stmt_basic_t)];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 (20w :word64))))|>;
   <|bb_label := BL_Address (Imm64 (20w :word64));
     bb_statements :=
       [BStmt_Observe (0 :num) (BExp_Const (Imm1 (1w :word1)))
          [BExp_Const (Imm64 (20w :word64))]
          (HD :bir_val_t list -> bir_val_t )];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 (28w :word64))))|>;
   <|bb_label := BL_Address (Imm64 (24w :word64));
     bb_statements :=
       [(BStmt_Assign (BVar "R4*" (BType_Imm Bit64))
           (BExp_Den (BVar "R4" (BType_Imm Bit64))) :
         bir_val_t bir_stmt_basic_t);
        (BStmt_Assign (BVar "R5*" (BType_Imm Bit64))
           (BExp_Den (BVar "R5" (BType_Imm Bit64))) :
         bir_val_t bir_stmt_basic_t);
        (BStmt_Assign (BVar "R3*" (BType_Imm Bit64))
           (BExp_Den (BVar "R3" (BType_Imm Bit64))) :
         bir_val_t bir_stmt_basic_t);
        (BStmt_Assign (BVar "R1*" (BType_Imm Bit64))
           (BExp_Den (BVar "R1" (BType_Imm Bit64))) :
         bir_val_t bir_stmt_basic_t);
        (BStmt_Assert
           (BExp_BinExp BIExp_And
              (BExp_BinPred BIExp_LessOrEqual
                 (BExp_Const (Imm64 (2148532224w :word64)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R1*" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R3*" (BType_Imm Bit64)))))
              (BExp_BinPred BIExp_LessThan
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R1*" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R3*" (BType_Imm Bit64))))
                 (BExp_Const (Imm64 (2148794240w :word64))))) :
         bir_val_t bir_stmt_basic_t);
        BStmt_Observe (0 :num) (BExp_Const (Imm1 (1w :word1)))
          [BExp_BinExp BIExp_Plus (BExp_Den (BVar "R1*" (BType_Imm Bit64)))
             (BExp_Den (BVar "R3*" (BType_Imm Bit64)))]
          (HD :bir_val_t list -> bir_val_t );
        BStmt_Observe (1 :num) (BExp_Const (Imm1 (1w :word1)))
          [BExp_BinExp BIExp_Plus (BExp_Den (BVar "R5*" (BType_Imm Bit64)))
             (BExp_Den (BVar "R4*" (BType_Imm Bit64)))]
          (HD :bir_val_t list -> bir_val_t );
        BStmt_Observe (0 :num) (BExp_Const (Imm1 (1w :word1)))
          [BExp_Const (Imm64 (24w :word64))]
          (HD :bir_val_t list -> bir_val_t )];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 (28w :word64))))|>;
   <|bb_label := BL_Address (Imm64 (28w :word64));
     bb_statements :=
       [BStmt_Observe (0 :num) (BExp_Const (Imm1 (1w :word1)))
          [BExp_Const (Imm64 (28w :word64))]
          (HD :bir_val_t list -> bir_val_t )];
     bb_last_statement := BStmt_Halt (BExp_Const (Imm32 (0w :word32)))|>]
:bir_val_t bir_program_t
``;

val prog_5_test =
  ("prog_5 - spectre_v1_mod1", prog_5,
     (prog_5_mem_address_pc,
      prog_5_cache_tag_index,
      prog_5_cache_tag_only,
      prog_5_cache_index_only,
      prog_5_cache_tag_index_part,
      prog_5_cache_tag_index_part_page,
      prog_5_cache_speculation,
      prog_5_cache_speculation_first)
  );
