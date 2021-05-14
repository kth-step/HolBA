(* ========================= prog_4 - xld_br_yld =========================== *)

(*
=================================
	ldr x17, [x16, #8]
	ldr x25, [x4, #16]
	cmp x10, x28
	b.hs #0x8
	ldr x27, [x26, #8]
=================================
*)

val prog_4 = ``
BirProgram
       [<|bb_label :=
            BL_Address_HC (Imm64 (0w :word64))
              "F9400611 (ldr x17, [x16, #8])";
          bb_atomic := F;
          bb_statements :=
            [(BStmt_Assert
                (BExp_Aligned Bit64 (3 :num)
                   (BExp_Den (BVar "R16" (BType_Imm Bit64)))) :
              bir_val_t bir_stmt_basic_t);
             (BStmt_Assign (BVar "R17" (BType_Imm Bit64))
                (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                   (BExp_BinExp BIExp_Plus
                      (BExp_Den (BVar "R16" (BType_Imm Bit64)))
                      (BExp_Const (Imm64 (8w :word64)))) BEnd_LittleEndian
                   Bit64) :bir_val_t bir_stmt_basic_t)];
          bb_last_statement :=
            BStmt_Jmp (BLE_Label (BL_Address (Imm64 (4w :word64))))|>;
        <|bb_label :=
            BL_Address_HC (Imm64 (4w :word64))
              "F9400899 (ldr x25, [x4, #16])";
          bb_atomic := F;
          bb_statements :=
            [(BStmt_Assert
                (BExp_Aligned Bit64 (3 :num)
                   (BExp_Den (BVar "R4" (BType_Imm Bit64)))) :
              bir_val_t bir_stmt_basic_t);
             (BStmt_Assign (BVar "R25" (BType_Imm Bit64))
                (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                   (BExp_BinExp BIExp_Plus
                      (BExp_Den (BVar "R4" (BType_Imm Bit64)))
                      (BExp_Const (Imm64 (16w :word64)))) BEnd_LittleEndian
                   Bit64) :bir_val_t bir_stmt_basic_t)];
          bb_last_statement :=
            BStmt_Jmp (BLE_Label (BL_Address (Imm64 (8w :word64))))|>;
        <|bb_label :=
            BL_Address_HC (Imm64 (8w :word64)) "EB1C015F (cmp x10, x28)";
          bb_atomic := F;
          bb_statements :=
            [(BStmt_Assign (BVar "ProcState_C" BType_Bool)
                (BExp_nzcv_SUB_C (BExp_Den (BVar "R10" (BType_Imm Bit64)))
                   (BExp_Den (BVar "R28" (BType_Imm Bit64)))) :
              bir_val_t bir_stmt_basic_t);
             (BStmt_Assign (BVar "ProcState_N" BType_Bool)
                (BExp_nzcv_SUB_N Bit64
                   (BExp_Den (BVar "R10" (BType_Imm Bit64)))
                   (BExp_Den (BVar "R28" (BType_Imm Bit64)))) :
              bir_val_t bir_stmt_basic_t);
             (BStmt_Assign (BVar "ProcState_V" BType_Bool)
                (BExp_nzcv_SUB_V Bit64
                   (BExp_Den (BVar "R10" (BType_Imm Bit64)))
                   (BExp_Den (BVar "R28" (BType_Imm Bit64)))) :
              bir_val_t bir_stmt_basic_t);
             (BStmt_Assign (BVar "ProcState_Z" BType_Bool)
                (BExp_nzcv_SUB_Z (BExp_Den (BVar "R10" (BType_Imm Bit64)))
                   (BExp_Den (BVar "R28" (BType_Imm Bit64)))) :
              bir_val_t bir_stmt_basic_t)];
          bb_last_statement :=
            BStmt_Jmp (BLE_Label (BL_Address (Imm64 (12w :word64))))|>;
        <|bb_label :=
            BL_Address_HC (Imm64 (12w :word64))
              "54000042 (b.cs 14 <.text+0x14>  // b.hs, b.nlast)";
          bb_atomic := F;
          bb_statements := ([] :bir_val_t bir_stmt_basic_t list );
          bb_last_statement :=
            BStmt_CJmp (BExp_Den (BVar "ProcState_C" BType_Bool))
              (BLE_Label (BL_Address (Imm64 (20w :word64))))
              (BLE_Label (BL_Address (Imm64 (16w :word64))))|>;
        <|bb_label :=
            BL_Address_HC (Imm64 (16w :word64))
              "F940075B (ldr x27, [x26, #8])";
          bb_atomic := F;
          bb_statements :=
            [(BStmt_Assert
                (BExp_Aligned Bit64 (3 :num)
                   (BExp_Den (BVar "R26" (BType_Imm Bit64)))) :
              bir_val_t bir_stmt_basic_t);
             (BStmt_Assign (BVar "R27" (BType_Imm Bit64))
                (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                   (BExp_BinExp BIExp_Plus
                      (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                      (BExp_Const (Imm64 (8w :word64)))) BEnd_LittleEndian
                   Bit64) :bir_val_t bir_stmt_basic_t)];
          bb_last_statement :=
            BStmt_Jmp (BLE_Label (BL_Address (Imm64 (20w :word64))))|>;
        <|bb_label := BL_Address (Imm64 (20w :word64));
          bb_atomic := F;
          bb_statements := ([] :bir_val_t bir_stmt_basic_t list );
          bb_last_statement := BStmt_Halt (BExp_Const (Imm32 (0w :word32)))|>]
:bir_val_t bir_program_t
``;

val prog_4_mem_address_pc = ``
F
``;

val prog_4_cache_tag_index = ``
F
``;

val prog_4_cache_tag_only = ``
F
``;

val prog_4_cache_index_only = ``
F
``;

val prog_4_cache_tag_index_part = ``
F
``;

val prog_4_cache_tag_index_part_page = ``
F
``;

val prog_4_cache_speculation = ``
F
``;

val prog_4_cache_speculation_first = ``
F
``;

val prog_4_test =
  ("prog_4 - xld_br_yld", prog_4,
     (prog_4_mem_address_pc,
      prog_4_cache_tag_index,
      prog_4_cache_tag_only,
      prog_4_cache_index_only,
      prog_4_cache_tag_index_part,
      prog_4_cache_tag_index_part_page,
      prog_4_cache_speculation,
      prog_4_cache_speculation_first)
  );
