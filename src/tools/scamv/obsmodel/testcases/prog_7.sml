(* ========================= prog_7 - test LSPC observations =========================== *)

val prog_7 = ``
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
               (BExp_Store (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                  (BExp_Den (BVar "R17" (BType_Imm Bit64))) BEnd_LittleEndian
                  (BExp_Const (Imm32 (100w :word32))))];
          bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 8w)))|>;
        <|bb_label := BL_Address (Imm64 8w); bb_statements := [];
          bb_last_statement := BStmt_Halt (BExp_Const (Imm32 0w))|>]
:'obs_type bir_program_t
``;

val prog_7_mem_address_pc = ``
F
``;

val prog_7_mem_address_pc_lspc = ``
BirProgram
  [<|bb_label := BL_Address (Imm64 (0w :word64));
     bb_statements :=
       [BStmt_Observe (0 :num) (BExp_Const (Imm1 (1w :word1)))
          [BExp_Const (Imm64 (0w :word64))] gen_LSPC_PC;
        (BStmt_Assert
           (BExp_BinPred BIExp_Equal
              (BExp_BinExp BIExp_And
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R14" (BType_Imm Bit64))))
                 (BExp_Const (Imm64 (7w :word64))))
              (BExp_Const (Imm64 (0w :word64)))) :
         load_store_pc_t bir_stmt_basic_t);
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
         load_store_pc_t bir_stmt_basic_t);
        BStmt_Observe (0 :num) (BExp_Const (Imm1 (1w :word1)))
          [BExp_BinExp BIExp_Plus (BExp_Den (BVar "R24" (BType_Imm Bit64)))
             (BExp_Den (BVar "R14" (BType_Imm Bit64)))] gen_LSPC_Load;
        (BStmt_Assign (BVar "R26" (BType_Imm Bit64))
           (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
              (BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R14" (BType_Imm Bit64)))) BEnd_LittleEndian
              Bit64) :load_store_pc_t bir_stmt_basic_t)];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 (4w :word64))))|>;
   <|bb_label := BL_Address (Imm64 (4w :word64));
     bb_statements :=
       [BStmt_Observe (0 :num) (BExp_Const (Imm1 (1w :word1)))
          [BExp_Const (Imm64 (4w :word64))] gen_LSPC_PC;
        (BStmt_Assert
           (BExp_BinPred BIExp_Equal
              (BExp_BinExp BIExp_And
                 (BExp_Den (BVar "R17" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 (7w :word64))))
              (BExp_Const (Imm64 (0w :word64)))) :
         load_store_pc_t bir_stmt_basic_t);
        (BStmt_Assert
           (BExp_BinExp BIExp_And
              (BExp_BinPred BIExp_LessOrEqual
                 (BExp_Const (Imm64 (0xFFCC0000w :word64)))
                 (BExp_Den (BVar "R17" (BType_Imm Bit64))))
              (BExp_BinPred BIExp_LessThan
                 (BExp_Den (BVar "R17" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 (0xFFCCFF80w :word64))))) :
         load_store_pc_t bir_stmt_basic_t);
        BStmt_Observe (0 :num) (BExp_Const (Imm1 (1w :word1)))
          [BExp_Den (BVar "R17" (BType_Imm Bit64))] gen_LSPC_Store;
        (BStmt_Assign (BVar "R15" (BType_Imm Bit64))
           (BExp_Store (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
              (BExp_Den (BVar "R17" (BType_Imm Bit64))) BEnd_LittleEndian
              (BExp_Const (Imm32 (100w :word32)))) :load_store_pc_t bir_stmt_basic_t)];
     bb_last_statement :=
       BStmt_Jmp (BLE_Label (BL_Address (Imm64 (8w :word64))))|>;
   <|bb_label := BL_Address (Imm64 (8w :word64));
     bb_statements :=
       [BStmt_Observe (0 :num) (BExp_Const (Imm1 (1w :word1)))
          [BExp_Const (Imm64 (8w :word64))] gen_LSPC_PC];
     bb_last_statement := BStmt_Halt (BExp_Const (Imm32 (0w :word32)))|>]
:load_store_pc_t bir_program_t
``;


val prog_7_cache_tag_index = ``
F
``;

val prog_7_cache_tag_only = ``
F
``;

val prog_7_cache_index_only = ``
F
``;

val prog_7_cache_tag_index_part = ``
F
``;

val prog_7_cache_tag_index_part_page = ``
F
``;

val prog_7_cache_speculation = ``
F
``;

val prog_7_cache_speculation_first = ``
F
``;

val prog_7_test =
  ("prog_7 - LSPC test", prog_7,
     (prog_7_mem_address_pc,
      prog_7_mem_address_pc_lspc,
      prog_7_cache_tag_index,
      prog_7_cache_tag_only,
      prog_7_cache_index_only,
      prog_7_cache_tag_index_part,
      prog_7_cache_tag_index_part_page,
      prog_7_cache_speculation,
      prog_7_cache_speculation_first)
  );

