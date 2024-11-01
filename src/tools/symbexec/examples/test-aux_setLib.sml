open HolKernel Parse boolLib bossLib;

open aux_setLib;

val _ = print "start parsing\n";

val birs_state_DIFF_tm = ``{<|bsst_pc :=
          <|bpc_label := BL_Address (Imm32 0x100013B4w); bpc_index := 0|>;
        bsst_environ :=
          birs_gen_env
            [("countw",
              BExp_BinExp BIExp_Plus
                (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
                (BExp_Const (Imm64 (1w + 4w))));
             ("LR",BExp_Const (Imm32 0x100012DDw));
             ("R0",BExp_Den (BVar "sy_R5" (BType_Imm Bit32)));
             ("PSR_Z",
              BExp_BinPred BIExp_Equal
                (BExp_Den (BVar "sy_R5" (BType_Imm Bit32)))
                (BExp_Const (Imm32 0w)));
             ("PSR_N",
              BExp_BinPred BIExp_SignedLessThan
                (BExp_Den (BVar "sy_R5" (BType_Imm Bit32)))
                (BExp_Const (Imm32 0w)));
             ("R11",BExp_Den (BVar "sy_R11" (BType_Imm Bit32)));
             ("R10",BExp_Den (BVar "sy_R10" (BType_Imm Bit32)));
             ("R9",BExp_Den (BVar "sy_R9" (BType_Imm Bit32)));
             ("R8",BExp_Den (BVar "sy_R8" (BType_Imm Bit32)));
             ("R7",BExp_Den (BVar "sy_R7" (BType_Imm Bit32)));
             ("R12",BExp_Den (BVar "sy_R12" (BType_Imm Bit32)));
             ("R5",BExp_Den (BVar "sy_R5" (BType_Imm Bit32)));
             ("R6",BExp_Den (BVar "sy_R6" (BType_Imm Bit32)));
             ("R4",BExp_Den (BVar "sy_R4" (BType_Imm Bit32)));
             ("tmp_PC",BExp_Den (BVar "sy_tmp_PC" (BType_Imm Bit32)));
             ("MEM",BExp_Den (BVar "sy_MEM" (BType_Mem Bit32 Bit8)));
             ("tmp_SP_process",
              BExp_Den (BVar "sy_tmp_SP_process" (BType_Imm Bit32)));
             ("SP_process",BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)));
             ("ModeHandler",BExp_Den (BVar "sy_ModeHandler" (BType_Imm Bit1)));
             ("tmp_PSR_C",BExp_Den (BVar "sy_tmp_PSR_C" (BType_Imm Bit1)));
             ("PSR_V",BExp_Den (BVar "sy_PSR_V" (BType_Imm Bit1)));
             ("R1",BExp_Den (BVar "sy_R1" (BType_Imm Bit32)));
             ("R3",BExp_Den (BVar "sy_R3" (BType_Imm Bit32)));
             ("PSR_C",BExp_Den (BVar "sy_PSR_C" (BType_Imm Bit1)));
             ("R2",BExp_Den (BVar "sy_R2" (BType_Imm Bit32)))];
        bsst_status := BST_Running;
        bsst_pcond :=
          BExp_BinPred BIExp_LessOrEqual
            (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
            (BExp_Const (Imm64 0xFFFFFC1w))|>} DIFF
     {<|bsst_pc :=
          <|bpc_label := BL_Address (Imm32 0x100013B4w); bpc_index := 0|>;
        bsst_environ :=
          birs_gen_env
            [("R11",BExp_Den (BVar "sy_R11" (BType_Imm Bit32)));
             ("R10",BExp_Den (BVar "sy_R10" (BType_Imm Bit32)));
             ("R9",BExp_Den (BVar "sy_R9" (BType_Imm Bit32)));
             ("R8",BExp_Den (BVar "sy_R8" (BType_Imm Bit32)));
             ("R7",BExp_Den (BVar "sy_R7" (BType_Imm Bit32)));
             ("R12",BExp_Den (BVar "sy_R12" (BType_Imm Bit32)));
             ("R5",BExp_Den (BVar "sy_R5" (BType_Imm Bit32)));
             ("R6",BExp_Den (BVar "sy_R6" (BType_Imm Bit32)));
             ("R4",BExp_Den (BVar "sy_R4" (BType_Imm Bit32)));
             ("tmp_PC",BExp_Den (BVar "sy_tmp_PC" (BType_Imm Bit32)));
             ("MEM",BExp_Den (BVar "sy_MEM" (BType_Mem Bit32 Bit8)));
             ("tmp_SP_process",
              BExp_Den (BVar "sy_tmp_SP_process" (BType_Imm Bit32)));
             ("SP_process",BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)));
             ("ModeHandler",BExp_Den (BVar "sy_ModeHandler" (BType_Imm Bit1)));
             ("LR",BExp_Const (Imm32 0x100012DDw));
             ("tmp_PSR_C",BExp_Den (BVar "sy_tmp_PSR_C" (BType_Imm Bit1)));
             ("PSR_V",BExp_Den (BVar "sy_PSR_V" (BType_Imm Bit1)));
             ("R1",BExp_Den (BVar "sy_R1" (BType_Imm Bit32)));
             ("R3",BExp_Den (BVar "sy_R3" (BType_Imm Bit32)));
             ("PSR_C",BExp_Den (BVar "sy_PSR_C" (BType_Imm Bit1)));
             ("R0",BExp_Den (BVar "sy_R5" (BType_Imm Bit32)));
             ("R2",BExp_Den (BVar "sy_R2" (BType_Imm Bit32)));
             ("PSR_Z",
              BExp_BinPred BIExp_Equal
                (BExp_Den (BVar "sy_R5" (BType_Imm Bit32)))
                (BExp_Const (Imm32 0w)));
             ("PSR_N",
              BExp_BinPred BIExp_SignedLessThan
                (BExp_Den (BVar "sy_R5" (BType_Imm Bit32)))
                (BExp_Const (Imm32 0w)));
             ("countw",
              BExp_BinExp BIExp_Plus
                (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
                (BExp_Const (Imm64 (1w + 4w))))]; bsst_status := BST_Running;
        bsst_pcond :=
          BExp_BinPred BIExp_LessOrEqual
            (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
            (BExp_Const (Imm64 0xFFFFFC1w))|>}``;


val birs_state_DIFF_UNION_tm = ``{<|bsst_pc :=
          <|bpc_label := BL_Address (Imm32 0x100013B4w); bpc_index := 0|>;
        bsst_environ :=
          birs_gen_env
            [("countw",
              BExp_BinExp BIExp_Plus
                (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
                (BExp_Const (Imm64 (1w + 4w))));
             ("LR",BExp_Const (Imm32 0x100012DDw));
             ("R0",BExp_Den (BVar "sy_R5" (BType_Imm Bit32)));
             ("PSR_Z",
              BExp_BinPred BIExp_Equal
                (BExp_Den (BVar "sy_R5" (BType_Imm Bit32)))
                (BExp_Const (Imm32 0w)));
             ("PSR_N",
              BExp_BinPred BIExp_SignedLessThan
                (BExp_Den (BVar "sy_R5" (BType_Imm Bit32)))
                (BExp_Const (Imm32 0w)));
             ("R11",BExp_Den (BVar "sy_R11" (BType_Imm Bit32)));
             ("R10",BExp_Den (BVar "sy_R10" (BType_Imm Bit32)));
             ("R9",BExp_Den (BVar "sy_R9" (BType_Imm Bit32)));
             ("R8",BExp_Den (BVar "sy_R8" (BType_Imm Bit32)));
             ("R7",BExp_Den (BVar "sy_R7" (BType_Imm Bit32)));
             ("R12",BExp_Den (BVar "sy_R12" (BType_Imm Bit32)));
             ("R5",BExp_Den (BVar "sy_R5" (BType_Imm Bit32)));
             ("R6",BExp_Den (BVar "sy_R6" (BType_Imm Bit32)));
             ("R4",BExp_Den (BVar "sy_R4" (BType_Imm Bit32)));
             ("tmp_PC",BExp_Den (BVar "sy_tmp_PC" (BType_Imm Bit32)));
             ("MEM",BExp_Den (BVar "sy_MEM" (BType_Mem Bit32 Bit8)));
             ("tmp_SP_process",
              BExp_Den (BVar "sy_tmp_SP_process" (BType_Imm Bit32)));
             ("SP_process",BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)));
             ("ModeHandler",BExp_Den (BVar "sy_ModeHandler" (BType_Imm Bit1)));
             ("tmp_PSR_C",BExp_Den (BVar "sy_tmp_PSR_C" (BType_Imm Bit1)));
             ("PSR_V",BExp_Den (BVar "sy_PSR_V" (BType_Imm Bit1)));
             ("R1",BExp_Den (BVar "sy_R1" (BType_Imm Bit32)));
             ("R3",BExp_Den (BVar "sy_R3" (BType_Imm Bit32)));
             ("PSR_C",BExp_Den (BVar "sy_PSR_C" (BType_Imm Bit1)));
             ("R2",BExp_Den (BVar "sy_R2" (BType_Imm Bit32)))];
        bsst_status := BST_Running;
        bsst_pcond :=
          BExp_BinPred BIExp_LessOrEqual
            (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
            (BExp_Const (Imm64 0xFFFFFC1w))|>} DIFF
     {<|bsst_pc :=
          <|bpc_label := BL_Address (Imm32 0x100013B4w); bpc_index := 0|>;
        bsst_environ :=
          birs_gen_env
            [("R11",BExp_Den (BVar "sy_R11" (BType_Imm Bit32)));
             ("R10",BExp_Den (BVar "sy_R10" (BType_Imm Bit32)));
             ("R9",BExp_Den (BVar "sy_R9" (BType_Imm Bit32)));
             ("R8",BExp_Den (BVar "sy_R8" (BType_Imm Bit32)));
             ("R7",BExp_Den (BVar "sy_R7" (BType_Imm Bit32)));
             ("R12",BExp_Den (BVar "sy_R12" (BType_Imm Bit32)));
             ("R5",BExp_Den (BVar "sy_R5" (BType_Imm Bit32)));
             ("R6",BExp_Den (BVar "sy_R6" (BType_Imm Bit32)));
             ("R4",BExp_Den (BVar "sy_R4" (BType_Imm Bit32)));
             ("tmp_PC",BExp_Den (BVar "sy_tmp_PC" (BType_Imm Bit32)));
             ("MEM",BExp_Den (BVar "sy_MEM" (BType_Mem Bit32 Bit8)));
             ("tmp_SP_process",
              BExp_Den (BVar "sy_tmp_SP_process" (BType_Imm Bit32)));
             ("SP_process",BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)));
             ("ModeHandler",BExp_Den (BVar "sy_ModeHandler" (BType_Imm Bit1)));
             ("LR",BExp_Const (Imm32 0x100012DDw));
             ("tmp_PSR_C",BExp_Den (BVar "sy_tmp_PSR_C" (BType_Imm Bit1)));
             ("PSR_V",BExp_Den (BVar "sy_PSR_V" (BType_Imm Bit1)));
             ("R1",BExp_Den (BVar "sy_R1" (BType_Imm Bit32)));
             ("R3",BExp_Den (BVar "sy_R3" (BType_Imm Bit32)));
             ("PSR_C",BExp_Den (BVar "sy_PSR_C" (BType_Imm Bit1)));
             ("R0",BExp_Den (BVar "sy_R5" (BType_Imm Bit32)));
             ("R2",BExp_Den (BVar "sy_R2" (BType_Imm Bit32)));
             ("PSR_Z",
              BExp_BinPred BIExp_Equal
                (BExp_Den (BVar "sy_R5" (BType_Imm Bit32)))
                (BExp_Const (Imm32 0w)));
             ("PSR_N",
              BExp_BinPred BIExp_SignedLessThan
                (BExp_Den (BVar "sy_R5" (BType_Imm Bit32)))
                (BExp_Const (Imm32 0w)));
             ("countw",
              BExp_BinExp BIExp_Plus
                (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
                (BExp_Const (Imm64 (1w + 4w))))]; bsst_status := BST_Running;
        bsst_pcond :=
          BExp_BinPred BIExp_LessOrEqual
            (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
            (BExp_Const (Imm64 0xFFFFFC1w))|>} ∪
     {<|bsst_pc :=
          <|bpc_label := BL_Address (Imm32 0x100013DCw); bpc_index := 0|>;
        bsst_environ :=
          birs_gen_env
            [("tmp_PSR_C",BExp_Den (BVar "sy_tmp_PSR_C" (BType_Imm Bit1)));
             ("LR",BExp_Const (Imm32 0x100012DDw));
             ("ModeHandler",BExp_Den (BVar "sy_ModeHandler" (BType_Imm Bit1)));
             ("SP_process",BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)));
             ("tmp_SP_process",
              BExp_Den (BVar "sy_tmp_SP_process" (BType_Imm Bit32)));
             ("MEM",BExp_Den (BVar "sy_MEM" (BType_Mem Bit32 Bit8)));
             ("tmp_PC",BExp_Den (BVar "sy_tmp_PC" (BType_Imm Bit32)));
             ("R4",BExp_Den (BVar "sy_R4" (BType_Imm Bit32)));
             ("R6",BExp_Den (BVar "sy_R6" (BType_Imm Bit32)));
             ("R5",BExp_Den (BVar "sy_R5" (BType_Imm Bit32)));
             ("R12",BExp_Den (BVar "sy_R12" (BType_Imm Bit32)));
             ("R7",BExp_Den (BVar "sy_R7" (BType_Imm Bit32)));
             ("R8",BExp_Den (BVar "sy_R8" (BType_Imm Bit32)));
             ("R9",BExp_Den (BVar "sy_R9" (BType_Imm Bit32)));
             ("R10",BExp_Den (BVar "sy_R10" (BType_Imm Bit32)));
             ("R11",BExp_Den (BVar "sy_R11" (BType_Imm Bit32)));
             ("R3",
              BExp_BinExp BIExp_RightShift
                (BExp_BinExp BIExp_RightShift
                   (BExp_BinExp BIExp_LeftShift (BExp_Const (Imm32 1w))
                      (BExp_Const (Imm32 16w))) (BExp_Const (Imm32 8w)))
                (BExp_Const (Imm32 4w)));
             ("R1",BExp_Den (BVar "syr_0" (BType_Imm Bit32)));
             ("R2",BExp_Const (Imm32 0x100013DEw));
             ("PSR_C",BExp_Den (BVar "syr_1" (BType_Imm Bit1)));
             ("PSR_N",BExp_Den (BVar "syr_2" (BType_Imm Bit1)));
             ("PSR_V",BExp_Den (BVar "syr_3" (BType_Imm Bit1)));
             ("PSR_Z",BExp_Den (BVar "syr_4" (BType_Imm Bit1)));
             ("R0",BExp_Den (BVar "syr_5" (BType_Imm Bit32)));
             ("countw",BExp_Den (BVar "syr_6" (BType_Imm Bit64)))];
        bsst_status := BST_Running;
        bsst_pcond :=
          BExp_BinPred BIExp_LessOrEqual
            (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
            (BExp_Const (Imm64 0xFFFFFC1w))|>}``;

val DIFF_UNION_thm = birs_state_DIFF_UNION_CONV birs_state_DIFF_UNION_tm;
val _ = print "finished DIFF_UNION_CONV\n";

val DIFF_thm = (DIFF_CONV birs_state_EQ_CONV) birs_state_DIFF_tm;
val _ = print "finished DIFF_CONV\n";

