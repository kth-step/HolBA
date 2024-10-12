open HolKernel Parse boolLib bossLib;


val taut_inputs = [
  (``BExp_BinExp BIExp_Or
        (BExp_UnaryExp BIExp_Not
            (BExp_BinExp BIExp_And
                (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_And
                        (BExp_BinExp BIExp_And
                            (BExp_BinExp BIExp_And
                                (BExp_BinPred BIExp_Equal
                                (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
                                (BExp_Const (Imm64 pre_countw)))
                                (BExp_BinPred BIExp_LessOrEqual
                                (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
                                (BExp_Const (Imm64 0xFFFFFEBw))))
                            (BExp_Den (BVar "syp_gen" (BType_Imm Bit1))))
                        (BExp_BinPred BIExp_LessOrEqual
                            (BExp_BinExp BIExp_LeftShift (BExp_Const (Imm32 1w))
                                (BExp_Const (Imm32 16w)))
                            (BExp_Den (BVar "sy_R0" (BType_Imm Bit32)))))
                    (BExp_BinPred BIExp_LessOrEqual
                        (BExp_BinExp BIExp_RightShift
                            (BExp_BinExp BIExp_LeftShift (BExp_Const (Imm32 1w))
                                (BExp_Const (Imm32 16w))) (BExp_Const (Imm32 8w)))
                        (BExp_BinExp BIExp_RightShift
                            (BExp_Den (BVar "sy_R0" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 16w)))))
                    (BExp_BinPred BIExp_LessOrEqual
                    (BExp_BinExp BIExp_RightShift
                        (BExp_BinExp BIExp_RightShift
                            (BExp_BinExp BIExp_LeftShift (BExp_Const (Imm32 1w))
                                (BExp_Const (Imm32 16w))) (BExp_Const (Imm32 8w)))
                        (BExp_Const (Imm32 4w)))
                    (BExp_BinExp BIExp_RightShift
                        (BExp_BinExp BIExp_RightShift
                            (BExp_Den (BVar "sy_R0" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 16w))) (BExp_Const (Imm32 8w)))))
                (BExp_BinPred BIExp_Equal (BExp_Den (BVar "syf_1" (BType_Imm Bit1)))
                    (BExp_BinPred BIExp_Equal
                    (BExp_Cast BIExp_UnsignedCast
                        (BExp_Load (BExp_Den (BVar "sy_MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_BinExp BIExp_Plus
                                (BExp_BinExp BIExp_RightShift
                                (BExp_BinExp BIExp_RightShift
                                    (BExp_BinExp BIExp_RightShift
                                        (BExp_Den (BVar "sy_R0" (BType_Imm Bit32)))
                                        (BExp_Const (Imm32 16w)))
                                    (BExp_Const (Imm32 8w))) (BExp_Const (Imm32 4w)))
                                (BExp_Const (Imm32 0x100013DEw))) BEnd_LittleEndian Bit8)
                        Bit32)
                    (BExp_UnaryExp BIExp_ChangeSign
                        (BExp_BinExp BIExp_Minus
                            (BExp_BinExp BIExp_Minus
                                (BExp_BinExp BIExp_Minus (BExp_Const (Imm32 28w))
                                (BExp_Const (Imm32 16w))) (BExp_Const (Imm32 8w)))
                            (BExp_Const (Imm32 4w))))))))
        (BExp_BinExp BIExp_And
            (BExp_BinExp BIExp_And
                (BExp_BinExp BIExp_And
                (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_And
                        (BExp_BinPred BIExp_Equal
                            (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 pre_countw)))
                        (BExp_BinPred BIExp_LessOrEqual
                            (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 0xFFFFFEBw))))
                    (BExp_Den (BVar "syp_gen" (BType_Imm Bit1))))
                (BExp_BinPred BIExp_LessOrEqual
                    (BExp_BinExp BIExp_LeftShift (BExp_Const (Imm32 1w))
                        (BExp_Const (Imm32 16w)))
                    (BExp_Den (BVar "sy_R0" (BType_Imm Bit32)))))
                (BExp_BinPred BIExp_LessOrEqual
                (BExp_BinExp BIExp_RightShift
                    (BExp_BinExp BIExp_LeftShift (BExp_Const (Imm32 1w))
                        (BExp_Const (Imm32 16w))) (BExp_Const (Imm32 8w)))
                (BExp_BinExp BIExp_RightShift
                    (BExp_Den (BVar "sy_R0" (BType_Imm Bit32)))
                    (BExp_Const (Imm32 16w)))))
            (BExp_BinPred BIExp_LessOrEqual
                (BExp_BinExp BIExp_RightShift
                (BExp_BinExp BIExp_RightShift
                    (BExp_BinExp BIExp_LeftShift (BExp_Const (Imm32 1w))
                        (BExp_Const (Imm32 16w))) (BExp_Const (Imm32 8w)))
                (BExp_Const (Imm32 4w)))
                (BExp_BinExp BIExp_RightShift
                (BExp_BinExp BIExp_RightShift
                    (BExp_Den (BVar "sy_R0" (BType_Imm Bit32)))
                    (BExp_Const (Imm32 16w))) (BExp_Const (Imm32 8w)))))``, true),

  (``BExp_BinExp BIExp_Or
        (BExp_UnaryExp BIExp_Not
            (BExp_BinExp BIExp_And
                (BExp_BinPred BIExp_Equal
                    (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 pre_countw)))
                (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 0xFFFFFEBw)))))
        (BExp_BinExp BIExp_And
            (BExp_BinExp BIExp_And
                (BExp_BinPred BIExp_Equal
                (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 (1w + 4w)))) (BExp_Const (Imm64 pre_countw)))
                (BExp_BinPred BIExp_LessOrEqual
                (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 (1w + 4w)))) (BExp_Const (Imm64 0xFFFFFEBw))))
            (BExp_BinExp BIExp_And
                (BExp_BinPred BIExp_Equal
                (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
                (BExp_Const (Imm64 pre_countw)))
                (BExp_BinPred BIExp_LessOrEqual
                (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
                (BExp_Const (Imm64 0xFFFFFEBw)))))``, false),

  (``BExp_BinExp BIExp_Or
        (BExp_UnaryExp BIExp_Not
            (BExp_BinExp BIExp_And
                (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_And
                        (BExp_BinExp BIExp_And
                            (BExp_BinExp BIExp_And
                                (BExp_BinPred BIExp_Equal
                                (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
                                (BExp_Const (Imm64 pre_countw)))
                                (BExp_BinPred BIExp_LessOrEqual
                                (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
                                (BExp_Const (Imm64 0xFFFFFEBw))))
                            (BExp_Den (BVar "syp_gen" (BType_Imm Bit1))))
                        (BExp_BinPred BIExp_LessOrEqual
                            (BExp_BinExp BIExp_LeftShift (BExp_Const (Imm32 1w))
                                (BExp_Const (Imm32 16w)))
                            (BExp_Den (BVar "sy_R0" (BType_Imm Bit32)))))
                    (BExp_BinPred BIExp_LessOrEqual
                        (BExp_BinExp BIExp_RightShift
                            (BExp_BinExp BIExp_LeftShift (BExp_Const (Imm32 1w))
                                (BExp_Const (Imm32 16w))) (BExp_Const (Imm32 8w)))
                        (BExp_BinExp BIExp_RightShift
                            (BExp_Den (BVar "sy_R0" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 16w)))))
                    (BExp_BinPred BIExp_LessOrEqual
                    (BExp_BinExp BIExp_RightShift
                        (BExp_BinExp BIExp_RightShift
                            (BExp_BinExp BIExp_LeftShift (BExp_Const (Imm32 1w))
                                (BExp_Const (Imm32 16w))) (BExp_Const (Imm32 8w)))
                        (BExp_Const (Imm32 4w)))
                    (BExp_BinExp BIExp_RightShift
                        (BExp_BinExp BIExp_RightShift
                            (BExp_Den (BVar "sy_R0" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 16w))) (BExp_Const (Imm32 8w)))))
                (BExp_BinPred BIExp_Equal (BExp_Den (BVar "syf_4" (BType_Imm Bit1)))
                    (BExp_BinPred BIExp_LessThan
                    (BExp_UnaryExp BIExp_Not
                        (BExp_BinExp BIExp_Minus
                            (BExp_BinExp BIExp_Minus
                                (BExp_BinExp BIExp_Minus (BExp_Const (Imm32 28w))
                                (BExp_Const (Imm32 16w))) (BExp_Const (Imm32 8w)))
                            (BExp_Const (Imm32 4w))))
                    (BExp_Cast BIExp_UnsignedCast
                        (BExp_Load (BExp_Den (BVar "sy_MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_BinExp BIExp_Plus
                                (BExp_BinExp BIExp_RightShift
                                (BExp_BinExp BIExp_RightShift
                                    (BExp_BinExp BIExp_RightShift
                                        (BExp_Den (BVar "sy_R0" (BType_Imm Bit32)))
                                        (BExp_Const (Imm32 16w)))
                                    (BExp_Const (Imm32 8w))) (BExp_Const (Imm32 4w)))
                                (BExp_Const (Imm32 0x100013DEw))) BEnd_LittleEndian Bit8)
                        Bit32)))))
        (BExp_BinExp BIExp_And
            (BExp_BinExp BIExp_And
                (BExp_BinExp BIExp_And
                (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_And
                        (BExp_BinPred BIExp_Equal
                            (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 pre_countw)))
                        (BExp_BinPred BIExp_LessOrEqual
                            (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 0xFFFFFEBw))))
                    (BExp_Den (BVar "syp_gen" (BType_Imm Bit1))))
                (BExp_BinPred BIExp_LessOrEqual
                    (BExp_BinExp BIExp_LeftShift (BExp_Const (Imm32 1w))
                        (BExp_Const (Imm32 16w)))
                    (BExp_Den (BVar "sy_R0" (BType_Imm Bit32)))))
                (BExp_BinPred BIExp_LessOrEqual
                (BExp_BinExp BIExp_RightShift
                    (BExp_BinExp BIExp_LeftShift (BExp_Const (Imm32 1w))
                        (BExp_Const (Imm32 16w))) (BExp_Const (Imm32 8w)))
                (BExp_BinExp BIExp_RightShift
                    (BExp_Den (BVar "sy_R0" (BType_Imm Bit32)))
                    (BExp_Const (Imm32 16w)))))
            (BExp_BinPred BIExp_LessOrEqual
                (BExp_BinExp BIExp_RightShift
                (BExp_BinExp BIExp_RightShift
                    (BExp_BinExp BIExp_LeftShift (BExp_Const (Imm32 1w))
                        (BExp_Const (Imm32 16w))) (BExp_Const (Imm32 8w)))
                (BExp_Const (Imm32 4w)))
                (BExp_BinExp BIExp_RightShift
                (BExp_BinExp BIExp_RightShift
                    (BExp_Den (BVar "sy_R0" (BType_Imm Bit32)))
                    (BExp_Const (Imm32 16w))) (BExp_Const (Imm32 8w)))))``, true)
];

val _ = holba_z3Lib.debug_print := true;

val _ = List.map (fn (inputexp, expected_output) =>
    if bir_smtLib.bir_smt_check_taut false inputexp = expected_output then ()
      else raise Fail "wrong output"
  ) taut_inputs;
