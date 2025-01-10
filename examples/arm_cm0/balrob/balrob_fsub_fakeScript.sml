open HolKernel Parse boolLib bossLib;

open balrob_supportLib;

open balrob_endsTheory;

val _ = new_theory "balrob_fsub_fake";

val symb_exec_thm = prove(``birs_symb_exec ^((lhs o concl) balrobLib.bir_balrob_prog_def)
          (<|bsst_pc :=
               <|bpc_label := BL_Address (Imm32 0x10000E50w);
                 bpc_index := 0|>;
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
                  ("SP_process",
                   BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)));
                  ("ModeHandler",
                   BExp_Den (BVar "sy_ModeHandler" (BType_Imm Bit1)));
                  ("LR",BExp_Den (BVar "sy_LR" (BType_Imm Bit32)));
                  ("tmp_PSR_C",
                   BExp_Den (BVar "sy_tmp_PSR_C" (BType_Imm Bit1)));
                  ("PSR_V",BExp_Den (BVar "sy_PSR_V" (BType_Imm Bit1)));
                  ("R1",BExp_Den (BVar "sy_R1" (BType_Imm Bit32)));
                  ("R3",BExp_Den (BVar "sy_R3" (BType_Imm Bit32)));
                  ("PSR_C",BExp_Den (BVar "sy_PSR_C" (BType_Imm Bit1)));
                  ("R0",BExp_Den (BVar "sy_R0" (BType_Imm Bit32)));
                  ("R2",BExp_Den (BVar "sy_R2" (BType_Imm Bit32)));
                  ("PSR_Z",BExp_Den (BVar "sy_PSR_Z" (BType_Imm Bit1)));
                  ("PSR_N",BExp_Den (BVar "sy_PSR_N" (BType_Imm Bit1)));
                  ("countw",BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))];
             bsst_status := BST_Running;
             bsst_pcond :=
               BExp_BinExp BIExp_And
                 (BExp_BinExp BIExp_And
                    (BExp_UnaryExp BIExp_Not
                       (BExp_Den (BVar "sy_ModeHandler" (BType_Imm Bit1))))
                    (BExp_BinExp BIExp_And
                       (BExp_BinPred BIExp_Equal
                          (BExp_BinExp BIExp_And
                             (BExp_Den
                                (BVar "sy_SP_process" (BType_Imm Bit32)))
                             (BExp_Const (Imm32 3w)))
                          (BExp_Const (Imm32 0w)))
                       (BExp_BinExp BIExp_And
                          (BExp_BinExp BIExp_And
                             (BExp_BinPred BIExp_LessThan
                                (BExp_Const (Imm32 0x10001F38w))
                                (BExp_Den
                                   (BVar "sy_SP_process" (BType_Imm Bit32))))
                             (BExp_BinPred BIExp_LessOrEqual
                                (BExp_Den
                                   (BVar "sy_SP_process" (BType_Imm Bit32)))
                                (BExp_Const (Imm32 0x10001FF0w))))
                          (BExp_BinPred BIExp_LessOrEqual
                             (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
                             (BExp_Const (Imm64 0xFFFFF45w))))))
                 (BExp_Den (BVar "syp_gen" (BType_Imm Bit1)))|>,
           {<|bpc_label := BL_Label "cheated"; bpc_index := 0|>},
           {<|bsst_pc :=
                <|bpc_label := BL_Address (Imm32 0x10000F14w);
                  bpc_index := 0|>;
              bsst_environ :=
                birs_gen_env
                  [("countw",BExp_Den (BVar "syi_countw" (BType_Imm Bit64)));
                   ("R9",BExp_Den (BVar "sy_R9" (BType_Imm Bit32)));
                   ("R8",BExp_Den (BVar "sy_R8" (BType_Imm Bit32)));
                   ("SP_process",
                    BExp_BinExp BIExp_Minus
                      (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)))
                      (BExp_Const (Imm32 24w)));
                   ("R3",BExp_Den (BVar "sy_R9" (BType_Imm Bit32)));
                   ("R2",BExp_Den (BVar "sy_R8" (BType_Imm Bit32)));
                   ("R0",BExp_Den (BVar "syf_1359" (BType_Imm Bit32)));
                   ("PSR_Z",BExp_Den (BVar "syf_1358" (BType_Imm Bit1)));
                   ("PSR_N",BExp_Den (BVar "syf_1357" (BType_Imm Bit1)));
                   ("PSR_C",BExp_Den (BVar "syf_1356" (BType_Imm Bit1)));
                   ("R4",BExp_Den (BVar "syf_1355" (BType_Imm Bit32)));
                   ("PSR_V",BExp_Den (BVar "syf_1354" (BType_Imm Bit1)));
                   ("R6",BExp_Den (BVar "syf_1353" (BType_Imm Bit32)));
                   ("R1",BExp_Den (BVar "syf_1352" (BType_Imm Bit32)));
                   ("R11",BExp_Den (BVar "sy_R11" (BType_Imm Bit32)));
                   ("R10",BExp_Den (BVar "sy_R10" (BType_Imm Bit32)));
                   ("R7",
                    BExp_BinExp BIExp_RightShift
                      (BExp_BinExp BIExp_LeftShift
                         (BExp_Den (BVar "sy_R0" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 9w))) (BExp_Const (Imm32 9w)));
                   ("R12",
                    BExp_BinExp BIExp_RightShift
                      (BExp_BinExp BIExp_LeftShift
                         (BExp_Den (BVar "sy_R1" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 9w))) (BExp_Const (Imm32 9w)));
                   ("R5",BExp_Den (BVar "syf_1351" (BType_Imm Bit32)));
                   ("tmp_PC",BExp_Den (BVar "sy_tmp_PC" (BType_Imm Bit32)));
                   ("MEM",
                    BExp_Store
                      (BExp_Store
                         (BExp_Store
                            (BExp_Store
                               (BExp_Store
                                  (BExp_Store
                                     (BExp_Store
                                        (BExp_Store
                                           (BExp_Den
                                              (BVar "sy_MEM"
                                                 (BType_Mem Bit32 Bit8)))
                                           (BExp_BinExp BIExp_Minus
                                              (BExp_Den
                                                 (BVar "sy_SP_process"
                                                    (BType_Imm Bit32)))
                                              (BExp_Const (Imm32 24w)))
                                           BEnd_LittleEndian
                                           (BExp_Den
                                              (BVar "sy_R3"
                                                 (BType_Imm Bit32))))
                                        (BExp_BinExp BIExp_Minus
                                           (BExp_Den
                                              (BVar "sy_SP_process"
                                                 (BType_Imm Bit32)))
                                           (BExp_Const (Imm32 20w)))
                                        BEnd_LittleEndian
                                        (BExp_Den
                                           (BVar "sy_R4" (BType_Imm Bit32))))
                                     (BExp_BinExp BIExp_Minus
                                        (BExp_Den
                                           (BVar "sy_SP_process"
                                              (BType_Imm Bit32)))
                                        (BExp_Const (Imm32 16w)))
                                     BEnd_LittleEndian
                                     (BExp_Den
                                        (BVar "sy_R5" (BType_Imm Bit32))))
                                  (BExp_BinExp BIExp_Minus
                                     (BExp_Den
                                        (BVar "sy_SP_process"
                                           (BType_Imm Bit32)))
                                     (BExp_Const (Imm32 12w)))
                                  BEnd_LittleEndian
                                  (BExp_Den
                                     (BVar "sy_R6" (BType_Imm Bit32))))
                               (BExp_BinExp BIExp_Minus
                                  (BExp_Den
                                     (BVar "sy_SP_process"
                                        (BType_Imm Bit32)))
                                  (BExp_Const (Imm32 8w)))
                               BEnd_LittleEndian
                               (BExp_Den (BVar "sy_R7" (BType_Imm Bit32))))
                            (BExp_BinExp BIExp_Minus
                               (BExp_Den
                                  (BVar "sy_SP_process" (BType_Imm Bit32)))
                               (BExp_Const (Imm32 4w))) BEnd_LittleEndian
                            (BExp_Den (BVar "sy_LR" (BType_Imm Bit32))))
                         (BExp_BinExp BIExp_Minus
                            (BExp_BinExp BIExp_Minus
                               (BExp_Den
                                  (BVar "sy_SP_process" (BType_Imm Bit32)))
                               (BExp_Const (Imm32 24w)))
                            (BExp_Const (Imm32 8w))) BEnd_LittleEndian
                         (BExp_Den (BVar "sy_R8" (BType_Imm Bit32))))
                      (BExp_BinExp BIExp_Minus
                         (BExp_BinExp BIExp_Minus
                            (BExp_Den
                               (BVar "sy_SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 24w)))
                         (BExp_Const (Imm32 4w))) BEnd_LittleEndian
                      (BExp_Den (BVar "sy_R9" (BType_Imm Bit32))));
                   ("tmp_SP_process",
                    BExp_BinExp BIExp_Minus
                      (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)))
                      (BExp_Const (Imm32 32w)));
                   ("ModeHandler",
                    BExp_Den (BVar "sy_ModeHandler" (BType_Imm Bit1)));
                   ("LR",BExp_Den (BVar "syf_1350" (BType_Imm Bit32)));
                   ("tmp_PSR_C",BExp_Den (BVar "syf_1349" (BType_Imm Bit1)))];
              bsst_status := BST_Running;
              bsst_pcond :=
                BExp_BinExp BIExp_And
                  (BExp_IntervalPred
                     (BExp_Den (BVar "syi_countw" (BType_Imm Bit64)))
                     (BExp_BinExp BIExp_Plus
                        (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
                        (BExp_Const (Imm64 69w)),
                      BExp_BinExp BIExp_Plus
                        (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
                        (BExp_Const (Imm64 187w))))
                  (BExp_BinExp BIExp_And
                     (BExp_UnaryExp BIExp_Not
                        (BExp_Den (BVar "sy_ModeHandler" (BType_Imm Bit1))))
                     (BExp_BinExp BIExp_And
                        (BExp_BinPred BIExp_Equal
                           (BExp_BinExp BIExp_And
                              (BExp_Den
                                 (BVar "sy_SP_process" (BType_Imm Bit32)))
                              (BExp_Const (Imm32 3w)))
                           (BExp_Const (Imm32 0w)))
                        (BExp_BinExp BIExp_And
                           (BExp_BinPred BIExp_LessThan
                              (BExp_Const (Imm32 0x10001F38w))
                              (BExp_Den
                                 (BVar "sy_SP_process" (BType_Imm Bit32))))
                           (BExp_BinExp BIExp_And
                              (BExp_BinPred BIExp_LessOrEqual
                                 (BExp_Den
                                    (BVar "sy_SP_process" (BType_Imm Bit32)))
                                 (BExp_Const (Imm32 0x10001FF0w)))
                              (BExp_BinExp BIExp_And
                                 (BExp_BinPred BIExp_LessOrEqual
                                    (BExp_Den
                                       (BVar "sy_countw" (BType_Imm Bit64)))
                                    (BExp_Const (Imm64 0xFFFFF45w)))
                                 (BExp_Den
                                    (BVar "syp_gen" (BType_Imm Bit1))))))))|>})``, cheat);

val entry_name = "__aeabi_fsub";
val _ = save_thm("balrob_summary_" ^ entry_name ^ "_thm", symb_exec_thm);

val _ = export_theory ();
