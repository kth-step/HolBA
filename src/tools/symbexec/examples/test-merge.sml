open HolKernel Parse boolLib bossLib;
open birs_mergeLib;
open birsSyntax;

val thm_test1 = aux_moveawayLib.mk_oracle_preserve_tags [] "TESTFILE" ``
  birs_symb_exec prog (<|bsst_pc :=
               <|bpc_label := BL_Address (Imm32 0x0w);
                 bpc_index := 0|>;
             bsst_environ :=
               birs_gen_env
                 [("x",BExp_Den (BVar "sy_x" (BType_Imm Bit32)));
                  ("y",BExp_Den (BVar "sy_y" (BType_Imm Bit8)));
                  ("MEM",BExp_Den (BVar "sy_MEM" (BType_Mem Bit32 Bit8)));];
             bsst_status := BST_Running;
             bsst_pcond :=
               BExp_BinExp BIExp_And
                    (BExp_BinPred BIExp_Equal
                        (BExp_BinExp BIExp_And
                            (BExp_Den (BVar "sy_x" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 3w)))
                        (BExp_Const (Imm32 0w)))
                    (BExp_Den (BVar "syp_gen" (BType_Imm Bit1)))|>,
           {<|bpc_label := BL_Label "xyz"; bpc_index := 0|>},
           {<|bsst_pc :=
                <|bpc_label := BL_Address (Imm32 0x10w);
                  bpc_index := 0|>;
              bsst_environ :=
                birs_gen_env
                  [("MEM",BExp_Den (BVar "sy_MEM" (BType_Mem Bit32 Bit8)));
                   ("x",
                    BExp_BinExp BIExp_Plus
                        (BExp_Den (BVar "sy_x" (BType_Imm Bit32)))
                        (BExp_Const (Imm32 16w)));
                   ("y",BExp_Den (BVar "sy_y" (BType_Imm Bit8)))];
              bsst_status := BST_Running;
              bsst_pcond :=
                BExp_BinExp BIExp_And
                  (BExp_Den (BVar "syp_gen" (BType_Imm Bit1)))
                    (BExp_BinPred BIExp_Equal
                        (BExp_BinExp BIExp_And
                            (BExp_Den (BVar "sy_x" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 3w)))
                        (BExp_Const (Imm32 0w)))|>;
           <|bsst_pc :=
                <|bpc_label := BL_Address (Imm32 0x10w);
                  bpc_index := 0|>;
              bsst_environ :=
                birs_gen_env
                  [("MEM",BExp_Den (BVar "sy_MEM" (BType_Mem Bit32 Bit8)));
                   ("x",
                    BExp_BinExp BIExp_Plus
                        (BExp_Den (BVar "sy_x" (BType_Imm Bit32)))
                        (BExp_Const (Imm32 32w)));
                   ("y",BExp_Den (BVar "sy_y" (BType_Imm Bit8)))];
              bsst_status := BST_Running;
              bsst_pcond :=
                BExp_BinExp BIExp_And
                    (BExp_Den (BVar "syp_gen" (BType_Imm Bit1)))
                    (BExp_BinExp BIExp_And
                        (BExp_BinPred BIExp_Equal
                            (BExp_BinExp BIExp_And
                                (BExp_Den (BVar "sy_x" (BType_Imm Bit32)))
                                (BExp_Const (Imm32 3w)))
                            (BExp_Const (Imm32 0w)))
                        (BExp_BinPred BIExp_Equal
                            (BExp_Den (BVar "sy_y" (BType_Imm Bit8)))
                            (BExp_Const (Imm8 7w))))|>})
``;

val thm_test2 = aux_moveawayLib.mk_oracle_preserve_tags [] "TESTFILE" ``
  birs_symb_exec prog (<|bsst_pc :=
               <|bpc_label := BL_Address (Imm32 0x0w);
                 bpc_index := 0|>;
             bsst_environ :=
               birs_gen_env
                 [("x",BExp_Den (BVar "sy_x" (BType_Imm Bit32)));
                  ("y",BExp_Den (BVar "sy_y" (BType_Imm Bit8)));
                  ("MEM",BExp_Den (BVar "sy_MEM" (BType_Mem Bit32 Bit8)));];
             bsst_status := BST_Running;
             bsst_pcond :=
               BExp_BinExp BIExp_And
                    (BExp_BinPred BIExp_Equal
                        (BExp_BinExp BIExp_And
                            (BExp_Den (BVar "sy_x" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 3w)))
                        (BExp_Const (Imm32 0w)))
                    (BExp_Den (BVar "syp_gen" (BType_Imm Bit1)))|>,
           {<|bpc_label := BL_Label "xyz"; bpc_index := 0|>},
           {<|bsst_pc :=
                <|bpc_label := BL_Address (Imm32 0x10w);
                  bpc_index := 0|>;
              bsst_environ :=
                birs_gen_env
                  [("MEM",
                    BExp_Store
                      (BExp_Store
                         (BExp_Store
                            (BExp_Den (BVar "sy_MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_BinExp BIExp_Minus
                               (BExp_BinExp BIExp_Minus
                                  (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)))
                                  (BExp_Const (Imm32 20w)))
                               (BExp_Const (Imm32 8w)))
                            BEnd_LittleEndian
                            (BExp_Den (BVar "sy_R10" (BType_Imm Bit32))))
                         (BExp_BinExp BIExp_Minus
                            (BExp_BinExp BIExp_Minus
                               (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)))
                               (BExp_Const (Imm32 20w)))
                            (BExp_Const (Imm32 4w)))
                         BEnd_LittleEndian
                         (BExp_Den (BVar "sy_R11" (BType_Imm Bit32))))
                      (BExp_BinExp BIExp_Plus
                         (BExp_BinExp BIExp_Minus
                            (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 48w)))
                         (BExp_Const (Imm32 4w)))
                      BEnd_LittleEndian
                      (BExp_Den (BVar "sy_aaa" (BType_Imm Bit32))));
                   ("x",
                    BExp_BinExp BIExp_Plus
                        (BExp_Den (BVar "sy_x" (BType_Imm Bit32)))
                        (BExp_Const (Imm32 16w)));
                   ("y",BExp_Den (BVar "sy_y" (BType_Imm Bit8)))];
              bsst_status := BST_Running;
              bsst_pcond :=
                BExp_BinExp BIExp_And
                  (BExp_Den (BVar "syp_gen" (BType_Imm Bit1)))
                    (BExp_BinPred BIExp_Equal
                        (BExp_BinExp BIExp_And
                            (BExp_Den (BVar "sy_x" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 3w)))
                        (BExp_Const (Imm32 0w)))|>;
           <|bsst_pc :=
                <|bpc_label := BL_Address (Imm32 0x10w);
                  bpc_index := 0|>;
              bsst_environ :=
                birs_gen_env
                  [("MEM",
                    BExp_Store
                      (BExp_Store
                         (BExp_Store
                            (BExp_Den (BVar "sy_MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_BinExp BIExp_Minus
                               (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)))
                               (BExp_Const (Imm32 28w)))
                            BEnd_LittleEndian
                            (BExp_Den (BVar "sy_bbb" (BType_Imm Bit32))))
                         (BExp_BinExp BIExp_Minus
                            (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 20w)))
                         BEnd_LittleEndian
                         (BExp_Den (BVar "sy_R11" (BType_Imm Bit32))))
                      (BExp_BinExp BIExp_Minus
                         (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 44w)))
                      BEnd_LittleEndian
                      (BExp_Den (BVar "sy_aaa" (BType_Imm Bit32))));
                   ("x",
                    BExp_BinExp BIExp_Plus
                        (BExp_Den (BVar "sy_x" (BType_Imm Bit32)))
                        (BExp_Const (Imm32 32w)));
                   ("y",BExp_Den (BVar "sy_y" (BType_Imm Bit8)))];
              bsst_status := BST_Running;
              bsst_pcond :=
                BExp_BinExp BIExp_And
                    (BExp_Den (BVar "syp_gen" (BType_Imm Bit1)))
                    (BExp_BinExp BIExp_And
                        (BExp_BinPred BIExp_Equal
                            (BExp_BinExp BIExp_And
                                (BExp_Den (BVar "sy_x" (BType_Imm Bit32)))
                                (BExp_Const (Imm32 3w)))
                            (BExp_Const (Imm32 0w)))
                        (BExp_BinPred BIExp_Equal
                            (BExp_Den (BVar "sy_y" (BType_Imm Bit8)))
                            (BExp_Const (Imm8 7w))))|>})
``;

val _ = show_tags := true;
val thm_test = thm_test2;

val _ = birs_freesymb_oracle_speed := false;
val _ = birs_mem_shuffle_oracle_speed := false;
(*
val _ = birs_freesymb_oracle_speed := true;
val _ = birs_mem_shuffle_oracle_speed := true;
*)
val newthm = birs_Pi_merge_RULE thm_test;

val _ = Portable.pprint Tag.pp_tag (tag thm_test);
val _ = print "\n\n";
val _ = Portable.pprint Tag.pp_tag (tag newthm);
val _ = print "\n\n";
val _ = print_thm newthm;
val _ = print "\n\n";
