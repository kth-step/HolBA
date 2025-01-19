open HolKernel Parse boolLib bossLib;
open birs_conseqLib;

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
                        (BExp_Const (Imm32 16w)));
                   ("y",BExp_Den (BVar "sy_y" (BType_Imm Bit8)))];
              bsst_status := BST_Running;
              bsst_pcond :=
                (BExp_Den (BVar "syp_gen" (BType_Imm Bit1)))|>})
``;

val thm_test3 = aux_moveawayLib.mk_oracle_preserve_tags [] "TESTFILE" ``
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
                        (BExp_Const (Imm32 0w)))|>})
``;

val thm_test = thm_test2;

(*val _ = rule_CONSEQ_oracle_speed := true;*)
val newthm = birs_Pi_first_pcond_RULE ``BExp_Den (BVar "syp_gen" (BType_Imm Bit1))`` thm_test;
(*val newthm = birs_sys_pcond_RULE ``
BExp_BinExp BIExp_And
  (BExp_BinExp BIExp_And
                    (BExp_BinPred BIExp_Equal
                        (BExp_BinExp BIExp_And
                            (BExp_Den (BVar "sy_x" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 3w)))
                        (BExp_Const (Imm32 0w)))
                    (BExp_Den (BVar "syp_gen" (BType_Imm Bit1))))
  (BExp_Den (BVar "syp_gen22" (BType_Imm Bit1)))`` thm_test;*)

val _ = show_tags := true;
val _ = Portable.pprint Tag.pp_tag (tag thm_test);
val _ = Portable.pprint Tag.pp_tag (tag newthm);
val _ = print_thm newthm;
val _ = print "\n\n";
