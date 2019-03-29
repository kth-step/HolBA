

(* --------------------------------------- *)
(* proggen *)
(* --------------------------------------- *)

val prog_sections = [
                     BILMR (Arbnum.fromString "0",
                       [("f9400023", BILME_code(SOME "ldr x3, [x1]")),
                        ("f9400044", BILME_code(SOME "ldr x4, [x2]"))])
                    ];



(* --------------------------------------- *)
(* lifting *)
(* --------------------------------------- *)

val prog = ``BirProgram
      [<|bb_label := BL_Address_HC (Imm64 0w) "F9400023 (ldr x3, [x1])";
         bb_statements :=
           [BStmt_Assert
              (BExp_Aligned Bit64 3 (BExp_Den (BVar "R1" (BType_Imm Bit64))));
            BStmt_Assign (BVar "R3" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_Den (BVar "R1" (BType_Imm Bit64))) BEnd_LittleEndian
                 Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 4w)))|>;
       <|bb_label := BL_Address_HC (Imm64 4w) "F9400044 (ldr x4, [x2])";
         bb_statements :=
           [BStmt_Assert
              (BExp_Aligned Bit64 3 (BExp_Den (BVar "R2" (BType_Imm Bit64))));
            BStmt_Assign (BVar "R4" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_Den (BVar "R2" (BType_Imm Bit64))) BEnd_LittleEndian
                 Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 8w)))|>]``;



(* --------------------------------------- *)
(* obsmod augmentation *)
(* --------------------------------------- *)

(*
  (cache line(x))
*)
val prog_w_obs = ``BirProgram
      [<|bb_label := BL_Address_HC (Imm64 0w) "F9400023 (ldr x3, [x1])";
         bb_statements :=
           [BStmt_Assert
              (BExp_Aligned Bit64 3 (BExp_Den (BVar "R1" (BType_Imm Bit64))));
            BStmt_Assign (BVar "R3" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_Den (BVar "R1" (BType_Imm Bit64))) BEnd_LittleEndian
                 Bit64);
            BStmt_Observe (BExp_Const (Imm1 1w))
                          ([BExp_BinExp BIExp_And
                                        (BExp_Const (Imm64 0x1FC0w))
                                        (BExp_Den (BVar "R1" (BType_Imm Bit64)))])
                          (\x. x)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 4w)))|>;
       <|bb_label := BL_Address_HC (Imm64 4w) "F9400044 (ldr x4, [x2])";
         bb_statements :=
           [BStmt_Assert
              (BExp_Aligned Bit64 3 (BExp_Den (BVar "R2" (BType_Imm Bit64))));
            BStmt_Assign (BVar "R4" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_Den (BVar "R2" (BType_Imm Bit64))) BEnd_LittleEndian
                 Bit64);
            BStmt_Observe (BExp_Const (Imm1 1w))
                          ([BExp_BinExp BIExp_And
                                        (BExp_Const (Imm64 0x1FC0w))
                                        (BExp_Den (BVar "R2" (BType_Imm Bit64)))])
                          (\x. x)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 8w)))|>]``;



(* --------------------------------------- *)
(* symbexec *)
(* --------------------------------------- *)

val prog_symbexecs =
  [
    (``BExp_BinExp BIExp_And (BExp_Const (Imm1 1w))
         (BExp_BinExp BIExp_And
           (BExp_Aligned Bit64 3 (BExp_Den (BVar "R1" (BType_Imm Bit64))))
           (BExp_Aligned Bit64 3 (BExp_Den (BVar "R2" (BType_Imm Bit64)))))``,
     ``BSEnv (FEMPTY
         |+ ("R1",  BType_Imm Bit64,      BExp_Den (BVar "R1"  (BType_Imm Bit64)))
         |+ ("R2",  BType_Imm Bit64,      BExp_Den (BVar "R2"  (BType_Imm Bit64)))
         |+ ("R3",  BType_Imm Bit64,      (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                                                     (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                                                     BEnd_LittleEndian
                                                     Bit64))
         |+ ("R4",  BType_Imm Bit64,      (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                                                     (BExp_Den (BVar "R2" (BType_Imm Bit64)))
                                                     BEnd_LittleEndian
                                                     Bit64))
         |+ ("MEM", BType_Mem Bit64 Bit8, BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
       )``,
     [
       (``(BExp_Const (Imm1 1w))``, [``BExp_BinExp BIExp_And
            (BExp_Const (Imm64 0x1FC0w))
            (BExp_Den (BVar "R1" (BType_Imm Bit64)))``]
        ,
         [BExp_BinExp BIExp_And
            (BExp_Const (Imm64 0x1FC0w))
            (BExp_Den (BVar "R2" (BType_Imm Bit64)))]
       ])
  ];



(* --------------------------------------- *)
(* obss per paths *)
(* --------------------------------------- *)

val prog_obss_paths =
    [
      (``...``, NONE),
    (``BExp_BinExp BIExp_And (BExp_Const (Imm1 1w))
         (BExp_BinExp BIExp_And
           (BExp_Aligned Bit64 3 (BExp_Den (BVar "R1" (BType_Imm Bit64))))
           (BExp_Aligned Bit64 3 (BExp_Den (BVar "R2" (BType_Imm Bit64)))))``,
     SOME [
          (``BExp_Const (Imm1 1w)``, ``BExp_BinExp BIExp_And
            (BExp_Const (Imm64 0x1FC0w))
            (BExp_Den (BVar "R1" (BType_Imm Bit64)))``)
        ,
          (``BExp_Const (Imm1 1w)``, ``BExp_BinExp BIExp_And
            (BExp_Const (Imm64 0x1FC0w))
            (BExp_Den (BVar "R2" (BType_Imm Bit64)))``)
       ])
  ];



(* --------------------------------------- *)
(* rel synth *)
(* --------------------------------------- *)

val p1_1 =
     ``BExp_BinExp BIExp_And (BExp_Const (Imm1 1w))
         (BExp_BinExp BIExp_And
           (BExp_Aligned Bit64 3 (BExp_Den (BVar "s1_R1" (BType_Imm Bit64))))
           (BExp_Aligned Bit64 3 (BExp_Den (BVar "s1_R2" (BType_Imm Bit64)))))``;

val p2_1 =
     ``BExp_BinExp BIExp_And (BExp_Const (Imm1 1w))
         (BExp_BinExp BIExp_And
           (BExp_Aligned Bit64 3 (BExp_Den (BVar "s2_R1" (BType_Imm Bit64))))
           (BExp_Aligned Bit64 3 (BExp_Den (BVar "s2_R2" (BType_Imm Bit64)))))``;

val obsl1_1_1 =
     ``BExp_BinExp BIExp_And
            (BExp_Const (Imm64 0x1FC0w))
            (BExp_Den (BVar "s1_R1" (BType_Imm Bit64)))``;

val obsl1_2_1 =
     ``BExp_BinExp BIExp_And
            (BExp_Const (Imm64 0x1FC0w))
            (BExp_Den (BVar "s1_R2" (BType_Imm Bit64)))``;

val obsl2_1_1 =
     ``BExp_BinExp BIExp_And
            (BExp_Const (Imm64 0x1FC0w))
            (BExp_Den (BVar "s2_R1" (BType_Imm Bit64)))``;

val obsl2_2_1 =
     ``BExp_BinExp BIExp_And
            (BExp_Const (Imm64 0x1FC0w))
            (BExp_Den (BVar "s2_R2" (BType_Imm Bit64)))``;

val prog_obsrel =
  ``bir_exp_and (bir_exp_and ^p1_1 ^p2_1)
      (bir_exp_imp (bir_exp_and ^p1_1 ^p2_1)
                   (bir_exp_and (BExp_BinPred BIExp_Equal ^obsl1_1_1 ^obsl2_1_1)
                                (BExp_BinPred BIExp_Equal ^obsl1_2_1 ^obsl2_2_1)))
  ``;



(* --------------------------------------- *)
(* rel partitioning *)
(* --------------------------------------- *)

val prog_obsrel_parts =
  [
    ``bir_exp_and (bir_exp_and ^p1_1 ^p2_1)
                  (bir_exp_and (BExp_BinPred BIExp_Equal ^obsl1_1_1 ^obsl2_1_1)
                               (BExp_BinPred BIExp_Equal ^obsl1_2_1 ^obsl2_2_1))
    ``
  ];



(* --------------------------------------- *)
(* constrain memory accesses (for cache on test platform, etc.) *)
(* --------------------------------------- *)

val s1_R1_va = ``bir_exp_and (BExp_BinPred BIExp_LessOrEqual (BExp_Const (Imm1 0x80000000w))
                                                             (BExp_Den (BVar "s1_R1" (BType_Imm Bit64))))
                             (BExp_BinPred BIExp_LessThan    (BExp_Den (BVar "s1_R1" (BType_Imm Bit64)))
                                                             (BExp_Const (Imm1 0xC0000000w)))``;

val s1_R2_va = ``bir_exp_and (BExp_BinPred BIExp_LessOrEqual (BExp_Const (Imm1 0x80000000w))
                                                             (BExp_Den (BVar "s1_R2" (BType_Imm Bit64))))
                             (BExp_BinPred BIExp_LessThan    (BExp_Den (BVar "s1_R2" (BType_Imm Bit64)))
                                                             (BExp_Const (Imm1 0xC0000000w)))``;

val s2_R1_va = ``bir_exp_and (BExp_BinPred BIExp_LessOrEqual (BExp_Const (Imm1 0x80000000w))
                                                             (BExp_Den (BVar "s2_R1" (BType_Imm Bit64))))
                             (BExp_BinPred BIExp_LessThan    (BExp_Den (BVar "s2_R1" (BType_Imm Bit64)))
                                                             (BExp_Const (Imm1 0xC0000000w)))``;

val s2_R2_va = ``bir_exp_and (BExp_BinPred BIExp_LessOrEqual (BExp_Const (Imm1 0x80000000w))
                                                             (BExp_Den (BVar "s2_R2" (BType_Imm Bit64))))
                             (BExp_BinPred BIExp_LessThan    (BExp_Den (BVar "s2_R2" (BType_Imm Bit64)))
                                                             (BExp_Const (Imm1 0xC0000000w)))``;

val prog_obsrel_parts_constrained =
    ``bir_exp_and
        (bir_exp_and (bir_exp_and ^p1_1 ^p2_1)
                     (bir_exp_and (BExp_BinPred BIExp_Equal ^obsl1_1_1 ^obsl2_1_1)
                                  (BExp_BinPred BIExp_Equal ^obsl1_2_1 ^obsl2_2_1)))
        (bir_exp_and (bir_exp_and ^s1_R1_va ^s1_R2_va)
                     (bir_exp_and ^s2_R1_va ^s2_R2_va))
    ``;



(* --------------------------------------- *)
(* state gen using smt *)
(* --------------------------------------- *)

val prog_states =
  (
    [("R1", 0), ("R2", 0)]
   ,
    [("R1", 0), ("R2", 32*1024)]
  );



(* --------------------------------------- *)
(* test exec *)
(* --------------------------------------- *)

val prog_testresult = false; (* distinguishable *)


