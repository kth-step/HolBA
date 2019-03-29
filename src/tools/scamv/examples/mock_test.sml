
open bir_relSynth;
open bslSyntax;

val cond = bandl [ble (bconst64 (0x30000 + 0x80000000),
                       bden (bvarimm64 "R1")),
                  ble (bden (bvarimm64 "R1"), bconst64 (0x42ff8 + 0x80000000)),
                  ``BExp_Aligned Bit64 3 (BExp_Den (BVar "R1" (BType_Imm Bit64)))``
                 ];

val bir_true = ``BExp_Const (Imm1 1w)``;

val prog_obss_paths =
    [
      (bnot cond, NONE),
      (cond,
       SOME [
           (bir_true, ``BExp_BinExp BIExp_And
                        (BExp_Const (Imm64 0x1FC0w))
                        (BExp_Den (BVar "R1" (BType_Imm Bit64)))``)
      ])
    ];

val relation = mkRel prog_obss_paths;
