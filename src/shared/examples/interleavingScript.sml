open HolKernel Parse boolLib bossLib;

open bslSyntax;
open bir_programTheory;

val _ = new_theory "interleaving_example";

fun bloadvar var n =
    bload64_le (bden (bvarmem64_8 "MEM"))
               (bplus (bden (bvarimm64 var),
                       bconst8 n));

fun bstorevar var n v =
    bassign (bvarmem64_8 "MEM",
             bstore_le (bden (bvarmem64_8 "MEM"))
                       (bplus (bden (bvarimm64 var),
                               bconst8 n)) v);
val bir_interleaving2_1 =
    bdefprog_list (Type`:'a`) "p_1"
                  [(blabel_str "P1"
                   ,[
                     bassign (bvarimm64 "R0",
                              bload64_le (bden (bvarmem64_8 "MEM")) (bden (bvarimm64 "x"))),
                     bassign (bvarmem64_8 "MEM",
                              bstore_le (bden (bvarmem64_8 "MEM"))
                                        (bden (bvarimm64 "y"))
                                        (bden (bvarimm64 "R0")))
                     ]
                   ,(bhalt o bconst32) 0)];

val bir_interleaving2_2 =
    bdefprog_list (Type`:'a`) "p_2"
                  [(blabel_str "P2"
                   ,[
                     bassign (bvarimm64 "R0",
                              bload64_le (bden (bvarmem64_8 "MEM")) (bden (bvarimm64 "y"))),
                     bassign (bvarmem64_8 "MEM",
                              bstore_le (bden (bvarmem64_8 "MEM"))
                                        (bden (bvarimm64 "x"))
                                        (bden (bvarimm64 "R0")))
                   ]
                   ,(bhalt o bconst32) 0)];

val initial = ``bir_state_init p_1 with bst_environ := BEnv (\vn. if vn = "x" then SOME (BVal_Imm (Imm64 0w)) else if vn = "y" then SOME (BVal_Imm (Imm64 1w)) else if vn = "MEM" then SOME (BVal_Mem Bit64 Bit8 (FEMPTY |+ (0,0) |+ (1,1))) else NONE)``;

val _ = export_theory ();
