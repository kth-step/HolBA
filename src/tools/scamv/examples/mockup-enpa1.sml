

(* --------------------------------------- *)
(* proggen *)
(* --------------------------------------- *)

val prog_sections = [
                     BILMR (Arbnum.fromString "0",
                       [("eb03005f", BILME_code(SOME "cmp x2, x3")),
                        ("54000043", BILME_code(SOME "b.cc c <lb>  // b.lo, b.ul, b.last")),
                        ("8b030041", BILME_code(SOME "add x1, x2, x3"))]),
                     BILMR (Arbnum.fromString "12",
                       [("f9400022", BILME_code(SOME "ldr x2, [x1]"))])
                    ];



(* --------------------------------------- *)
(* lifting *)
(* --------------------------------------- *)

val prog = ``BirProgram
      [<|bb_label := BL_Address_HC (Imm64 0w) "EB03005F (cmp x2, x3)";
         bb_statements :=
           [BStmt_Assign (BVar "ProcState_C" BType_Bool)
              (BExp_nzcv_SUB_C (BExp_Den (BVar "R2" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R3" (BType_Imm Bit64))));
            BStmt_Assign (BVar "ProcState_N" BType_Bool)
              (BExp_nzcv_SUB_N Bit64 (BExp_Den (BVar "R2" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R3" (BType_Imm Bit64))));
            BStmt_Assign (BVar "ProcState_V" BType_Bool)
              (BExp_nzcv_SUB_V Bit64 (BExp_Den (BVar "R2" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R3" (BType_Imm Bit64))));
            BStmt_Assign (BVar "ProcState_Z" BType_Bool)
              (BExp_nzcv_SUB_Z (BExp_Den (BVar "R2" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R3" (BType_Imm Bit64))))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 4w)))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 4w)
             "54000043 (b.cc c <lb>  // b.lo, b.ul, b.last)";
         bb_statements := [];
         bb_last_statement :=
           BStmt_CJmp (BExp_Den (BVar "ProcState_C" BType_Bool))
             (BLE_Label (BL_Address (Imm64 8w)))
             (BLE_Label (BL_Address (Imm64 12w)))|>;
       <|bb_label := BL_Address_HC (Imm64 8w) "8B030041 (add x1, x2, x3)";
         bb_statements :=
           [BStmt_Assign (BVar "R1" (BType_Imm Bit64))
              (BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "R3" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R2" (BType_Imm Bit64))))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 12w)))|>;
       <|bb_label := BL_Address_HC (Imm64 12w) "F9400022 (ldr x2, [x1])";
         bb_statements :=
           [BStmt_Assert
              (BExp_Aligned Bit64 3 (BExp_Den (BVar "R1" (BType_Imm Bit64))));
            BStmt_Assign (BVar "R2" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_Den (BVar "R1" (BType_Imm Bit64))) BEnd_LittleEndian
                 Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 16w)))|>]``;



(* --------------------------------------- *)
(* obsmod augmentation *)
(* --------------------------------------- *)

      
val prog_w_obs =
``BirProgram
      [<|bb_label := BL_Address_HC (Imm64 0w) "EB03005F (cmp x2, x3)";
         bb_statements :=
           [BStmt_Assign (BVar "ProcState_C" BType_Bool)
              (BExp_nzcv_SUB_C (BExp_Den (BVar "R2" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R3" (BType_Imm Bit64))));
            BStmt_Assign (BVar "ProcState_N" BType_Bool)
              (BExp_nzcv_SUB_N Bit64 (BExp_Den (BVar "R2" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R3" (BType_Imm Bit64))));
            BStmt_Assign (BVar "ProcState_V" BType_Bool)
              (BExp_nzcv_SUB_V Bit64 (BExp_Den (BVar "R2" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R3" (BType_Imm Bit64))));
            BStmt_Assign (BVar "ProcState_Z" BType_Bool)
              (BExp_nzcv_SUB_Z (BExp_Den (BVar "R2" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R3" (BType_Imm Bit64))))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 4w)))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 4w)
             "54000043 (b.cc c <lb>  // b.lo, b.ul, b.last)";
         bb_statements := [];
         bb_last_statement :=
           BStmt_CJmp (BExp_Den (BVar "ProcState_C" BType_Bool))
             (BLE_Label (BL_Address (Imm64 8w)))
             (BLE_Label (BL_Address (Imm64 12w)))|>;
       <|bb_label := BL_Address_HC (Imm64 8w) "8B030041 (add x1, x2, x3)";
         bb_statements :=
           [BStmt_Assign (BVar "R1" (BType_Imm Bit64))
              (BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "R3" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R2" (BType_Imm Bit64))))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 12w)))|>;
       <|bb_label := BL_Address_HC (Imm64 12w) "F9400022 (ldr x2, [x1])";
         bb_statements :=
           [BStmt_Assert
              (BExp_Aligned Bit64 3 (BExp_Den (BVar "R1" (BType_Imm Bit64))));
            BStmt_Assign (BVar "R2" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_Den (BVar "R1" (BType_Imm Bit64))) BEnd_LittleEndian
                 Bit64);
            BStmt_Observe (BExp_Const (Imm1 1w))
                          ([BExp_BinExp BIExp_And
                                        (BExp_Const (Imm64 0x1FC0w))
                                        (BExp_Den (BVar "R1" (BType_Imm Bit64)))])
                          (\x. x)
           ];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 16w)))|>]``;



(* --------------------------------------- *)
(* symbexec *)
(* --------------------------------------- *)

val prog_symbexecs = ;



(* --------------------------------------- *)
(* obss per paths *)
(* --------------------------------------- *)

val prog_obss_paths = ;



(* --------------------------------------- *)
(* rel synth *)
(* --------------------------------------- *)

val prog_obsrel = ;



(* --------------------------------------- *)
(* rel partitioning *)
(* --------------------------------------- *)

val prog_obsrel_parts = ;



(* --------------------------------------- *)
(* constrain memory accesses (for cache on test platform, etc.) *)
(* --------------------------------------- *)

val prog_obsrel_parts_constrained = ;



(* --------------------------------------- *)
(* state gen using smt *)
(* --------------------------------------- *)

val prog_states = ;



(* --------------------------------------- *)
(* test exec *)
(* --------------------------------------- *)

val prog_testresult = ;


