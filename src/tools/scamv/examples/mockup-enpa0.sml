

(* --------------------------------------- *)
(* proggen *)
(* --------------------------------------- *)

val prog_sections = [
                     BILMR (Arbnum.fromString "0",
                       [("54000040", BILME_code(SOME "b.eq 8 <l2>  // b.none")),
                        ("9b037c41", BILME_code(SOME "mul x1, x2, x3"))]),
                     BILMR (Arbnum.fromString "8",
                       [("f9400422", BILME_code(SOME "ldr x2, [x1, #8]"))])
                    ];



(* --------------------------------------- *)
(* lifting *)
(* --------------------------------------- *)

val prog = ``BirProgram
      [<|bb_label :=
           BL_Address_HC (Imm64 0w) "54000040 (b.eq 8 <l2>  // b.none)";
         bb_statements := [];
         bb_last_statement :=
           BStmt_CJmp (BExp_Den (BVar "ProcState_Z" BType_Bool))
             (BLE_Label (BL_Address (Imm64 8w)))
             (BLE_Label (BL_Address (Imm64 4w)))|>;
       <|bb_label := BL_Address_HC (Imm64 4w) "9B037C41 (mul x1, x2, x3)";
         bb_statements :=
           [BStmt_Assign (BVar "R1" (BType_Imm Bit64))
              (BExp_BinExp BIExp_Mult
                 (BExp_Den (BVar "R3" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R2" (BType_Imm Bit64))))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 8w)))|>;
       <|bb_label := BL_Address_HC (Imm64 8w) "F9400422 (ldr x2, [x1, #8])";
         bb_statements :=
           [BStmt_Assert
              (BExp_Aligned Bit64 3 (BExp_Den (BVar "R1" (BType_Imm Bit64))));
            BStmt_Assign (BVar "R2" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 8w))) BEnd_LittleEndian Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 12w)))|>]``;



(* --------------------------------------- *)
(* obsmod augmentation *)
(* --------------------------------------- *)

val prog_w_obs = ;



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


