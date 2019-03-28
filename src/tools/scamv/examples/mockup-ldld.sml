

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


