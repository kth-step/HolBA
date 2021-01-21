open HolKernel Parse boolLib bossLib;
open bslSyntax;

open bir_obs_modelLib;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = Globals.show_types := true;


val mem_bounds =
      let
        open wordsSyntax;
        val (mem_base, mem_len) = (Arbnum.fromHexString "0xFFCC0000",
                                   Arbnum.fromHexString  "0x10000");
        val mem_end = (Arbnum.- (Arbnum.+ (mem_base, mem_len), Arbnum.fromInt 128));
      in
        pairSyntax.mk_pair
            (mk_wordi (mem_base, 64),
             mk_wordi (mem_end, 64))
      end;


(*
(bir_prog_genLib.prog_gen_store_a_la_qc "spectre" 100) ()
(bir_prog_genLib.prog_gen_store_a_la_qc "spectre_v1" 100) ()
(bir_prog_genLib.prog_gen_store_a_la_qc "xld_br_yld" 2) ()
*)

(* ========================= prog_1 - branch and merge (spectre) =========================== *)

(*
=================================
	ldr x26, [x14,x24]
	ldr x15, [x17, #0]
	cmp x14, x15
	b.eq #0xC
	ldr x10, [x26, #76]
	b #0x8
	ldr x14, [x9]
=================================
*)

val prog_1 = ``
BirProgram
       [<|bb_label :=
            BL_Address_HC (Imm64 0w) "F87869DA (ldr x26, [x14, x24])";
          bb_statements :=
            [BStmt_Assert
               (BExp_Aligned Bit64 3
                  (BExp_BinExp BIExp_Plus
                     (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                     (BExp_Den (BVar "R14" (BType_Imm Bit64)))));
             BStmt_Assign (BVar "R26" (BType_Imm Bit64))
               (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                  (BExp_BinExp BIExp_Plus
                     (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                     (BExp_Den (BVar "R14" (BType_Imm Bit64))))
                  BEnd_LittleEndian Bit64)];
          bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 4w)))|>;
        <|bb_label := BL_Address_HC (Imm64 4w) "F940022F (ldr x15, [x17])";
          bb_statements :=
            [BStmt_Assert
               (BExp_Aligned Bit64 3
                  (BExp_Den (BVar "R17" (BType_Imm Bit64))));
             BStmt_Assign (BVar "R15" (BType_Imm Bit64))
               (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                  (BExp_Den (BVar "R17" (BType_Imm Bit64))) BEnd_LittleEndian
                  Bit64)];
          bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 8w)))|>;
        <|bb_label := BL_Address_HC (Imm64 8w) "EB0F01DF (cmp x14, x15)";
          bb_statements :=
            [BStmt_Assign (BVar "ProcState_C" BType_Bool)
               (BExp_nzcv_SUB_C (BExp_Den (BVar "R14" (BType_Imm Bit64)))
                  (BExp_Den (BVar "R15" (BType_Imm Bit64))));
             BStmt_Assign (BVar "ProcState_N" BType_Bool)
               (BExp_nzcv_SUB_N Bit64
                  (BExp_Den (BVar "R14" (BType_Imm Bit64)))
                  (BExp_Den (BVar "R15" (BType_Imm Bit64))));
             BStmt_Assign (BVar "ProcState_V" BType_Bool)
               (BExp_nzcv_SUB_V Bit64
                  (BExp_Den (BVar "R14" (BType_Imm Bit64)))
                  (BExp_Den (BVar "R15" (BType_Imm Bit64))));
             BStmt_Assign (BVar "ProcState_Z" BType_Bool)
               (BExp_nzcv_SUB_Z (BExp_Den (BVar "R14" (BType_Imm Bit64)))
                  (BExp_Den (BVar "R15" (BType_Imm Bit64))))];
          bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 12w)))|>;
        <|bb_label :=
            BL_Address_HC (Imm64 12w)
              "54000060 (b.eq 18 <.text+0x18>  // b.none)";
          bb_statements := [];
          bb_last_statement :=
            BStmt_CJmp (BExp_Den (BVar "ProcState_Z" BType_Bool))
              (BLE_Label (BL_Address (Imm64 24w)))
              (BLE_Label (BL_Address (Imm64 16w)))|>;
        <|bb_label :=
            BL_Address_HC (Imm64 16w) "F844C34A (ldur x10, [x26, #76])";
          bb_statements :=
            [BStmt_Assert
               (BExp_Aligned Bit64 3
                  (BExp_BinExp BIExp_Plus
                     (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                     (BExp_Const (Imm64 4w))));
             BStmt_Assign (BVar "R10" (BType_Imm Bit64))
               (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                  (BExp_BinExp BIExp_Plus
                     (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                     (BExp_Const (Imm64 76w))) BEnd_LittleEndian Bit64)];
          bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 20w)))|>;
        <|bb_label :=
            BL_Address_HC (Imm64 20w) "14000002 (b 1c <.text+0x1c>)";
          bb_statements := [];
          bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 28w)))|>;
        <|bb_label := BL_Address_HC (Imm64 24w) "F940012E (ldr x14, [x9])";
          bb_statements :=
            [BStmt_Assert
               (BExp_Aligned Bit64 3 (BExp_Den (BVar "R9" (BType_Imm Bit64))));
             BStmt_Assign (BVar "R14" (BType_Imm Bit64))
               (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                  (BExp_Den (BVar "R9" (BType_Imm Bit64))) BEnd_LittleEndian
                  Bit64)];
          bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 28w)))|>;
        <|bb_label := BL_Address (Imm64 28w); bb_statements := [];
          bb_last_statement := BStmt_Halt (BExp_Const (Imm32 0w))|>]
:bir_val_t bir_program_t
``;

val prog_1_mem_address_pc = ``
BirProgram
      [<|bb_label := BL_Address (Imm64 0w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w)) [BExp_Const (Imm64 0w)] HD;
            BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R14" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 4291559424w))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R14" (BType_Imm Bit64)))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R14" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 4291624832w))));
            BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R14" (BType_Imm Bit64)))] HD;
            BStmt_Assign (BVar "R26" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R14" (BType_Imm Bit64))))
                 BEnd_LittleEndian Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 4w)))|>;
       <|bb_label := BL_Address (Imm64 4w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w)) [BExp_Const (Imm64 4w)] HD;
            BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_Den (BVar "R17" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 4291559424w))
                    (BExp_Den (BVar "R17" (BType_Imm Bit64))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_Den (BVar "R17" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 4291624832w))));
            BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_Den (BVar "R17" (BType_Imm Bit64))] HD;
            BStmt_Assign (BVar "R15" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_Den (BVar "R17" (BType_Imm Bit64))) BEnd_LittleEndian
                 Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 8w)))|>;
       <|bb_label := BL_Address (Imm64 8w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w)) [BExp_Const (Imm64 8w)] HD;
            BStmt_Assign (BVar "ProcState_C" (BType_Imm Bit1))
              (BExp_BinPred BIExp_LessOrEqual
                 (BExp_Den (BVar "R15" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R14" (BType_Imm Bit64))));
            BStmt_Assign (BVar "ProcState_N" (BType_Imm Bit1))
              (BExp_BinPred BIExp_SignedLessThan
                 (BExp_BinExp BIExp_Minus
                    (BExp_Den (BVar "R14" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R15" (BType_Imm Bit64))))
                 (BExp_Const (Imm64 0w)));
            BStmt_Assign (BVar "ProcState_V" (BType_Imm Bit1))
              (BExp_BinPred BIExp_Equal
                 (BExp_BinPred BIExp_SignedLessThan
                    (BExp_BinExp BIExp_Minus
                       (BExp_Den (BVar "R14" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R15" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 0w)))
                 (BExp_BinPred BIExp_SignedLessOrEqual
                    (BExp_Den (BVar "R15" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R14" (BType_Imm Bit64)))));
            BStmt_Assign (BVar "ProcState_Z" (BType_Imm Bit1))
              (BExp_BinPred BIExp_Equal
                 (BExp_Den (BVar "R14" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R15" (BType_Imm Bit64))))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 12w)))|>;
       <|bb_label := BL_Address (Imm64 12w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w)) [BExp_Const (Imm64 12w)]
              HD];
         bb_last_statement :=
           BStmt_CJmp (BExp_Den (BVar "ProcState_Z" (BType_Imm Bit1)))
             (BLE_Label (BL_Address (Imm64 24w)))
             (BLE_Label (BL_Address (Imm64 16w)))|>;
       <|bb_label := BL_Address (Imm64 16w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w)) [BExp_Const (Imm64 16w)]
              HD;
            BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 4w))) (BExp_Const (Imm64 7w)))
                 (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 4291559424w))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 76w))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 76w)))
                    (BExp_Const (Imm64 4291624832w))));
            BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 76w))] HD;
            BStmt_Assign (BVar "R10" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 76w))) BEnd_LittleEndian Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 20w)))|>;
       <|bb_label := BL_Address (Imm64 20w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w)) [BExp_Const (Imm64 20w)]
              HD];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 28w)))|>;
       <|bb_label := BL_Address (Imm64 24w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w)) [BExp_Const (Imm64 24w)]
              HD;
            BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 4291559424w))
                    (BExp_Den (BVar "R9" (BType_Imm Bit64))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 4291624832w))));
            BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_Den (BVar "R9" (BType_Imm Bit64))] HD;
            BStmt_Assign (BVar "R14" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_Den (BVar "R9" (BType_Imm Bit64))) BEnd_LittleEndian
                 Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 28w)))|>;
       <|bb_label := BL_Address (Imm64 28w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w)) [BExp_Const (Imm64 28w)]
              HD]; bb_last_statement := BStmt_Halt (BExp_Const (Imm32 0w))|>]
:bir_val_t bir_program_t
``;

val prog_1_cache_tag_index = ``
BirProgram
      [<|bb_label := BL_Address (Imm64 0w);
         bb_statements :=
           [BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R14" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 4291559424w))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R14" (BType_Imm Bit64)))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R14" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 4291624832w))));
            BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_RightShift
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R14" (BType_Imm Bit64))))
                 (BExp_Const (Imm64 6w))] HD;
            BStmt_Assign (BVar "R26" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R14" (BType_Imm Bit64))))
                 BEnd_LittleEndian Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 4w)))|>;
       <|bb_label := BL_Address (Imm64 4w);
         bb_statements :=
           [BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_Den (BVar "R17" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 4291559424w))
                    (BExp_Den (BVar "R17" (BType_Imm Bit64))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_Den (BVar "R17" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 4291624832w))));
            BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_RightShift
                 (BExp_Den (BVar "R17" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 6w))] HD;
            BStmt_Assign (BVar "R15" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_Den (BVar "R17" (BType_Imm Bit64))) BEnd_LittleEndian
                 Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 8w)))|>;
       <|bb_label := BL_Address (Imm64 8w);
         bb_statements :=
           [BStmt_Assign (BVar "ProcState_C" (BType_Imm Bit1))
              (BExp_BinPred BIExp_LessOrEqual
                 (BExp_Den (BVar "R15" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R14" (BType_Imm Bit64))));
            BStmt_Assign (BVar "ProcState_N" (BType_Imm Bit1))
              (BExp_BinPred BIExp_SignedLessThan
                 (BExp_BinExp BIExp_Minus
                    (BExp_Den (BVar "R14" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R15" (BType_Imm Bit64))))
                 (BExp_Const (Imm64 0w)));
            BStmt_Assign (BVar "ProcState_V" (BType_Imm Bit1))
              (BExp_BinPred BIExp_Equal
                 (BExp_BinPred BIExp_SignedLessThan
                    (BExp_BinExp BIExp_Minus
                       (BExp_Den (BVar "R14" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R15" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 0w)))
                 (BExp_BinPred BIExp_SignedLessOrEqual
                    (BExp_Den (BVar "R15" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R14" (BType_Imm Bit64)))));
            BStmt_Assign (BVar "ProcState_Z" (BType_Imm Bit1))
              (BExp_BinPred BIExp_Equal
                 (BExp_Den (BVar "R14" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R15" (BType_Imm Bit64))))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 12w)))|>;
       <|bb_label := BL_Address (Imm64 12w); bb_statements := [];
         bb_last_statement :=
           BStmt_CJmp (BExp_Den (BVar "ProcState_Z" (BType_Imm Bit1)))
             (BLE_Label (BL_Address (Imm64 24w)))
             (BLE_Label (BL_Address (Imm64 16w)))|>;
       <|bb_label := BL_Address (Imm64 16w);
         bb_statements :=
           [BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 4w))) (BExp_Const (Imm64 7w)))
                 (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 4291559424w))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 76w))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 76w)))
                    (BExp_Const (Imm64 4291624832w))));
            BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_RightShift
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 76w))) (BExp_Const (Imm64 6w))] HD;
            BStmt_Assign (BVar "R10" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 76w))) BEnd_LittleEndian Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 20w)))|>;
       <|bb_label := BL_Address (Imm64 20w); bb_statements := [];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 28w)))|>;
       <|bb_label := BL_Address (Imm64 24w);
         bb_statements :=
           [BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 4291559424w))
                    (BExp_Den (BVar "R9" (BType_Imm Bit64))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 4291624832w))));
            BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_RightShift
                 (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 6w))] HD;
            BStmt_Assign (BVar "R14" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_Den (BVar "R9" (BType_Imm Bit64))) BEnd_LittleEndian
                 Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 28w)))|>;
       <|bb_label := BL_Address (Imm64 28w); bb_statements := [];
         bb_last_statement := BStmt_Halt (BExp_Const (Imm32 0w))|>]
:bir_val_t bir_program_t
``;

val prog_1_cache_tag_only = ``
BirProgram
      [<|bb_label := BL_Address (Imm64 0w);
         bb_statements :=
           [BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R14" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 4291559424w))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R14" (BType_Imm Bit64)))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R14" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 4291624832w))));
            BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_RightShift
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R14" (BType_Imm Bit64))))
                 (BExp_Const (Imm64 13w))] HD;
            BStmt_Assign (BVar "R26" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R14" (BType_Imm Bit64))))
                 BEnd_LittleEndian Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 4w)))|>;
       <|bb_label := BL_Address (Imm64 4w);
         bb_statements :=
           [BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_Den (BVar "R17" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 4291559424w))
                    (BExp_Den (BVar "R17" (BType_Imm Bit64))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_Den (BVar "R17" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 4291624832w))));
            BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_RightShift
                 (BExp_Den (BVar "R17" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 13w))] HD;
            BStmt_Assign (BVar "R15" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_Den (BVar "R17" (BType_Imm Bit64))) BEnd_LittleEndian
                 Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 8w)))|>;
       <|bb_label := BL_Address (Imm64 8w);
         bb_statements :=
           [BStmt_Assign (BVar "ProcState_C" (BType_Imm Bit1))
              (BExp_BinPred BIExp_LessOrEqual
                 (BExp_Den (BVar "R15" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R14" (BType_Imm Bit64))));
            BStmt_Assign (BVar "ProcState_N" (BType_Imm Bit1))
              (BExp_BinPred BIExp_SignedLessThan
                 (BExp_BinExp BIExp_Minus
                    (BExp_Den (BVar "R14" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R15" (BType_Imm Bit64))))
                 (BExp_Const (Imm64 0w)));
            BStmt_Assign (BVar "ProcState_V" (BType_Imm Bit1))
              (BExp_BinPred BIExp_Equal
                 (BExp_BinPred BIExp_SignedLessThan
                    (BExp_BinExp BIExp_Minus
                       (BExp_Den (BVar "R14" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R15" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 0w)))
                 (BExp_BinPred BIExp_SignedLessOrEqual
                    (BExp_Den (BVar "R15" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R14" (BType_Imm Bit64)))));
            BStmt_Assign (BVar "ProcState_Z" (BType_Imm Bit1))
              (BExp_BinPred BIExp_Equal
                 (BExp_Den (BVar "R14" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R15" (BType_Imm Bit64))))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 12w)))|>;
       <|bb_label := BL_Address (Imm64 12w); bb_statements := [];
         bb_last_statement :=
           BStmt_CJmp (BExp_Den (BVar "ProcState_Z" (BType_Imm Bit1)))
             (BLE_Label (BL_Address (Imm64 24w)))
             (BLE_Label (BL_Address (Imm64 16w)))|>;
       <|bb_label := BL_Address (Imm64 16w);
         bb_statements :=
           [BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 4w))) (BExp_Const (Imm64 7w)))
                 (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 4291559424w))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 76w))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 76w)))
                    (BExp_Const (Imm64 4291624832w))));
            BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_RightShift
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 76w))) (BExp_Const (Imm64 13w))] HD;
            BStmt_Assign (BVar "R10" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 76w))) BEnd_LittleEndian Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 20w)))|>;
       <|bb_label := BL_Address (Imm64 20w); bb_statements := [];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 28w)))|>;
       <|bb_label := BL_Address (Imm64 24w);
         bb_statements :=
           [BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 4291559424w))
                    (BExp_Den (BVar "R9" (BType_Imm Bit64))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 4291624832w))));
            BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_RightShift
                 (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 13w))] HD;
            BStmt_Assign (BVar "R14" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_Den (BVar "R9" (BType_Imm Bit64))) BEnd_LittleEndian
                 Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 28w)))|>;
       <|bb_label := BL_Address (Imm64 28w); bb_statements := [];
         bb_last_statement := BStmt_Halt (BExp_Const (Imm32 0w))|>]
:bir_val_t bir_program_t
``;

val prog_1_cache_index_only = ``
BirProgram
      [<|bb_label := BL_Address (Imm64 0w);
         bb_statements :=
           [BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R14" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 4291559424w))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R14" (BType_Imm Bit64)))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R14" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 4291624832w))));
            BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_And (BExp_Const (Imm64 127w))
                 (BExp_BinExp BIExp_RightShift
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R14" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 6w)))] HD;
            BStmt_Assign (BVar "R26" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R14" (BType_Imm Bit64))))
                 BEnd_LittleEndian Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 4w)))|>;
       <|bb_label := BL_Address (Imm64 4w);
         bb_statements :=
           [BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_Den (BVar "R17" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 4291559424w))
                    (BExp_Den (BVar "R17" (BType_Imm Bit64))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_Den (BVar "R17" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 4291624832w))));
            BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_And (BExp_Const (Imm64 127w))
                 (BExp_BinExp BIExp_RightShift
                    (BExp_Den (BVar "R17" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 6w)))] HD;
            BStmt_Assign (BVar "R15" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_Den (BVar "R17" (BType_Imm Bit64))) BEnd_LittleEndian
                 Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 8w)))|>;
       <|bb_label := BL_Address (Imm64 8w);
         bb_statements :=
           [BStmt_Assign (BVar "ProcState_C" (BType_Imm Bit1))
              (BExp_BinPred BIExp_LessOrEqual
                 (BExp_Den (BVar "R15" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R14" (BType_Imm Bit64))));
            BStmt_Assign (BVar "ProcState_N" (BType_Imm Bit1))
              (BExp_BinPred BIExp_SignedLessThan
                 (BExp_BinExp BIExp_Minus
                    (BExp_Den (BVar "R14" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R15" (BType_Imm Bit64))))
                 (BExp_Const (Imm64 0w)));
            BStmt_Assign (BVar "ProcState_V" (BType_Imm Bit1))
              (BExp_BinPred BIExp_Equal
                 (BExp_BinPred BIExp_SignedLessThan
                    (BExp_BinExp BIExp_Minus
                       (BExp_Den (BVar "R14" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R15" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 0w)))
                 (BExp_BinPred BIExp_SignedLessOrEqual
                    (BExp_Den (BVar "R15" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R14" (BType_Imm Bit64)))));
            BStmt_Assign (BVar "ProcState_Z" (BType_Imm Bit1))
              (BExp_BinPred BIExp_Equal
                 (BExp_Den (BVar "R14" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R15" (BType_Imm Bit64))))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 12w)))|>;
       <|bb_label := BL_Address (Imm64 12w); bb_statements := [];
         bb_last_statement :=
           BStmt_CJmp (BExp_Den (BVar "ProcState_Z" (BType_Imm Bit1)))
             (BLE_Label (BL_Address (Imm64 24w)))
             (BLE_Label (BL_Address (Imm64 16w)))|>;
       <|bb_label := BL_Address (Imm64 16w);
         bb_statements :=
           [BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 4w))) (BExp_Const (Imm64 7w)))
                 (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 4291559424w))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 76w))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 76w)))
                    (BExp_Const (Imm64 4291624832w))));
            BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_And (BExp_Const (Imm64 127w))
                 (BExp_BinExp BIExp_RightShift
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 76w))) (BExp_Const (Imm64 6w)))] HD;
            BStmt_Assign (BVar "R10" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 76w))) BEnd_LittleEndian Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 20w)))|>;
       <|bb_label := BL_Address (Imm64 20w); bb_statements := [];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 28w)))|>;
       <|bb_label := BL_Address (Imm64 24w);
         bb_statements :=
           [BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 4291559424w))
                    (BExp_Den (BVar "R9" (BType_Imm Bit64))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 4291624832w))));
            BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_And (BExp_Const (Imm64 127w))
                 (BExp_BinExp BIExp_RightShift
                    (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 6w)))] HD;
            BStmt_Assign (BVar "R14" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_Den (BVar "R9" (BType_Imm Bit64))) BEnd_LittleEndian
                 Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 28w)))|>;
       <|bb_label := BL_Address (Imm64 28w); bb_statements := [];
         bb_last_statement := BStmt_Halt (BExp_Const (Imm32 0w))|>]
:bir_val_t bir_program_t
``;

val prog_1_cache_tag_index_part = ``
BirProgram
      [<|bb_label := BL_Address (Imm64 0w);
         bb_statements :=
           [BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R14" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 4291559424w))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R14" (BType_Imm Bit64)))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R14" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 4291624832w))));
            BStmt_Observe 0
              (BExp_BinPred BIExp_LessThan (BExp_Const (Imm64 60w))
                 (BExp_BinExp BIExp_Mod
                    (BExp_BinExp BIExp_RightShift
                       (BExp_BinExp BIExp_Plus
                          (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                          (BExp_Den (BVar "R14" (BType_Imm Bit64))))
                       (BExp_Const (Imm64 6w))) (BExp_Const (Imm64 128w))))
              [BExp_BinExp BIExp_RightShift
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R14" (BType_Imm Bit64))))
                 (BExp_Const (Imm64 6w))] HD;
            BStmt_Assign (BVar "R26" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R14" (BType_Imm Bit64))))
                 BEnd_LittleEndian Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 4w)))|>;
       <|bb_label := BL_Address (Imm64 4w);
         bb_statements :=
           [BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_Den (BVar "R17" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 4291559424w))
                    (BExp_Den (BVar "R17" (BType_Imm Bit64))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_Den (BVar "R17" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 4291624832w))));
            BStmt_Observe 0
              (BExp_BinPred BIExp_LessThan (BExp_Const (Imm64 60w))
                 (BExp_BinExp BIExp_Mod
                    (BExp_BinExp BIExp_RightShift
                       (BExp_Den (BVar "R17" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 6w))) (BExp_Const (Imm64 128w))))
              [BExp_BinExp BIExp_RightShift
                 (BExp_Den (BVar "R17" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 6w))] HD;
            BStmt_Assign (BVar "R15" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_Den (BVar "R17" (BType_Imm Bit64))) BEnd_LittleEndian
                 Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 8w)))|>;
       <|bb_label := BL_Address (Imm64 8w);
         bb_statements :=
           [BStmt_Assign (BVar "ProcState_C" (BType_Imm Bit1))
              (BExp_BinPred BIExp_LessOrEqual
                 (BExp_Den (BVar "R15" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R14" (BType_Imm Bit64))));
            BStmt_Assign (BVar "ProcState_N" (BType_Imm Bit1))
              (BExp_BinPred BIExp_SignedLessThan
                 (BExp_BinExp BIExp_Minus
                    (BExp_Den (BVar "R14" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R15" (BType_Imm Bit64))))
                 (BExp_Const (Imm64 0w)));
            BStmt_Assign (BVar "ProcState_V" (BType_Imm Bit1))
              (BExp_BinPred BIExp_Equal
                 (BExp_BinPred BIExp_SignedLessThan
                    (BExp_BinExp BIExp_Minus
                       (BExp_Den (BVar "R14" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R15" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 0w)))
                 (BExp_BinPred BIExp_SignedLessOrEqual
                    (BExp_Den (BVar "R15" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R14" (BType_Imm Bit64)))));
            BStmt_Assign (BVar "ProcState_Z" (BType_Imm Bit1))
              (BExp_BinPred BIExp_Equal
                 (BExp_Den (BVar "R14" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R15" (BType_Imm Bit64))))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 12w)))|>;
       <|bb_label := BL_Address (Imm64 12w); bb_statements := [];
         bb_last_statement :=
           BStmt_CJmp (BExp_Den (BVar "ProcState_Z" (BType_Imm Bit1)))
             (BLE_Label (BL_Address (Imm64 24w)))
             (BLE_Label (BL_Address (Imm64 16w)))|>;
       <|bb_label := BL_Address (Imm64 16w);
         bb_statements :=
           [BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 4w))) (BExp_Const (Imm64 7w)))
                 (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 4291559424w))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 76w))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 76w)))
                    (BExp_Const (Imm64 4291624832w))));
            BStmt_Observe 0
              (BExp_BinPred BIExp_LessThan (BExp_Const (Imm64 60w))
                 (BExp_BinExp BIExp_Mod
                    (BExp_BinExp BIExp_RightShift
                       (BExp_BinExp BIExp_Plus
                          (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                          (BExp_Const (Imm64 76w))) (BExp_Const (Imm64 6w)))
                    (BExp_Const (Imm64 128w))))
              [BExp_BinExp BIExp_RightShift
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 76w))) (BExp_Const (Imm64 6w))] HD;
            BStmt_Assign (BVar "R10" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 76w))) BEnd_LittleEndian Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 20w)))|>;
       <|bb_label := BL_Address (Imm64 20w); bb_statements := [];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 28w)))|>;
       <|bb_label := BL_Address (Imm64 24w);
         bb_statements :=
           [BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 4291559424w))
                    (BExp_Den (BVar "R9" (BType_Imm Bit64))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 4291624832w))));
            BStmt_Observe 0
              (BExp_BinPred BIExp_LessThan (BExp_Const (Imm64 60w))
                 (BExp_BinExp BIExp_Mod
                    (BExp_BinExp BIExp_RightShift
                       (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 6w))) (BExp_Const (Imm64 128w))))
              [BExp_BinExp BIExp_RightShift
                 (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 6w))] HD;
            BStmt_Assign (BVar "R14" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_Den (BVar "R9" (BType_Imm Bit64))) BEnd_LittleEndian
                 Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 28w)))|>;
       <|bb_label := BL_Address (Imm64 28w); bb_statements := [];
         bb_last_statement := BStmt_Halt (BExp_Const (Imm32 0w))|>]
:bir_val_t bir_program_t
``;

val prog_1_cache_tag_index_part_page = ``
BirProgram
      [<|bb_label := BL_Address (Imm64 0w);
         bb_statements :=
           [BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R14" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 4291559424w))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R14" (BType_Imm Bit64)))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R14" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 4291624832w))));
            BStmt_Observe 0
              (BExp_BinPred BIExp_LessThan (BExp_Const (Imm64 63w))
                 (BExp_BinExp BIExp_Mod
                    (BExp_BinExp BIExp_RightShift
                       (BExp_BinExp BIExp_Plus
                          (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                          (BExp_Den (BVar "R14" (BType_Imm Bit64))))
                       (BExp_Const (Imm64 6w))) (BExp_Const (Imm64 128w))))
              [BExp_BinExp BIExp_RightShift
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R14" (BType_Imm Bit64))))
                 (BExp_Const (Imm64 6w))] HD;
            BStmt_Assign (BVar "R26" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R14" (BType_Imm Bit64))))
                 BEnd_LittleEndian Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 4w)))|>;
       <|bb_label := BL_Address (Imm64 4w);
         bb_statements :=
           [BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_Den (BVar "R17" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 4291559424w))
                    (BExp_Den (BVar "R17" (BType_Imm Bit64))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_Den (BVar "R17" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 4291624832w))));
            BStmt_Observe 0
              (BExp_BinPred BIExp_LessThan (BExp_Const (Imm64 63w))
                 (BExp_BinExp BIExp_Mod
                    (BExp_BinExp BIExp_RightShift
                       (BExp_Den (BVar "R17" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 6w))) (BExp_Const (Imm64 128w))))
              [BExp_BinExp BIExp_RightShift
                 (BExp_Den (BVar "R17" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 6w))] HD;
            BStmt_Assign (BVar "R15" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_Den (BVar "R17" (BType_Imm Bit64))) BEnd_LittleEndian
                 Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 8w)))|>;
       <|bb_label := BL_Address (Imm64 8w);
         bb_statements :=
           [BStmt_Assign (BVar "ProcState_C" (BType_Imm Bit1))
              (BExp_BinPred BIExp_LessOrEqual
                 (BExp_Den (BVar "R15" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R14" (BType_Imm Bit64))));
            BStmt_Assign (BVar "ProcState_N" (BType_Imm Bit1))
              (BExp_BinPred BIExp_SignedLessThan
                 (BExp_BinExp BIExp_Minus
                    (BExp_Den (BVar "R14" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R15" (BType_Imm Bit64))))
                 (BExp_Const (Imm64 0w)));
            BStmt_Assign (BVar "ProcState_V" (BType_Imm Bit1))
              (BExp_BinPred BIExp_Equal
                 (BExp_BinPred BIExp_SignedLessThan
                    (BExp_BinExp BIExp_Minus
                       (BExp_Den (BVar "R14" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R15" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 0w)))
                 (BExp_BinPred BIExp_SignedLessOrEqual
                    (BExp_Den (BVar "R15" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R14" (BType_Imm Bit64)))));
            BStmt_Assign (BVar "ProcState_Z" (BType_Imm Bit1))
              (BExp_BinPred BIExp_Equal
                 (BExp_Den (BVar "R14" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R15" (BType_Imm Bit64))))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 12w)))|>;
       <|bb_label := BL_Address (Imm64 12w); bb_statements := [];
         bb_last_statement :=
           BStmt_CJmp (BExp_Den (BVar "ProcState_Z" (BType_Imm Bit1)))
             (BLE_Label (BL_Address (Imm64 24w)))
             (BLE_Label (BL_Address (Imm64 16w)))|>;
       <|bb_label := BL_Address (Imm64 16w);
         bb_statements :=
           [BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 4w))) (BExp_Const (Imm64 7w)))
                 (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 4291559424w))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 76w))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 76w)))
                    (BExp_Const (Imm64 4291624832w))));
            BStmt_Observe 0
              (BExp_BinPred BIExp_LessThan (BExp_Const (Imm64 63w))
                 (BExp_BinExp BIExp_Mod
                    (BExp_BinExp BIExp_RightShift
                       (BExp_BinExp BIExp_Plus
                          (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                          (BExp_Const (Imm64 76w))) (BExp_Const (Imm64 6w)))
                    (BExp_Const (Imm64 128w))))
              [BExp_BinExp BIExp_RightShift
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 76w))) (BExp_Const (Imm64 6w))] HD;
            BStmt_Assign (BVar "R10" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 76w))) BEnd_LittleEndian Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 20w)))|>;
       <|bb_label := BL_Address (Imm64 20w); bb_statements := [];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 28w)))|>;
       <|bb_label := BL_Address (Imm64 24w);
         bb_statements :=
           [BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 4291559424w))
                    (BExp_Den (BVar "R9" (BType_Imm Bit64))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 4291624832w))));
            BStmt_Observe 0
              (BExp_BinPred BIExp_LessThan (BExp_Const (Imm64 63w))
                 (BExp_BinExp BIExp_Mod
                    (BExp_BinExp BIExp_RightShift
                       (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 6w))) (BExp_Const (Imm64 128w))))
              [BExp_BinExp BIExp_RightShift
                 (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 6w))] HD;
            BStmt_Assign (BVar "R14" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_Den (BVar "R9" (BType_Imm Bit64))) BEnd_LittleEndian
                 Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 28w)))|>;
       <|bb_label := BL_Address (Imm64 28w); bb_statements := [];
         bb_last_statement := BStmt_Halt (BExp_Const (Imm32 0w))|>]
:bir_val_t bir_program_t
``;

(*
=================================
	ldr x26, [x14,x24]
obs0 0x0
obs0 x14+x24
	ldr x15, [x17, #0]
obs0 0x4
obs0 x17
	cmp x14, x15
obs0 0x8
	b.eq #0xC
obs0 0xC
	ldr x10, [x26, #76]
obs1 x9*
obs0 0x10
obs0 x26+76
	b #0x8
obs0 0x14
	ldr x14, [x9]
obs1 x26*+76
obs0 0x18
obs0 x9
	HALT
obs0 0x1C

=================================
*)

val prog_1_cache_speculation = ``
BirProgram
      [<|bb_label := BL_Address (Imm64 0w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w)) [BExp_Const (Imm64 0w)] HD;
            BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R14" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 4291559424w))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R14" (BType_Imm Bit64)))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R14" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 4291624832w))));
            BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R14" (BType_Imm Bit64)))] HD;
            BStmt_Assign (BVar "R26" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R24" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R14" (BType_Imm Bit64))))
                 BEnd_LittleEndian Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 4w)))|>;
       <|bb_label := BL_Address (Imm64 4w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w)) [BExp_Const (Imm64 4w)] HD;
            BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_Den (BVar "R17" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 4291559424w))
                    (BExp_Den (BVar "R17" (BType_Imm Bit64))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_Den (BVar "R17" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 4291624832w))));
            BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_Den (BVar "R17" (BType_Imm Bit64))] HD;
            BStmt_Assign (BVar "R15" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_Den (BVar "R17" (BType_Imm Bit64))) BEnd_LittleEndian
                 Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 8w)))|>;
       <|bb_label := BL_Address (Imm64 8w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w)) [BExp_Const (Imm64 8w)] HD;
            BStmt_Assign (BVar "ProcState_C" (BType_Imm Bit1))
              (BExp_BinPred BIExp_LessOrEqual
                 (BExp_Den (BVar "R15" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R14" (BType_Imm Bit64))));
            BStmt_Assign (BVar "ProcState_N" (BType_Imm Bit1))
              (BExp_BinPred BIExp_SignedLessThan
                 (BExp_BinExp BIExp_Minus
                    (BExp_Den (BVar "R14" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R15" (BType_Imm Bit64))))
                 (BExp_Const (Imm64 0w)));
            BStmt_Assign (BVar "ProcState_V" (BType_Imm Bit1))
              (BExp_BinPred BIExp_Equal
                 (BExp_BinPred BIExp_SignedLessThan
                    (BExp_BinExp BIExp_Minus
                       (BExp_Den (BVar "R14" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R15" (BType_Imm Bit64))))
                    (BExp_Const (Imm64 0w)))
                 (BExp_BinPred BIExp_SignedLessOrEqual
                    (BExp_Den (BVar "R15" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R14" (BType_Imm Bit64)))));
            BStmt_Assign (BVar "ProcState_Z" (BType_Imm Bit1))
              (BExp_BinPred BIExp_Equal
                 (BExp_Den (BVar "R14" (BType_Imm Bit64)))
                 (BExp_Den (BVar "R15" (BType_Imm Bit64))))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 12w)))|>;
       <|bb_label := BL_Address (Imm64 12w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w)) [BExp_Const (Imm64 12w)]
              HD];
         bb_last_statement :=
           BStmt_CJmp (BExp_Den (BVar "ProcState_Z" (BType_Imm Bit1)))
             (BLE_Label (BL_Address (Imm64 24w)))
             (BLE_Label (BL_Address (Imm64 16w)))|>;
       <|bb_label := BL_Address (Imm64 16w);
         bb_statements :=
           [BStmt_Assign (BVar "R9*" (BType_Imm Bit64))
              (BExp_Den (BVar "R9" (BType_Imm Bit64)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 2148532224w))
                    (BExp_Den (BVar "R9*" (BType_Imm Bit64))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_Den (BVar "R9*" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 2148794240w))));
            BStmt_Observe 1 (BExp_Const (Imm1 1w))
              [BExp_Den (BVar "R9*" (BType_Imm Bit64))] HD;
            BStmt_Observe 0 (BExp_Const (Imm1 1w)) [BExp_Const (Imm64 16w)]
              HD;
            BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 4w))) (BExp_Const (Imm64 7w)))
                 (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 4291559424w))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 76w))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 76w)))
                    (BExp_Const (Imm64 4291624832w))));
            BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 76w))] HD;
            BStmt_Assign (BVar "R10" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 76w))) BEnd_LittleEndian Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 20w)))|>;
       <|bb_label := BL_Address (Imm64 20w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w)) [BExp_Const (Imm64 20w)]
              HD];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 28w)))|>;
       <|bb_label := BL_Address (Imm64 24w);
         bb_statements :=
           [BStmt_Assign (BVar "R26*" (BType_Imm Bit64))
              (BExp_Den (BVar "R26" (BType_Imm Bit64)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 2148532224w))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R26*" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 76w))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R26*" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 76w)))
                    (BExp_Const (Imm64 2148794240w))));
            BStmt_Observe 1 (BExp_Const (Imm1 1w))
              [BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "R26*" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 76w))] HD;
            BStmt_Observe 0 (BExp_Const (Imm1 1w)) [BExp_Const (Imm64 24w)]
              HD;
            BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Const (Imm64 4291559424w))
                    (BExp_Den (BVar "R9" (BType_Imm Bit64))))
                 (BExp_BinPred BIExp_LessThan
                    (BExp_Den (BVar "R9" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 4291624832w))));
            BStmt_Observe 0 (BExp_Const (Imm1 1w))
              [BExp_Den (BVar "R9" (BType_Imm Bit64))] HD;
            BStmt_Assign (BVar "R14" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_Den (BVar "R9" (BType_Imm Bit64))) BEnd_LittleEndian
                 Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 28w)))|>;
       <|bb_label := BL_Address (Imm64 28w);
         bb_statements :=
           [BStmt_Observe 0 (BExp_Const (Imm1 1w)) [BExp_Const (Imm64 28w)]
              HD]; bb_last_statement := BStmt_Halt (BExp_Const (Imm32 0w))|>]
:bir_val_t bir_program_t
``;

val prog_1_cache_speculation_first = ``
F
``;

val prog_1_test =
  ("prog_1 - branch and merge", prog_1,
     (prog_1_mem_address_pc,
      prog_1_cache_tag_index,
      prog_1_cache_tag_only,
      prog_1_cache_index_only,
      prog_1_cache_tag_index_part,
      prog_1_cache_tag_index_part_page,
      prog_1_cache_speculation,
      prog_1_cache_speculation_first)
  );


(* ========================= prog_2 - empty program =========================== *)

val prog_2 = ``
BirProgram []
:bir_val_t bir_program_t
``;

val prog_2_mem_address_pc = ``
BirProgram []
:bir_val_t bir_program_t
``;

val prog_2_cache_tag_index = ``
BirProgram []
:bir_val_t bir_program_t
``;

val prog_2_cache_tag_only = ``
BirProgram []
:bir_val_t bir_program_t
``;

val prog_2_cache_index_only = ``
BirProgram []
:bir_val_t bir_program_t
``;

val prog_2_cache_tag_index_part = ``
BirProgram []
:bir_val_t bir_program_t
``;

val prog_2_cache_tag_index_part_page = ``
BirProgram []
:bir_val_t bir_program_t
``;

val prog_2_cache_speculation = ``
F
``;

val prog_2_cache_speculation_first = ``
F
``;

val prog_2_test =
  ("prog_2 - empty program", prog_2,
     (prog_2_mem_address_pc,
      prog_2_cache_tag_index,
      prog_2_cache_tag_only,
      prog_2_cache_index_only,
      prog_2_cache_tag_index_part,
      prog_2_cache_tag_index_part_page,
      prog_2_cache_speculation,
      prog_2_cache_speculation_first)
  );

(* ========================= prog_3 - spectre_v1 =========================== *)

(*
=================================
	cmp x1, x2
	b.hs #0x10
	ldr x4, [x3, x1]
	lsl x4, x4, #0x1
	ldr x6, [x5, x4]
=================================
*)

val prog_3 = ``
BirProgram
       [<|bb_label :=
            BL_Address_HC (Imm64 (0w :word64)) "EB02003F (cmp x1, x2)";
          bb_statements :=
            [(BStmt_Assign (BVar "ProcState_C" BType_Bool)
                (BExp_nzcv_SUB_C (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                   (BExp_Den (BVar "R2" (BType_Imm Bit64)))) :
              bir_val_t bir_stmt_basic_t);
             (BStmt_Assign (BVar "ProcState_N" BType_Bool)
                (BExp_nzcv_SUB_N Bit64
                   (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                   (BExp_Den (BVar "R2" (BType_Imm Bit64)))) :
              bir_val_t bir_stmt_basic_t);
             (BStmt_Assign (BVar "ProcState_V" BType_Bool)
                (BExp_nzcv_SUB_V Bit64
                   (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                   (BExp_Den (BVar "R2" (BType_Imm Bit64)))) :
              bir_val_t bir_stmt_basic_t);
             (BStmt_Assign (BVar "ProcState_Z" BType_Bool)
                (BExp_nzcv_SUB_Z (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                   (BExp_Den (BVar "R2" (BType_Imm Bit64)))) :
              bir_val_t bir_stmt_basic_t)];
          bb_last_statement :=
            BStmt_Jmp (BLE_Label (BL_Address (Imm64 (4w :word64))))|>;
        <|bb_label :=
            BL_Address_HC (Imm64 (4w :word64))
              "54000082 (b.cs 14 <.text+0x14>  // b.hs, b.nlast)";
          bb_statements := ([] :bir_val_t bir_stmt_basic_t list );
          bb_last_statement :=
            BStmt_CJmp (BExp_Den (BVar "ProcState_C" BType_Bool))
              (BLE_Label (BL_Address (Imm64 (20w :word64))))
              (BLE_Label (BL_Address (Imm64 (8w :word64))))|>;
        <|bb_label :=
            BL_Address_HC (Imm64 (8w :word64)) "F8616864 (ldr x4, [x3, x1])";
          bb_statements :=
            [(BStmt_Assert
                (BExp_Aligned Bit64 (3 :num)
                   (BExp_BinExp BIExp_Plus
                      (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                      (BExp_Den (BVar "R3" (BType_Imm Bit64))))) :
              bir_val_t bir_stmt_basic_t);
             (BStmt_Assign (BVar "R4" (BType_Imm Bit64))
                (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                   (BExp_BinExp BIExp_Plus
                      (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                      (BExp_Den (BVar "R3" (BType_Imm Bit64))))
                   BEnd_LittleEndian Bit64) :bir_val_t bir_stmt_basic_t)];
          bb_last_statement :=
            BStmt_Jmp (BLE_Label (BL_Address (Imm64 (12w :word64))))|>;
        <|bb_label :=
            BL_Address_HC (Imm64 (12w :word64)) "D37FF884 (lsl x4, x4, #1)";
          bb_statements :=
            [(BStmt_Assign (BVar "R4" (BType_Imm Bit64))
                (BExp_BinExp BIExp_And
                   (BExp_Const (Imm64 (18446744073709551615w :word64)))
                   (BExp_BinExp BIExp_LeftShift
                      (BExp_Den (BVar "R4" (BType_Imm Bit64)))
                      (BExp_Const (Imm64 (1w :word64))))) :
              bir_val_t bir_stmt_basic_t)];
          bb_last_statement :=
            BStmt_Jmp (BLE_Label (BL_Address (Imm64 (16w :word64))))|>;
        <|bb_label :=
            BL_Address_HC (Imm64 (16w :word64)) "F86468A6 (ldr x6, [x5, x4])";
          bb_statements :=
            [(BStmt_Assert
                (BExp_Aligned Bit64 (3 :num)
                   (BExp_BinExp BIExp_Plus
                      (BExp_Den (BVar "R5" (BType_Imm Bit64)))
                      (BExp_Den (BVar "R4" (BType_Imm Bit64))))) :
              bir_val_t bir_stmt_basic_t);
             (BStmt_Assign (BVar "R6" (BType_Imm Bit64))
                (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                   (BExp_BinExp BIExp_Plus
                      (BExp_Den (BVar "R5" (BType_Imm Bit64)))
                      (BExp_Den (BVar "R4" (BType_Imm Bit64))))
                   BEnd_LittleEndian Bit64) :bir_val_t bir_stmt_basic_t)];
          bb_last_statement :=
            BStmt_Jmp (BLE_Label (BL_Address (Imm64 (20w :word64))))|>;
        <|bb_label := BL_Address (Imm64 (20w :word64));
          bb_statements := ([] :bir_val_t bir_stmt_basic_t list );
          bb_last_statement := BStmt_Halt (BExp_Const (Imm32 (0w :word32)))|>]
:bir_val_t bir_program_t
``;

val prog_3_mem_address_pc = ``
F
``;

val prog_3_cache_tag_index = ``
F
``;

val prog_3_cache_tag_only = ``
F
``;

val prog_3_cache_index_only = ``
F
``;

val prog_3_cache_tag_index_part = ``
F
``;

val prog_3_cache_tag_index_part_page = ``
F
``;

val prog_3_cache_speculation = ``
F
``;

val prog_3_cache_speculation_first = ``
F
``;

val prog_3_test =
  ("prog_3 - spectre_v1", prog_3,
     (prog_3_mem_address_pc,
      prog_3_cache_tag_index,
      prog_3_cache_tag_only,
      prog_3_cache_index_only,
      prog_3_cache_tag_index_part,
      prog_3_cache_tag_index_part_page,
      prog_3_cache_speculation,
      prog_3_cache_speculation_first)
  );


(* ========================= prog_4 - xld_br_yld =========================== *)

(*
=================================
	ldr x17, [x16, #8]
	ldr x25, [x4, #16]
	cmp x10, x28
	b.hs #0x8
	ldr x27, [x26, #8]
=================================
*)

val prog_4 = ``
BirProgram
       [<|bb_label :=
            BL_Address_HC (Imm64 (0w :word64))
              "F9400611 (ldr x17, [x16, #8])";
          bb_statements :=
            [(BStmt_Assert
                (BExp_Aligned Bit64 (3 :num)
                   (BExp_Den (BVar "R16" (BType_Imm Bit64)))) :
              bir_val_t bir_stmt_basic_t);
             (BStmt_Assign (BVar "R17" (BType_Imm Bit64))
                (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                   (BExp_BinExp BIExp_Plus
                      (BExp_Den (BVar "R16" (BType_Imm Bit64)))
                      (BExp_Const (Imm64 (8w :word64)))) BEnd_LittleEndian
                   Bit64) :bir_val_t bir_stmt_basic_t)];
          bb_last_statement :=
            BStmt_Jmp (BLE_Label (BL_Address (Imm64 (4w :word64))))|>;
        <|bb_label :=
            BL_Address_HC (Imm64 (4w :word64))
              "F9400899 (ldr x25, [x4, #16])";
          bb_statements :=
            [(BStmt_Assert
                (BExp_Aligned Bit64 (3 :num)
                   (BExp_Den (BVar "R4" (BType_Imm Bit64)))) :
              bir_val_t bir_stmt_basic_t);
             (BStmt_Assign (BVar "R25" (BType_Imm Bit64))
                (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                   (BExp_BinExp BIExp_Plus
                      (BExp_Den (BVar "R4" (BType_Imm Bit64)))
                      (BExp_Const (Imm64 (16w :word64)))) BEnd_LittleEndian
                   Bit64) :bir_val_t bir_stmt_basic_t)];
          bb_last_statement :=
            BStmt_Jmp (BLE_Label (BL_Address (Imm64 (8w :word64))))|>;
        <|bb_label :=
            BL_Address_HC (Imm64 (8w :word64)) "EB1C015F (cmp x10, x28)";
          bb_statements :=
            [(BStmt_Assign (BVar "ProcState_C" BType_Bool)
                (BExp_nzcv_SUB_C (BExp_Den (BVar "R10" (BType_Imm Bit64)))
                   (BExp_Den (BVar "R28" (BType_Imm Bit64)))) :
              bir_val_t bir_stmt_basic_t);
             (BStmt_Assign (BVar "ProcState_N" BType_Bool)
                (BExp_nzcv_SUB_N Bit64
                   (BExp_Den (BVar "R10" (BType_Imm Bit64)))
                   (BExp_Den (BVar "R28" (BType_Imm Bit64)))) :
              bir_val_t bir_stmt_basic_t);
             (BStmt_Assign (BVar "ProcState_V" BType_Bool)
                (BExp_nzcv_SUB_V Bit64
                   (BExp_Den (BVar "R10" (BType_Imm Bit64)))
                   (BExp_Den (BVar "R28" (BType_Imm Bit64)))) :
              bir_val_t bir_stmt_basic_t);
             (BStmt_Assign (BVar "ProcState_Z" BType_Bool)
                (BExp_nzcv_SUB_Z (BExp_Den (BVar "R10" (BType_Imm Bit64)))
                   (BExp_Den (BVar "R28" (BType_Imm Bit64)))) :
              bir_val_t bir_stmt_basic_t)];
          bb_last_statement :=
            BStmt_Jmp (BLE_Label (BL_Address (Imm64 (12w :word64))))|>;
        <|bb_label :=
            BL_Address_HC (Imm64 (12w :word64))
              "54000042 (b.cs 14 <.text+0x14>  // b.hs, b.nlast)";
          bb_statements := ([] :bir_val_t bir_stmt_basic_t list );
          bb_last_statement :=
            BStmt_CJmp (BExp_Den (BVar "ProcState_C" BType_Bool))
              (BLE_Label (BL_Address (Imm64 (20w :word64))))
              (BLE_Label (BL_Address (Imm64 (16w :word64))))|>;
        <|bb_label :=
            BL_Address_HC (Imm64 (16w :word64))
              "F940075B (ldr x27, [x26, #8])";
          bb_statements :=
            [(BStmt_Assert
                (BExp_Aligned Bit64 (3 :num)
                   (BExp_Den (BVar "R26" (BType_Imm Bit64)))) :
              bir_val_t bir_stmt_basic_t);
             (BStmt_Assign (BVar "R27" (BType_Imm Bit64))
                (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                   (BExp_BinExp BIExp_Plus
                      (BExp_Den (BVar "R26" (BType_Imm Bit64)))
                      (BExp_Const (Imm64 (8w :word64)))) BEnd_LittleEndian
                   Bit64) :bir_val_t bir_stmt_basic_t)];
          bb_last_statement :=
            BStmt_Jmp (BLE_Label (BL_Address (Imm64 (20w :word64))))|>;
        <|bb_label := BL_Address (Imm64 (20w :word64));
          bb_statements := ([] :bir_val_t bir_stmt_basic_t list );
          bb_last_statement := BStmt_Halt (BExp_Const (Imm32 (0w :word32)))|>]
:bir_val_t bir_program_t
``;

val prog_4_mem_address_pc = ``
F
``;

val prog_4_cache_tag_index = ``
F
``;

val prog_4_cache_tag_only = ``
F
``;

val prog_4_cache_index_only = ``
F
``;

val prog_4_cache_tag_index_part = ``
F
``;

val prog_4_cache_tag_index_part_page = ``
F
``;

val prog_4_cache_speculation = ``
F
``;

val prog_4_cache_speculation_first = ``
F
``;

val prog_4_test =
  ("prog_4 - xld_br_yld", prog_4,
     (prog_4_mem_address_pc,
      prog_4_cache_tag_index,
      prog_4_cache_tag_only,
      prog_4_cache_index_only,
      prog_4_cache_tag_index_part,
      prog_4_cache_tag_index_part_page,
      prog_4_cache_speculation,
      prog_4_cache_speculation_first)
  );


(* =========================== test case list to process ============================ *)

val test_cases =
  [prog_1_test, prog_2_test, prog_3_test, prog_4_test]


(* =========================== run and compare test cases ============================ *)

val _ = print "\n\n";

(*
val (name, prog, expected) = hd test_cases;
*)
fun run_test_case (name, prog, expected) =
  let
    val _ = print ("running test case '" ^ name ^ "' ...\n");

    fun fold_obs_add ((m, p), l) =
      if identical p ``F`` then (print ("!!! no expected output for '" ^ m ^ "' !!!\n"); l)
      else (((#add_obs (get_obs_model m)) mem_bounds prog, p)::l);

    val (expected_mem_address_pc,
         expected_cache_tag_index,
         expected_cache_tag_only,
         expected_cache_index_only,
         expected_cache_tag_index_part,
         expected_cache_tag_index_part_page,
         expected_cache_speculation,
         expected_cache_speculation_first) = expected;

    val progs_list_raw =
      [("mem_address_pc",            expected_mem_address_pc),
       ("cache_tag_index",           expected_cache_tag_index),
       ("cache_tag_only",            expected_cache_tag_only),
       ("cache_index_only",          expected_cache_index_only),
       ("cache_tag_index_part",      expected_cache_tag_index_part),
       ("cache_tag_index_part_page", expected_cache_tag_index_part_page),
       ("cache_speculation",         expected_cache_speculation),
       ("cache_speculation_first",   expected_cache_speculation_first)];

    val progs_list = List.foldr fold_obs_add [] progs_list_raw;

    val _ = List.map (fn (t, t_) =>
            if identical t t_ then () else (
            print ("have: ");
            PolyML.print t;
            print ("expecting: ");
            PolyML.print t_;
            raise Fail ("unexpected obs added program: " ^ "\n" ^ (term_to_string prog)))
      ) progs_list;

    val _ = print "\n";

  in () end;

val _ = List.map run_test_case test_cases;
