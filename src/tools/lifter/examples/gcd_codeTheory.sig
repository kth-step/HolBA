signature gcd_codeTheory =
sig
  type thm = Thm.thm

  (*  Theorems  *)
    val gcd_arm8_program_THM : thm
    val gcd_m0_program_THM : thm

  val gcd_code_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [bir_inst_lifting] Parent theory of "gcd_code"

   [gcd_arm8_program_THM]  Theorem

       []
      |- bir_is_lifted_prog arm8_bmr (WI_end 0w 0x1000000w)
           [(0x400578w,
             [31w; 0w; 1w; 107w; 226w; 3w; 0w; 42w; 64w; 1w; 0w; 84w; 63w;
              0w; 2w; 107w; 64w; 0w; 1w; 75w; 35w; 0w; 2w; 75w; 0w; 176w;
              130w; 26w; 97w; 160w; 129w; 26w; 226w; 3w; 0w; 42w; 63w; 0w;
              0w; 107w; 33w; 255w; 255w; 84w; 192w; 3w; 95w; 214w; 192w;
              3w; 95w; 214w; 0w; 0w; 0w; 0w])]
           (BirProgram
              [<|bb_label :=
                   BL_Address_HC (Imm64 0x400578w) "6B01001F (cmp w0, w1)";
                 bb_statements :=
                   [BStmt_Assign (BVar "ProcState_C" BType_Bool)
                      (BExp_nzcv_SUB_C
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64))) Bit32)
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                            Bit32));
                    BStmt_Assign (BVar "ProcState_N" BType_Bool)
                      (BExp_nzcv_SUB_N Bit32
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64))) Bit32)
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                            Bit32));
                    BStmt_Assign (BVar "ProcState_V" BType_Bool)
                      (BExp_nzcv_SUB_V Bit32
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64))) Bit32)
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                            Bit32));
                    BStmt_Assign (BVar "ProcState_Z" BType_Bool)
                      (BExp_nzcv_SUB_Z
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64))) Bit32)
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40057Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x40057Cw) "2A0003E2 (mov w2, w0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R2" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64))) Bit32)
                         Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400580w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400580w)
                     "54000140 (b.eq 4005a8 <gcd+0x30>)";
                 bb_statements := [];
                 bb_last_statement :=
                   BStmt_CJmp (BExp_Den (BVar "ProcState_Z" BType_Bool))
                     (BLE_Label (BL_Address (Imm64 0x4005A8w)))
                     (BLE_Label (BL_Address (Imm64 0x400584w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400584w) "6B02003F (cmp w1, w2)";
                 bb_statements :=
                   [BStmt_Assign (BVar "ProcState_C" BType_Bool)
                      (BExp_nzcv_SUB_C
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R1" (BType_Imm Bit64))) Bit32)
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R2" (BType_Imm Bit64)))
                            Bit32));
                    BStmt_Assign (BVar "ProcState_N" BType_Bool)
                      (BExp_nzcv_SUB_N Bit32
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R1" (BType_Imm Bit64))) Bit32)
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R2" (BType_Imm Bit64)))
                            Bit32));
                    BStmt_Assign (BVar "ProcState_V" BType_Bool)
                      (BExp_nzcv_SUB_V Bit32
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R1" (BType_Imm Bit64))) Bit32)
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R2" (BType_Imm Bit64)))
                            Bit32));
                    BStmt_Assign (BVar "ProcState_Z" BType_Bool)
                      (BExp_nzcv_SUB_Z
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R1" (BType_Imm Bit64))) Bit32)
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R2" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400588w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400588w)
                     "4B010040 (sub w0, w2, w1)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_Minus
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R2" (BType_Imm Bit64)))
                               Bit32)
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40058Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x40058Cw)
                     "4B020023 (sub w3, w1, w2)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R3" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_BinExp BIExp_Minus
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                               Bit32)
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R2" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400590w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400590w)
                     "1A82B000 (csel w0, w0, w2, lt)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_IfThenElse
                            (BExp_UnaryExp BIExp_Not
                               (BExp_BinPred BIExp_Equal
                                  (BExp_Den
                                     (BVar "ProcState_N" BType_Bool))
                                  (BExp_Den
                                     (BVar "ProcState_V" BType_Bool))))
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                               Bit32)
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R2" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400594w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400594w)
                     "1A81A061 (csel w1, w3, w1, ge)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_IfThenElse
                            (BExp_BinPred BIExp_Equal
                               (BExp_Den (BVar "ProcState_N" BType_Bool))
                               (BExp_Den (BVar "ProcState_V" BType_Bool)))
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R3" (BType_Imm Bit64)))
                               Bit32)
                            (BExp_Cast BIExp_LowCast
                               (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                               Bit32)) Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400598w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400598w) "2A0003E2 (mov w2, w0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "R2" (BType_Imm Bit64))
                      (BExp_Cast BIExp_UnsignedCast
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64))) Bit32)
                         Bit64)];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40059Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x40059Cw) "6B00003F (cmp w1, w0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "ProcState_C" BType_Bool)
                      (BExp_nzcv_SUB_C
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R1" (BType_Imm Bit64))) Bit32)
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32));
                    BStmt_Assign (BVar "ProcState_N" BType_Bool)
                      (BExp_nzcv_SUB_N Bit32
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R1" (BType_Imm Bit64))) Bit32)
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32));
                    BStmt_Assign (BVar "ProcState_V" BType_Bool)
                      (BExp_nzcv_SUB_V Bit32
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R1" (BType_Imm Bit64))) Bit32)
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32));
                    BStmt_Assign (BVar "ProcState_Z" BType_Bool)
                      (BExp_nzcv_SUB_Z
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R1" (BType_Imm Bit64))) Bit32)
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x4005A0w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4005A0w)
                     "54FFFF21 (b.ne 400584 <gcd+0xc>)";
                 bb_statements := [];
                 bb_last_statement :=
                   BStmt_CJmp (BExp_Den (BVar "ProcState_Z" BType_Bool))
                     (BLE_Label (BL_Address (Imm64 0x4005A4w)))
                     (BLE_Label (BL_Address (Imm64 0x400584w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4005A4w) "D65F03C0 (ret)";
                 bb_statements := [];
                 bb_last_statement :=
                   BStmt_Jmp
                     (BLE_Exp (BExp_Den (BVar "R30" (BType_Imm Bit64))))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x4005A8w) "D65F03C0 (ret)";
                 bb_statements := [];
                 bb_last_statement :=
                   BStmt_Jmp
                     (BLE_Exp
                        (BExp_Den (BVar "R30" (BType_Imm Bit64))))|>])

   [gcd_m0_program_THM]  Theorem

       []
      |- bir_is_lifted_prog (m0_bmr (F,T)) (WI_end 0w 0x20000w)
           [(0x10404w,
             [16w; 181w; 3w; 0w; 136w; 66w; 12w; 208w; 88w; 26w; 204w; 26w;
              26w; 0w; 153w; 66w; 0w; 218w; 2w; 0w; 16w; 0w; 153w; 66w; 0w;
              219w; 33w; 0w; 19w; 0w; 145w; 66w; 242w; 209w; 16w; 189w])]
           (BirProgram
              [<|bb_label :=
                   BL_Address_HC (Imm32 0x10404w) "B510 (push {r4, lr})";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit32 0 131072
                         (BExp_BinExp BIExp_Minus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 8w))) 8);
                    BStmt_Assign (BVar "tmp_SP_process" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Minus
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 8w)));
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit32 Bit8))
                      (BExp_Store
                         (BExp_Store
                            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_BinExp BIExp_Minus
                               (BExp_Den
                                  (BVar "SP_process" (BType_Imm Bit32)))
                               (BExp_Const (Imm32 8w))) BEnd_LittleEndian
                            (BExp_Den (BVar "R4" (BType_Imm Bit32))))
                         (BExp_BinExp BIExp_Minus
                            (BExp_Den
                               (BVar "SP_process" (BType_Imm Bit32)))
                            (BExp_Const (Imm32 4w))) BEnd_LittleEndian
                         (BExp_Den (BVar "LR" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "SP_process" (BType_Imm Bit32))
                      (BExp_Den
                         (BVar "tmp_SP_process" (BType_Imm Bit32)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 0x10406w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 0x10406w) "0003 (movs r3, r0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_Den (BVar "R0" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_Den (BVar "R0" (BType_Imm Bit32)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 0x10408w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 0x10408w) "4288 (cmp r0, r1)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_C" BType_Bool)
                      (BExp_nzcv_SUB_C
                         (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R1" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_nzcv_SUB_N Bit32
                         (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R1" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_V" BType_Bool)
                      (BExp_nzcv_SUB_V Bit32
                         (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R1" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_nzcv_SUB_Z
                         (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R1" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 0x1040Aw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 0x1040Aw)
                     "D00C (beq.n 10426 <gcd+0x22>)"; bb_statements := [];
                 bb_last_statement :=
                   BStmt_CJmp (BExp_Den (BVar "PSR_Z" BType_Bool))
                     (BLE_Label (BL_Address (Imm32 0x10426w)))
                     (BLE_Label (BL_Address (Imm32 0x1040Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 0x1040Cw) "1A58 (subs r0, r3, r1)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_C" BType_Bool)
                      (BExp_nzcv_SUB_C
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R1" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_nzcv_SUB_N Bit32
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R1" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_V" BType_Bool)
                      (BExp_nzcv_SUB_V Bit32
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R1" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_nzcv_SUB_Z
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R1" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Minus
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R1" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 0x1040Ew)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 0x1040Ew) "1ACC (subs r4, r1, r3)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_C" BType_Bool)
                      (BExp_nzcv_SUB_C
                         (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_nzcv_SUB_N Bit32
                         (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_V" BType_Bool)
                      (BExp_nzcv_SUB_V Bit32
                         (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_nzcv_SUB_Z
                         (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "R4" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Minus
                         (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 0x10410w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 0x10410w) "001A (movs r2, r3)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_Den (BVar "R3" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R2" (BType_Imm Bit32))
                      (BExp_Den (BVar "R3" (BType_Imm Bit32)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 0x10412w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 0x10412w) "4299 (cmp r1, r3)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_C" BType_Bool)
                      (BExp_nzcv_SUB_C
                         (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_nzcv_SUB_N Bit32
                         (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_V" BType_Bool)
                      (BExp_nzcv_SUB_V Bit32
                         (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_nzcv_SUB_Z
                         (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 0x10414w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 0x10414w)
                     "DA00 (bge.n 10418 <gcd+0x14>)"; bb_statements := [];
                 bb_last_statement :=
                   BStmt_CJmp
                     (BExp_BinPred BIExp_Equal
                        (BExp_Den (BVar "PSR_N" BType_Bool))
                        (BExp_Den (BVar "PSR_V" BType_Bool)))
                     (BLE_Label (BL_Address (Imm32 0x10418w)))
                     (BLE_Label (BL_Address (Imm32 0x10416w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 0x10416w) "0002 (movs r2, r0)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_Den (BVar "R0" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R2" (BType_Imm Bit32))
                      (BExp_Den (BVar "R0" (BType_Imm Bit32)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 0x10418w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 0x10418w) "0010 (movs r0, r2)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_Den (BVar "R2" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R0" (BType_Imm Bit32))
                      (BExp_Den (BVar "R2" (BType_Imm Bit32)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 0x1041Aw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 0x1041Aw) "4299 (cmp r1, r3)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_C" BType_Bool)
                      (BExp_nzcv_SUB_C
                         (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_nzcv_SUB_N Bit32
                         (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_V" BType_Bool)
                      (BExp_nzcv_SUB_V Bit32
                         (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_nzcv_SUB_Z
                         (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R3" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 0x1041Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 0x1041Cw)
                     "DB00 (blt.n 10420 <gcd+0x1c>)"; bb_statements := [];
                 bb_last_statement :=
                   BStmt_CJmp
                     (BExp_BinPred BIExp_Equal
                        (BExp_Den (BVar "PSR_N" BType_Bool))
                        (BExp_Den (BVar "PSR_V" BType_Bool)))
                     (BLE_Label (BL_Address (Imm32 0x1041Ew)))
                     (BLE_Label (BL_Address (Imm32 0x10420w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 0x1041Ew) "0021 (movs r1, r4)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_Den (BVar "R4" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_Den (BVar "R4" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R1" (BType_Imm Bit32))
                      (BExp_Den (BVar "R4" (BType_Imm Bit32)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 0x10420w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 0x10420w) "0013 (movs r3, r2)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_MSB Bit32
                         (BExp_Den (BVar "R2" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_BinPred BIExp_Equal
                         (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 0w)));
                    BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                      (BExp_Den (BVar "R2" (BType_Imm Bit32)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 0x10422w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 0x10422w) "4291 (cmp r1, r2)";
                 bb_statements :=
                   [BStmt_Assign (BVar "PSR_C" BType_Bool)
                      (BExp_nzcv_SUB_C
                         (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R2" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_N" BType_Bool)
                      (BExp_nzcv_SUB_N Bit32
                         (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R2" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_V" BType_Bool)
                      (BExp_nzcv_SUB_V Bit32
                         (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R2" (BType_Imm Bit32))));
                    BStmt_Assign (BVar "PSR_Z" BType_Bool)
                      (BExp_nzcv_SUB_Z
                         (BExp_Den (BVar "R1" (BType_Imm Bit32)))
                         (BExp_Den (BVar "R2" (BType_Imm Bit32))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm32 0x10424w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 0x10424w)
                     "D1F2 (bne.n 1040c <gcd+0x8>)"; bb_statements := [];
                 bb_last_statement :=
                   BStmt_CJmp (BExp_Den (BVar "PSR_Z" BType_Bool))
                     (BLE_Label (BL_Address (Imm32 0x10426w)))
                     (BLE_Label (BL_Address (Imm32 0x1040Cw)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm32 0x10426w) "BD10 (pop {r4, pc})";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit32 2
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32))));
                    BStmt_Assert
                      (BExp_UnaryExp BIExp_Not
                         (BExp_Aligned Bit8 1
                            (BExp_Load
                               (BExp_Den
                                  (BVar "MEM" (BType_Mem Bit32 Bit8)))
                               (BExp_BinExp BIExp_Plus
                                  (BExp_Den
                                     (BVar "SP_process" (BType_Imm Bit32)))
                                  (BExp_Const (Imm32 4w)))
                               BEnd_LittleEndian Bit8)));
                    BStmt_Assert
                      (BExp_UnaryExp BIExp_Not
                         (BExp_Den (BVar "ModeHandler" BType_Bool)));
                    BStmt_Assign (BVar "tmp_PC" (BType_Imm Bit32))
                      (BExp_Align Bit32 1
                         (BExp_Load
                            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                            (BExp_BinExp BIExp_Plus
                               (BExp_Den
                                  (BVar "SP_process" (BType_Imm Bit32)))
                               (BExp_Const (Imm32 4w))) BEnd_LittleEndian
                            Bit32));
                    BStmt_Assign (BVar "R4" (BType_Imm Bit32))
                      (BExp_Load
                         (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32)))
                         BEnd_LittleEndian Bit32);
                    BStmt_Assign (BVar "SP_process" (BType_Imm Bit32))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "SP_process" (BType_Imm Bit32)))
                         (BExp_Const (Imm32 8w)))];
                 bb_last_statement :=
                   BStmt_Jmp
                     (BLE_Exp
                        (BExp_Den (BVar "tmp_PC" (BType_Imm Bit32))))|>])


*)
end
