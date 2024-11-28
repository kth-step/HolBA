open HolKernel Parse boolLib bossLib;

open wordsTheory;

open bir_symbLib;

open chachaTheory chacha_specTheory;

val _ = new_theory "chacha_symb_exec_quarterround";

(* --------------------------- *)
(* Symbolic analysis execution *)
(* --------------------------- *)

val _ = show_tags := true;

(* ------------ *)
(* quarterround *)
(* ------------ *)

(*
   108a0:	00ab0a3b          	addw	s4,s6,a0
   108a4:	014d4d33          	xor	s10,s10,s4
   108a8:	010d151b          	slliw	a0,s10,0x10
   108ac:	010d5d1b          	srliw	s10,s10,0x10
   108b0:	01a56533          	or	a0,a0,s10

   108b4:	01c5043b          	addw	s0,a0,t3
   108b8:	008b4b33          	xor	s6,s6,s0
   108bc:	00cb179b          	slliw	a5,s6,0xc
   108c0:	014b5b1b          	srliw	s6,s6,0x14
   108c4:	0167e7b3          	or	a5,a5,s6
*)

(*
        <|bb_label :=
            BL_Address_HC (Imm64 0x108A0w) "00AB0A3B (addw s4,s6,a0)";
          bb_statements :=
            [BStmt_Assign (BVar "x20" (BType_Imm Bit64))
               (BExp_Cast BIExp_SignedCast
                  (BExp_Cast BIExp_LowCast
                     (BExp_BinExp BIExp_Plus
                        (BExp_Den (BVar "x10" (BType_Imm Bit64)))
                        (BExp_Den (BVar "x22" (BType_Imm Bit64)))) Bit32)
                  Bit64)];
          bb_last_statement :=
            BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x108A4w)))|>;
        <|bb_label :=
            BL_Address_HC (Imm64 0x108A4w) "014D4D33 (xor s10,s10,s4)";
          bb_statements :=
            [BStmt_Assign (BVar "x26" (BType_Imm Bit64))
               (BExp_BinExp BIExp_Xor
                  (BExp_Den (BVar "x20" (BType_Imm Bit64)))
                  (BExp_Den (BVar "x26" (BType_Imm Bit64))))];
          bb_last_statement :=
            BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x108A8w)))|>;
        <|bb_label :=
            BL_Address_HC (Imm64 0x108A8w) "010D151B (slliw a0,s10,0x10)";
          bb_statements :=
            [BStmt_Assign (BVar "x10" (BType_Imm Bit64))
               (BExp_Cast BIExp_SignedCast
                  (BExp_BinExp BIExp_LeftShift
                     (BExp_Cast BIExp_LowCast
                        (BExp_Den (BVar "x26" (BType_Imm Bit64))) Bit32)
                     (BExp_Const (Imm32 16w))) Bit64)];
          bb_last_statement :=
            BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x108ACw)))|>;
        <|bb_label :=
            BL_Address_HC (Imm64 0x108ACw) "010D5D1B (srliw s10,s10,0x10)";
          bb_statements :=
            [BStmt_Assign (BVar "x26" (BType_Imm Bit64))
               (BExp_Cast BIExp_SignedCast
                  (BExp_BinExp BIExp_RightShift
                     (BExp_Cast BIExp_LowCast
                        (BExp_Den (BVar "x26" (BType_Imm Bit64))) Bit32)
                     (BExp_Const (Imm32 16w))) Bit64)];
          bb_last_statement :=
            BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x108B0w)))|>;
        <|bb_label :=
            BL_Address_HC (Imm64 0x108B0w) "01A56533 (or a0,a0,s10)";
          bb_statements :=
            [BStmt_Assign (BVar "x10" (BType_Imm Bit64))
               (BExp_BinExp BIExp_Or
                  (BExp_Den (BVar "x10" (BType_Imm Bit64)))
                  (BExp_Den (BVar "x26" (BType_Imm Bit64))))];
          bb_last_statement :=
            BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x108B4w)))|>;
*)

val symb_analysis_thm =
 bir_symb_analysis_thm
  bir_chacha_prog_def
  chacha_line_init_addr_def [chacha_line_end_addr_def]
  bspec_chacha_line_pre_def chacha_birenvtyl_def;

val _ = Portable.pprint Tag.pp_tag (tag symb_analysis_thm);

Theorem chacha_line_symb_analysis_thm = symb_analysis_thm

val symb_analysis_thm =
 bir_symb_analysis_thm
  bir_chacha_prog_def
  chacha_other_line_init_addr_def [chacha_other_line_end_addr_def]
  bspec_chacha_line_pre_other_def chacha_birenvtyl_def;

val _ = Portable.pprint Tag.pp_tag (tag symb_analysis_thm);

Theorem chacha_other_line_symb_analysis_thm = symb_analysis_thm

val symb_analysis_thm =
 bir_symb_analysis_thm
  bir_chacha_prog_def
  chacha_quarter_round_init_addr_def [chacha_quarter_round_end_addr_def]
  bspec_chacha_quarter_round_pre_def chacha_birenvtyl_def;

val _ = Portable.pprint Tag.pp_tag (tag symb_analysis_thm);

Theorem chacha_quarter_round_symb_analysis_thm = symb_analysis_thm

val _ = export_theory ();
