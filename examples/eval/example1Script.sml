open HolKernel Parse boolLib bossLib;
open rich_listTheory listTheory arithmeticTheory finite_mapTheory ;
open bir_programTheory ;
open evalwrapLib;

val _ = new_theory "example1";

Definition prog_def:
  prog =
  BirProgram [
  <|bb_label := BL_Address_HC (Imm64 0w) "";
    bb_statements :=
      [
        BStmt_Assign (BVar "_is_locked" $ BType_Imm Bit64)
          $ BExp_Den $ BVar "_crit" $ BType_Imm Bit64 ;
        BStmt_Assign (BVar "_crit_cid" $ BType_Imm Bit64)
            $ BExp_IfThenElse
                (BExp_Cast BIExp_SignedCast
                  (BExp_Den $ BVar "_is_locked" $ BType_Imm Bit64) Bit1)
                (BExp_Den $ BVar "_crit_cid" $ BType_Imm Bit64)
                (BExp_Const $ Imm64 0w);
        BStmt_Assign (BVar "_crit" $ BType_Imm Bit64)
            $ BExp_IfThenElse
                (BExp_Cast BIExp_SignedCast
                  (BExp_Den $ BVar "_is_locked" $ BType_Imm Bit64) Bit1)
                (BExp_Den $ BVar "_crit" $ BType_Imm Bit64)
                (BExp_Const $ Imm64 1w);
      ];
    bb_last_statement :=
        BStmt_CJmp
          (BExp_Cast BIExp_SignedCast
            (BExp_Den $ BVar "_is_locked" $ BType_Imm Bit64) Bit1)
          (BLE_Label $ BL_Address $ Imm64 0w)
          (BLE_Label $ BL_Address $ Imm64 4w);
  |>]
End

Theorem bir_get_current_statement_prog_label0w2 =
  qeval_ctxt [`pc.bpc_label = BL_Address (Imm64 0w)`,`pc.bpc_index = 2`]
    `bir_get_current_statement prog pc`

Theorem bir_get_current_statement_prog_label0w3 =
  qeval_ctxt [`pc.bpc_label = BL_Address (Imm64 0w)`,`pc.bpc_index = 2`]
    `bir_get_current_statement prog (bir_pc_next pc)`

val _ = export_theory();

