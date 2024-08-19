(* ------------------------------------------------------------------------- *)
(*  Basic type definition of BIR expressions                                 *)
(* ------------------------------------------------------------------------- *)

open HolKernel Parse bossLib boolLib ;
open wordsTheory ;
open finite_mapTheory ;

val _ = new_theory "bir_basic" ;


(* Identifier for variable name *)
Type ident = ``:string`` ;


(* Immediates *)
Datatype:
  bir_imm_t = 
    Imm1 word1
  | Imm8 word8
  | Imm16 word16
  | Imm32 word32
  | Imm64 word64
  | Imm128 word128
End


(* Immediate Typing size *)
Datatype:
  bir_immtype_t =
  | Bit1
  | Bit8
  | Bit16
  | Bit32
  | Bit64
  | Bit128
End


(* Endian for memory operations *)
Datatype:
  bir_endian_t =
  | BEnd_BigEndian
  | BEnd_LittleEndian
  | BEnd_NoEndian
End


(* Values for evaluation relation *)
Datatype:
  bir_val_t = 
    BVal_Imm bir_imm_t
  | BVal_Mem bir_immtype_t bir_immtype_t (num |-> num) (* Address Type / Value Type *)
End

(* General typing *)
Datatype:
  bir_type_t = 
    BType_Imm bir_immtype_t
  | BType_Mem bir_immtype_t bir_immtype_t (* Address Type / Value Type *)
End



(* Variable to lookup in environment *)
Datatype:
  bir_var_t = BVar ident
End


(* Binary expressions *)
Datatype:
  bir_binexp_t = 
    BIExp_And
  | BIExp_Plus
End

(* Unary expressions *)
Datatype:
  bir_unaryexp_t = 
    BIExp_Not
  | BIExp_ChangeSign
End


(* Binary predicates *)
Datatype:
  bir_binpred_t =
  | BIExp_Equal
  | BIExp_LessThan
End

(* BIR Expressions *)
Datatype:
  bir_exp_t =
    BExp_Const bir_imm_t
  | BExp_MemConst bir_immtype_t bir_immtype_t (num |-> num) (* Address Type / Value Type *)
  | BExp_Den bir_var_t

  | BExp_BinExp bir_binexp_t bir_exp_t bir_exp_t
  | BExp_UnaryExp bir_unaryexp_t bir_exp_t

  | BExp_BinPred bir_binpred_t bir_exp_t bir_exp_t
  | BExp_IfThenElse bir_exp_t bir_exp_t bir_exp_t

  (* Memory value / Address Value (Imm) / Endian / Type of where to load *)
  | BExp_Load bir_exp_t bir_exp_t bir_endian_t bir_immtype_t
  (* Memory value / Address Value (Imm) / Endian / Value to store *)
  | BExp_Store bir_exp_t bir_exp_t bir_endian_t bir_exp_t
End



(* Booleans *)

Definition bool2w_def:
  bool2w b = (if b then 1w else 0w):word1
End

Definition bool2b_def:
  bool2b b = Imm1 (bool2w b)
End

Definition birT_def:
  birT = BVal_Imm (Imm1 1w)
End

Definition birF_def:
  birF = BVal_Imm (Imm1 0w)
End

(* Correction Theorems of boolean functions *)
Theorem bool2b_T_eq_birT:
  BVal_Imm (bool2b T) = birT
Proof
  rw [bool2b_def, bool2w_def, birT_def]
QED

Theorem bool2b_F_eq_birF:
  BVal_Imm (bool2b F) = birF
Proof
  rw [bool2b_def, bool2w_def, birF_def]
QED


(* Utility functions *)
Definition bir_dest_bool_val_def:
  (bir_dest_bool_val (BVal_Imm (Imm1 w)) = SOME (w = 1w)) /\
  (bir_dest_bool_val _ = NONE)
End

Definition val_from_imm_option_def:
  (val_from_imm_option NONE = NONE) /\
  (val_from_imm_option (SOME imm) = SOME (BVal_Imm imm))
End


val _ = export_theory () ;
