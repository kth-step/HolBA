open HolKernel Parse bossLib boolLib ;
open wordsTheory ;

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


(* Values for evaluation relation *)
Datatype:
    bir_val_t = 
        BVal_Imm bir_imm_t
End

(* General typing *)
Datatype:
    bir_type_t = 
        BType_imm bir_immtype_t
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
      | BExp_Den bir_var_t

      | BExp_BinExp bir_binexp_t bir_exp_t bir_exp_t
      | BExp_UnaryExp bir_unaryexp_t bir_exp_t

      | BExp_BinPred bir_binpred_t bir_exp_t bir_exp_t
      | BExp_IfThenElse bir_exp_t bir_exp_t bir_exp_t
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


val _ = export_theory () ;
