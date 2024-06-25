open HolKernel Parse bossLib boolLib
open wordsTheory

val _ = new_theory "bir_basic"


(** Identifier for variable name *)
Type ident = ``:string``


(** Immediates *)
Datatype:
    bir_imm_t = 
        Imm1 word1
      | Imm8 word8
      | Imm16 word16
      | Imm32 word32
      | Imm64 word64
      | Imm128 word128
End


(** Values for evaluation relation *)
Datatype:
    bir_val_t = 
        BVal_Imm bir_imm_t
End



(** Variable to lookup in environment *)
Datatype:
    bir_var_t = BVar ident (* bir_type_t *)
End


(** Binary expressions *)
Datatype:
    bir_binexp_t = 
        BIExp_And
      (* | BIExp_Or *)
      | BIExp_Plus
End

Datatype:
    bir_unaryexp_t = 
        BIExp_Not
      | BIExp_ChangeSign
End

(** BIR Expressions *)
Datatype:
    bir_exp_t =
        BExp_Const bir_imm_t
      | BExp_Den bir_var_t
      | BExp_BinExp bir_binexp_t bir_exp_t bir_exp_t
      | BExp_UnaryExp bir_unaryexp_t bir_exp_t
End



val _ = export_theory ()
