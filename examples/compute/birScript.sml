open HolKernel Parse bossLib boolLib
open wordsTheory
open stringTheory


val _ = new_theory "bir"

(** Identifier for variable name *)
Type ident = ``:string``
(* Datatype: *)
(*     ident_t = string *)
(* End *)


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


(** BIR Expressions *)
Datatype:
    bir_exp_t =
        BExp_Const bir_imm_t
      | BExp_Den bir_var_t
      | BExp_BinExp bir_binexp_t bir_exp_t bir_exp_t
End


(* Environment for evaluation *)
(* Type environment = ``:(ident # bir_value_t) list`` *)
Datatype:
    bir_var_environment_t = BEnv (string -> (bir_val_t option))
End

(** Lookup relation *)
Inductive bir_env_lookup:
    !env id. (env id = (SOME a)) ==> bir_env_lookup (BEnv env) id a
End

(** Empty environment *)
Definition bir_empty_env_def:
    bir_empty_env = BEnv (\x. NONE)
End

(** Update environment *)
Definition bir_env_update_def:
    bir_env_update env id v = BEnv ((id =+ SOME v) env)
End


(** Some theorems about bir_env functions *)
Theorem bir_env_lookup_empty:
    !id v. ~(bir_env_lookup bir_empty_env id v)
Proof
    rw [bir_empty_env_def, bir_env_lookup_cases]
QED

Theorem bir_env_lookup_update:
    !env id v. bir_env_lookup (bir_env_update env id v) id v 
Proof
    rw [bir_env_update_def, bir_env_lookup_cases]
QED

(** Gets the operator for a given binary operation *)
Definition bir_binexp_get_oper_def:
    (bir_binexp_get_oper BIExp_And = word_and) /\
    (bir_binexp_get_oper BIExp_Plus = word_add)
End


(** Evaluates a binary expression of two immediates *)
Inductive bir_eval_binexp_imm:
    (!binexp w1 w2. 
        bir_eval_binexp_imm binexp (Imm1 w1) (Imm1 w2) (Imm1 ((bir_binexp_get_oper binexp) w1 w2))) /\
    (!binexp w1 w2. 
        bir_eval_binexp_imm binexp (Imm8 w1) (Imm8 w2) (Imm8 ((bir_binexp_get_oper binexp) w1 w2))) /\
    (!binexp w1 w2. 
        bir_eval_binexp_imm binexp (Imm16 w1) (Imm16 w2) (Imm16 ((bir_binexp_get_oper binexp) w1 w2))) /\
    (!binexp w1 w2. 
        bir_eval_binexp_imm binexp (Imm32 w1) (Imm32 w2) (Imm32 ((bir_binexp_get_oper binexp) w1 w2))) /\
    (!binexp w1 w2. 
        bir_eval_binexp_imm binexp (Imm64 w1) (Imm64 w2) (Imm64 ((bir_binexp_get_oper binexp) w1 w2))) /\
    (!binexp w1 w2. 
        bir_eval_binexp_imm binexp (Imm128 w1) (Imm128 w2) (Imm128 ((bir_binexp_get_oper binexp) w1 w2)))
End

(** TODO : Utility of this function seems low.
*   Might as well use bir_eval_binexp_imm directly.
*   Keeps things tidier I guess *)
(** Evaluates a general binary expression with values as parameters *)
Inductive bir_eval_binexp:
    (!binexp imm1 imm2 imm. 
        (bir_eval_binexp_imm binexp imm1 imm2 imm) ==>
        (bir_eval_binexp binexp (BVal_Imm imm1) (BVal_Imm imm2) (BVal_Imm imm)))
End


Inductive bir_eval_exp:
    (** BExp_Const *)
    ( !env const. bir_eval_exp env (BExp_Const const) (BVal_Imm const) ) /\

    (** BExp_Den *)
    ( !env id. bir_env_lookup env id v ==> bir_eval_exp env (BExp_Den (BVar id)) v) /\

    (** BExp_BinExp *)
    ( !env binexp e1 e2 v1 v2. 
        ((bir_eval_exp env e1 v1) /\ (bir_eval_exp env e2 v2) /\
            (bir_eval_binexp binexp v1 v2 v))
        ==> 
        (bir_eval_exp env (BExp_BinExp binexp e1 e2) v))
End












val _ = export_theory ()
