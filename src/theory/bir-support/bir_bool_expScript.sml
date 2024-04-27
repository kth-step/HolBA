open HolKernel Parse boolLib bossLib;
open bir_auxiliaryLib;
open bir_auxiliaryTheory;
open bir_envTheory bir_valuesTheory;
open bir_immTheory bir_typing_expTheory;
open bir_exp_memTheory bir_expTheory;
open bir_exp_immTheory;
open HolBACoreSimps

val _ = new_theory "bir_bool_exp";


(******************)
(* boolean values *)
(******************)

Definition bir_val_true_def:
  bir_val_true  = BVal_Imm   (Imm1 1w)
End
Definition bir_val_false_def:
  bir_val_false = BVal_Imm   (Imm1 0w)
End

Theorem bir_val_TF_dist:
  (bir_val_false <> bir_val_true)
Proof
SIMP_TAC (std_ss ++ holBACore_ss ++ wordsLib.WORD_ss) [bir_val_false_def, bir_val_true_def]
QED


Theorem type_of_bir_val_TF:
  (type_of_bir_val bir_val_true = BType_Bool) /\
    (type_of_bir_val bir_val_false = BType_Bool)
Proof
SIMP_TAC (std_ss++holBACore_ss) [bir_val_false_def, bir_val_true_def,
  BType_Bool_def]
QED


Theorem bir_val_is_Bool_bool2b_DEF:
  !v. bir_val_is_Bool v <=> ?b. (v = BVal_Imm (bool2b b))
Proof
SIMP_TAC (std_ss++holBACore_ss) [bir_val_is_Bool_def,
  bir_val_is_Imm_s_def] >>
REPEAT STRIP_TAC >> EQ_TAC >> STRIP_TAC >| [
  Cases_on `(n2w n):word1` >>
  Cases_on `(n'=0) \/ (n'=1)` >- METIS_TAC[bool2b_def, bool2w_def] >>
  FULL_SIMP_TAC (arith_ss++wordsLib.WORD_ss) [],

  ASM_SIMP_TAC std_ss [bool2b_def, bool2w_def] >>
  METIS_TAC[]
]
QED


Theorem BVal_Imm_bool2b_TF_DEF:
  !b. (BVal_Imm (bool2b b) = if b then bir_val_true else bir_val_false)
Proof
Cases >> SIMP_TAC (std_ss++holBACore_ss) [bir_val_true_def, bir_val_false_def]
QED

Theorem bir_val_TF_bool2b_DEF:
  (bir_val_true = BVal_Imm (bool2b T)) /\
    (bir_val_false = BVal_Imm (bool2b F))
Proof
SIMP_TAC std_ss [BVal_Imm_bool2b_TF_DEF]
QED

Theorem BVal_Imm_bool2b_EQ_TF_REWRS:
  (!b. (BVal_Imm (bool2b b) = bir_val_true) <=> b) /\
    (!b. (BVal_Imm (bool2b b) = bir_val_false) <=> ~b)
Proof
SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss) [BVal_Imm_bool2b_TF_DEF,
  bir_val_TF_dist]
QED


Theorem bir_val_is_Bool_ALT_DEF:
  !v. bir_val_is_Bool v <=> ((v = bir_val_false) \/ (v = bir_val_true))
Proof
SIMP_TAC std_ss [bir_val_is_Bool_bool2b_DEF, BVal_Imm_bool2b_TF_DEF] >>
METIS_TAC[]
QED


Theorem bir_dest_bool_val_TF:
  ((bir_dest_bool_val bir_val_false) = SOME F) /\
    ((bir_dest_bool_val bir_val_true) = SOME T)
Proof
SIMP_TAC (std_ss++wordsLib.WORD_ss) [bir_val_false_def, bir_val_true_def, bir_dest_bool_val_def]
QED


Theorem bool2w_ELIMS:
  (!b. ((bool2w b = 0w) <=> ~b)) /\
    (!b. ((bool2w b = 1w) <=> b)) /\
    (!b1 b2. (bool2w b1 = bool2w b2) <=> (b1 = b2))
Proof
SIMP_TAC (std_ss++holBACore_ss++boolSimps.LIFT_COND_ss++
  wordsLib.WORD_ss) [bool2w_def]
QED


Theorem bool2b_ELIMS:
  (!b w. ((bool2b b = Imm1 w) <=> (bool2w b = w))) /\
    (!b1 b2. (bool2b b1 = bool2b b2) <=> (b1 = b2))
Proof
SIMP_TAC (std_ss++holBACore_ss++boolSimps.LIFT_COND_ss) [bool2b_def, bool2w_ELIMS]
QED


Theorem bir_val_is_Bool_bool2b:
  !b. bir_val_is_Bool (BVal_Imm (bool2b b))
Proof
SIMP_TAC (std_ss++holBACore_ss) [bir_val_is_Bool_ALT_DEF]
QED


Definition bir_mk_bool_val_def:
  bir_mk_bool_val b = BVal_Imm (bool2b b)
End

Theorem bir_mk_bool_val_is_bool:
  !b. bir_val_is_Bool (bir_mk_bool_val b)
Proof
SIMP_TAC std_ss [bir_mk_bool_val_def, bir_val_is_Bool_bool2b]
QED


Theorem bir_mk_bool_val_ALT_DEF_TF:
  !b. bir_mk_bool_val b = (if b then bir_val_true else bir_val_false)
Proof
SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss) [bir_mk_bool_val_def, bool2b_def, bir_val_true_def, bir_val_false_def, bool2w_def]
QED

Theorem bir_mk_bool_val_true_thm:
  !v1.
      (bir_mk_bool_val v1 = bir_val_true) = v1
Proof
RW_TAC std_ss [bir_mk_bool_val_ALT_DEF_TF, 
               bir_val_false_def, bir_val_true_def, word1_distinct]
QED

Theorem bir_mk_bool_val_inv:
  !b. bir_dest_bool_val (bir_mk_bool_val b) = SOME b
Proof
Cases >> SIMP_TAC std_ss [bir_mk_bool_val_ALT_DEF_TF, bir_dest_bool_val_TF]
QED


Theorem bir_dest_bool_val_inv:
  !b v. (bir_dest_bool_val v = SOME b) ==> (v = bir_mk_bool_val b)
Proof
REPEAT STRIP_TAC >>
MP_TAC (Q.SPEC `v` bir_dest_bool_val_EQ_NONE) >>
ASM_SIMP_TAC std_ss [bir_val_is_Bool_ALT_DEF] >>
STRIP_TAC >> (
  FULL_SIMP_TAC std_ss [bir_dest_bool_val_TF, bir_mk_bool_val_ALT_DEF_TF]
)
QED


Theorem bir_dest_bool_val_EQ_SOME:
  !v b. ((bir_dest_bool_val v) = SOME b) <=>
          (v = bir_mk_bool_val b)
Proof
METIS_TAC[bir_dest_bool_val_inv, bir_mk_bool_val_inv]
QED


Theorem bir_dest_bool_val_IS_SOME:
  !v. IS_SOME (bir_dest_bool_val v) <=>
        bir_val_is_Bool v
Proof
GEN_TAC >>
MP_TAC (Q.SPEC `v` bir_dest_bool_val_EQ_NONE) >>
Cases_on `bir_dest_bool_val v` >> (
  ASM_SIMP_TAC std_ss []
)
QED



(***********************)
(* boolean expressions *)
(***********************)

Definition bir_exp_true_def:
  bir_exp_true  = BExp_Const (Imm1 1w)
End
Definition bir_exp_false_def:
  bir_exp_false = BExp_Const (Imm1 0w)
End

Theorem bir_eval_exp_TF:
  (!env. bir_eval_exp bir_exp_true env = SOME bir_val_true) /\
    (!env. bir_eval_exp bir_exp_false env = SOME bir_val_false)
Proof
SIMP_TAC std_ss [bir_exp_false_def, bir_exp_true_def, bir_eval_exp_def,
  bir_val_true_def, bir_val_false_def]
QED


Definition bir_is_bool_exp_def:
  bir_is_bool_exp e <=>
  (type_of_bir_exp e = SOME (BType_Imm Bit1))
End

(* Conditional rewrite *)
Theorem bir_is_bool_exp_GSYM:
  !ex.
      (type_of_bir_exp ex = SOME BType_Bool) =
        (bir_is_bool_exp ex)
Proof
RW_TAC std_ss [BType_Bool_def, GSYM bir_is_bool_exp_def]
QED

Theorem bir_number_of_mem_splits_BitResult:
  !vty aty. bir_number_of_mem_splits vty Bit1 aty =
              (if vty = Bit1 then SOME 1 else NONE)
Proof
REPEAT STRIP_TAC >>
SIMP_TAC std_ss [bir_number_of_mem_splits_def, size_of_bir_immtype_def] >>
Cases_on `size_of_bir_immtype vty = 1` >- (
  FULL_SIMP_TAC arith_ss [bitTheory.ONE_LE_TWOEXP,
    size_of_bir_immtype_EQ_REWRS, size_of_bir_immtype_def]
) >>
`size_of_bir_immtype vty <> 0` by METIS_TAC[bir_immTheory.size_of_bir_immtype_NEQ_0] >>
`1 < size_of_bir_immtype vty` by DECIDE_TAC >>
ASM_SIMP_TAC arith_ss [] >>
METIS_TAC[size_of_bir_immtype_def]
QED


Theorem bir_is_bool_exp_REWRS:
  (bir_is_bool_exp bir_exp_false) /\
  (bir_is_bool_exp bir_exp_true) /\

  (!c. (bir_is_bool_exp (BExp_Const c) <=> (type_of_bir_imm c = Bit1))) /\

  (!v. (bir_is_bool_exp (BExp_Den v) <=> (BType_Imm Bit1 = bir_var_type v))) /\

  (!uo e. (bir_is_bool_exp (BExp_UnaryExp uo e) <=> bir_is_bool_exp e)) /\

  (!bo e1 e2. (bir_is_bool_exp (BExp_BinExp bo e1 e2) <=>
     (bir_is_bool_exp e1 /\ bir_is_bool_exp e2))) /\

  (!bo e1 e2. (bir_is_bool_exp (BExp_BinPred bo e1 e2) <=>
     ?it. (type_of_bir_exp e1 = SOME (BType_Imm it)) /\
          (type_of_bir_exp e2 = SOME (BType_Imm it)))) /\

  (!bo e1 e2. (bir_is_bool_exp (BExp_MemEq e1 e2) <=>
     ?at vt. (type_of_bir_exp e1 = SOME (BType_Mem at vt)) /\
             (type_of_bir_exp e2 = SOME (BType_Mem at vt)))) /\

  (!ec e1 e2. (bir_is_bool_exp (BExp_IfThenElse ec e1 e2) <=>
     bir_is_bool_exp ec /\ bir_is_bool_exp e1 /\ bir_is_bool_exp e2)) /\

  (!ct e s. (bir_is_bool_exp (BExp_Cast ct e s) <=>
     ((s = Bit1) /\ (?it. (type_of_bir_exp e = SOME (BType_Imm it)))))) /\

  (!ae me en s. (bir_is_bool_exp (BExp_Load ae me en s) <=>
     ((s = Bit1) /\ (?at.
     (type_of_bir_exp ae = SOME (BType_Mem at Bit1)) /\
     (type_of_bir_exp me = SOME (BType_Imm at)))))) /\

  (!ae me ve en. (bir_is_bool_exp (BExp_Store ae me en ve) <=>  F))
Proof
SIMP_TAC (std_ss++holBACore_ss++boolSimps.EQUIV_EXTRACT_ss) [bir_is_bool_exp_def,
  bir_exp_true_def, bir_exp_false_def, BType_Bool_def,
  bir_number_of_mem_splits_BitResult] >> METIS_TAC []
QED


(* TODO: Rename? *)
Theorem bir_eval_TF_is_bool:
  !ex env w.
    (bir_eval_exp ex env = SOME (BVal_Imm (Imm1 w))) ==>
    bir_is_bool_exp ex
Proof
REPEAT STRIP_TAC >>
IMP_RES_TAC bir_eval_exp_IS_SOME_IMPLIES_TYPE >>
QSPECL_X_ASSUM ``!ty. _`` [`BType_Imm Bit1`] >>
FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_is_bool_exp_def]
QED


(*************************)
(* convenient shorthands *)
(*************************)

Definition bir_exp_or_def:
  bir_exp_or  e1 e2 = BExp_BinExp   BIExp_Or  e1 e2
End
Definition bir_exp_and_def:
  bir_exp_and e1 e2 = BExp_BinExp   BIExp_And e1 e2
End
Definition bir_exp_not_def:
  bir_exp_not e     = BExp_UnaryExp BIExp_Not e
End
Definition bir_exp_imp_def:
  bir_exp_imp e1 e2 = bir_exp_or (bir_exp_not e1) e2
End

Theorem bir_exp_imp_or_thm:
  !e1 e2. bir_exp_imp e1 e2 = bir_exp_or (bir_exp_not e1) e2
Proof
REWRITE_TAC [bir_exp_imp_def]
QED

Theorem bir_bool_shorthands_REWRS:
  (!e1 e2. (bir_exp_or  e1 e2) = (BExp_BinExp   BIExp_Or  e1 e2))
  /\ (!e1 e2. (bir_exp_and e1 e2) = (BExp_BinExp   BIExp_And e1 e2))
  /\ (!e    . (bir_exp_not e    ) = (BExp_UnaryExp BIExp_Not e    ))
  /\ (!e1 e2. (bir_exp_imp e1 e2) = (bir_exp_or (bir_exp_not e1) e2))
Proof
REWRITE_TAC [
    bir_exp_or_def,
    bir_exp_and_def,
    bir_exp_not_def,
    bir_exp_imp_def
  ]
QED

(*********************************************)
(* boolean expressions properly typed in env *)
(*********************************************)

Definition bir_is_bool_exp_env_def:
  bir_is_bool_exp_env env e <=>
  (bir_is_bool_exp e /\
   (bir_env_vars_are_initialised env (bir_vars_of_exp e)))
End

(* Conditional rewrite *)
Theorem bir_is_bool_exp_env_GSYM:
  !env e.
      bir_is_bool_exp e ==>
      ((bir_env_vars_are_initialised env (bir_vars_of_exp e)) =
        bir_is_bool_exp_env env e)
Proof
RW_TAC std_ss [bir_is_bool_exp_env_def]
QED

Theorem bir_is_bool_exp_env_IMPLIES_dest_bool_val:
  !env e. bir_is_bool_exp_env env e ==> bir_is_bool_exp e
Proof
SIMP_TAC std_ss [bir_is_bool_exp_env_def]
QED


Theorem bir_is_bool_exp_env_IMPLIES_EVAL_IS_BOOL:
  !env e. bir_is_bool_exp_env env e ==>
      ?va. (bir_eval_exp e env = SOME va) /\ (bir_val_is_Bool va)
Proof
SIMP_TAC std_ss [bir_is_bool_exp_env_def, bir_is_bool_exp_def] >>
REPEAT STRIP_TAC >>
`?va. (bir_eval_exp e env = SOME va) /\ (type_of_bir_val va = BType_Imm Bit1)` by
  METIS_TAC[type_of_bir_exp_THM_with_init_vars] >>
FULL_SIMP_TAC (std_ss++holBACore_ss) [type_of_bir_val_EQ_ELIMS,
  bir_val_is_Bool_def]
QED

Theorem bir_bool_values:
  !env ex.
      bir_is_bool_exp_env env ex ==>
       (((bir_eval_exp ex env) = SOME bir_val_false) \/
        ((bir_eval_exp ex env) = SOME bir_val_true)
       )
Proof
REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_is_bool_exp_env_def, 
                      bir_is_bool_exp_def] >>
IMP_RES_TAC type_of_bir_exp_THM_with_init_vars >>
Cases_on `(bir_eval_exp ex env)` >> (
  Cases_on `va` >> FULL_SIMP_TAC (std_ss++holBACore_ss) [type_of_bir_val_def] >> (
    rename1 `(BVal_Imm b = bir_val_false)` >>
    Cases_on `b` >- (
      SUBGOAL_THEN
        ``!c.
            ((BVal_Imm (Imm1 c)) = bir_val_true) \/
            ((BVal_Imm (Imm1 c)) = bir_val_false)``
        (fn thm => METIS_TAC [thm]) >- (
           FULL_SIMP_TAC (std_ss++holBACore_ss++wordsLib.WORD_ss++
                          wordsLib.WORD_BIT_EQ_ss)
             [bir_val_true_def, bir_val_false_def] >>
           METIS_TAC []
        )
    ) >> (
      FULL_SIMP_TAC (std_ss++holBACore_ss) [type_of_bir_imm_def]
    )
  )
)
QED


Definition bir_eval_bool_exp_def:
  bir_eval_bool_exp env e =
  THE (bir_dest_bool_val (THE (bir_eval_exp env e)))
End



Theorem bir_eval_bool_exp_INTRO:
  !env e. bir_is_bool_exp_env env e ==>
      (bir_eval_exp e env = SOME (bir_mk_bool_val (bir_eval_bool_exp e env)))
Proof
REPEAT STRIP_TAC >>
IMP_RES_TAC bir_is_bool_exp_env_IMPLIES_EVAL_IS_BOOL >>
FULL_SIMP_TAC std_ss [bir_eval_bool_exp_def, GSYM bir_dest_bool_val_IS_SOME,
  optionTheory.IS_SOME_EXISTS] >>
METIS_TAC[bir_dest_bool_val_inv]
QED




Theorem bir_is_bool_exp_env_REWRS:
  (bir_is_bool_exp_env env bir_exp_false) /\
  (bir_is_bool_exp_env env bir_exp_true) /\

  (!c. (bir_is_bool_exp_env env (BExp_Const c) <=> ((type_of_bir_imm c = Bit1)))) /\

  (!v. (bir_is_bool_exp_env env (BExp_Den v) <=> (
     bir_env_var_is_initialised env v /\
     (BType_Imm Bit1 = bir_var_type v)))) /\

  (!uo e. (bir_is_bool_exp_env env (BExp_UnaryExp uo e) <=> bir_is_bool_exp_env env e)) /\

  (!bo e1 e2. (bir_is_bool_exp_env env (BExp_BinExp bo e1 e2) <=>
     (bir_is_bool_exp_env env e1 /\ bir_is_bool_exp_env env e2))) /\

  (!bo e1 e2. (bir_is_bool_exp_env env (BExp_BinPred bo e1 e2) <=> (
     bir_env_vars_are_initialised env (bir_vars_of_exp e1) /\
     bir_env_vars_are_initialised env (bir_vars_of_exp e2) /\
     ?it. (type_of_bir_exp e1 = SOME (BType_Imm it)) /\
          (type_of_bir_exp e2 = SOME (BType_Imm it))))) /\

  (!ec e1 e2. (bir_is_bool_exp_env env (BExp_IfThenElse ec e1 e2) <=>
     bir_is_bool_exp_env env ec /\ bir_is_bool_exp_env env e1 /\ bir_is_bool_exp_env env e2)) /\

  (!ct e s. (bir_is_bool_exp_env env (BExp_Cast ct e s) <=>
     ((s = Bit1) /\
     bir_env_vars_are_initialised env (bir_vars_of_exp e) /\
     (?it. (type_of_bir_exp e = SOME (BType_Imm it)))))) /\

  (!ae me en s. (bir_is_bool_exp_env env (BExp_Load ae me en s) <=>
     ((s = Bit1) /\
      bir_env_vars_are_initialised env (bir_vars_of_exp me) /\
      bir_env_vars_are_initialised env (bir_vars_of_exp ae) /\
     (?at.
     (type_of_bir_exp ae = SOME (BType_Mem at Bit1)) /\
     (type_of_bir_exp me = SOME (BType_Imm at)))))) /\

  (!ae me ve en. (bir_is_bool_exp_env env (BExp_Store ae me en ve) <=>  F))
Proof
SIMP_TAC (std_ss++holBACore_ss++boolSimps.EQUIV_EXTRACT_ss) [bir_is_bool_exp_env_def,
  bir_is_bool_exp_REWRS, bir_exp_false_def, bir_exp_true_def,
  bir_vars_of_exp_def, bir_env_oldTheory.bir_env_vars_are_initialised_UNION,
  bir_env_oldTheory.bir_env_vars_are_initialised_EMPTY, bir_env_oldTheory.bir_env_vars_are_initialised_INSERT]
QED



Theorem bir_eval_bool_exp_TF:
  (!env. (bir_eval_bool_exp bir_exp_true env) = T) /\
    (!env. (bir_eval_bool_exp bir_exp_false env) = F)
Proof
SIMP_TAC (std_ss++holBACore_ss) [bir_eval_bool_exp_def, bir_eval_exp_TF,
  bir_dest_bool_val_TF]
QED


Theorem bir_eval_bool_exp_BExp_Const_bool2b:
  (!env b. (bir_eval_bool_exp (BExp_Const (bool2b b)) env) = b)
Proof
SIMP_TAC (std_ss++holBACore_ss) [bir_eval_bool_exp_def, GSYM bir_mk_bool_val_def,
  bir_mk_bool_val_inv]
QED



Definition bir_bin_exp_GET_BOOL_OPER_def:
  (bir_bin_exp_GET_BOOL_OPER BIExp_And = SOME (T, $/\)) /\
   (bir_bin_exp_GET_BOOL_OPER BIExp_Or = SOME (T, $\/)) /\
   (bir_bin_exp_GET_BOOL_OPER BIExp_Xor = SOME (F, (\b1 b2. ~(b1 = b2)))) /\
   (bir_bin_exp_GET_BOOL_OPER BIExp_Plus = SOME (F, (\b1 b2. ~(b1 = b2)))) /\
   (bir_bin_exp_GET_BOOL_OPER BIExp_Minus = SOME (F, (\b1 b2. ~(b1 = b2)))) /\
   (bir_bin_exp_GET_BOOL_OPER BIExp_Mult = SOME (F, $/\ )) /\
   (bir_bin_exp_GET_BOOL_OPER BIExp_Div = NONE) /\
   (bir_bin_exp_GET_BOOL_OPER BIExp_SignedDiv = NONE) /\
   (bir_bin_exp_GET_BOOL_OPER BIExp_Mod =  NONE) /\
   (bir_bin_exp_GET_BOOL_OPER BIExp_SignedMod = NONE) /\
   (bir_bin_exp_GET_BOOL_OPER BIExp_LeftShift = SOME (F, \b1 b2. b1 /\ ~b2)) /\
   (bir_bin_exp_GET_BOOL_OPER BIExp_RightShift = SOME (F, \b1 b2. b1 /\ ~b2)) /\
   (bir_bin_exp_GET_BOOL_OPER BIExp_SignedRightShift = SOME (F, \b1 b2. b1)) /\
   (bir_bin_exp_GET_BOOL_OPER _ = NONE) (* Should never fire *)
End


Theorem bir_bin_exp_GET_BOOL_OPER_THM:
  !uo de b1 b2 bop. (bir_bin_exp_GET_BOOL_OPER uo = SOME (de, bop)) ==>
                      (bir_bin_exp uo (bool2b b1) (bool2b b2) =
                      (bool2b (bop b1 b2)))
Proof
SIMP_TAC (std_ss++holBACore_ss) [bool2b_def, bir_bin_exp_REWRS] >>
Cases_on `uo` >> (
  Cases_on `b1` >> Cases_on `b2` >> (
    SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss++wordsLib.WORD_ss) [bool2w_def, bir_bin_exp_REWRS,
      bool2b_def, bir_bin_exp_GET_BOOL_OPER_def, bir_bin_exp_GET_OPER_def]
  )
)
QED

Theorem bir_bin_exp_BOOL_OPER_EVAL = SIMP_RULE (std_ss++DatatypeSimps.expand_type_quants_ss[``:bir_bin_exp_t``]) [
     FORALL_AND_THM, bir_bin_exp_GET_BOOL_OPER_def] bir_bin_exp_GET_BOOL_OPER_THM



Theorem bir_eval_bool_exp_BExp_BinExp:
  !de uo bop env e1 e2.
       (bir_bin_exp_GET_BOOL_OPER uo = SOME (de, bop)) ==>
       bir_is_bool_exp_env env (BExp_BinExp uo e1 e2) ==> (
       (bir_eval_bool_exp (BExp_BinExp uo e1 e2) env) <=>
        bop (bir_eval_bool_exp e1 env) (bir_eval_bool_exp e2 env))
Proof
SIMP_TAC std_ss [bir_eval_bool_exp_def, bir_eval_exp_def, bir_eval_bin_exp_def,
   bir_is_bool_exp_env_REWRS] >>
REPEAT STRIP_TAC >>
`?b1. bir_eval_exp e1 env = SOME (bir_mk_bool_val b1)` by METIS_TAC[bir_eval_bool_exp_INTRO] >>
`?b2. bir_eval_exp e2 env = SOME (bir_mk_bool_val b2)` by METIS_TAC[bir_eval_bool_exp_INTRO] >>
FULL_SIMP_TAC std_ss [bir_mk_bool_val_inv] >>
ASM_SIMP_TAC std_ss [bir_eval_bin_exp_def, bir_mk_bool_val_def,
  type_of_bool2b] >>
`bir_bin_exp uo (bool2b b1) (bool2b b2) = bool2b (bop b1 b2)` by METIS_TAC[
   bir_bin_exp_GET_BOOL_OPER_THM] >>
ASM_SIMP_TAC std_ss [bir_mk_bool_val_inv, GSYM bir_mk_bool_val_def]
QED


Theorem bir_eval_bool_exp_BExp_BinExp_REWRS = SIMP_RULE (std_ss++DatatypeSimps.expand_type_quants_ss [``:bir_bin_exp_t``]) [
    bir_bin_exp_GET_BOOL_OPER_def, bir_is_bool_exp_env_REWRS, FORALL_AND_THM]
    bir_eval_bool_exp_BExp_BinExp


Theorem bir_eval_bool_exp_BExp_BinExp_REWRS_GSYM = GSYM (SIMP_RULE (std_ss++DatatypeSimps.expand_type_quants_ss [``:bir_bin_exp_t``]) [
    bir_bin_exp_GET_BOOL_OPER_def, bir_is_bool_exp_env_REWRS, FORALL_AND_THM]
    (SPEC T bir_eval_bool_exp_BExp_BinExp))





Definition bir_bin_pred_GET_BOOL_OPER_def:
  (bir_bin_pred_GET_BOOL_OPER BIExp_Equal = SOME (T, $=)) /\
   (bir_bin_pred_GET_BOOL_OPER BIExp_NotEqual = SOME (T, $<>)) /\
   (bir_bin_pred_GET_BOOL_OPER BIExp_LessThan = SOME (F, (\b1 b2. ~b1 /\ b2))) /\
   (bir_bin_pred_GET_BOOL_OPER BIExp_SignedLessThan = SOME (F, (\b1 b2. b1 /\ ~b2))) /\
   (bir_bin_pred_GET_BOOL_OPER BIExp_LessOrEqual = SOME (T, $==>)) /\
   (bir_bin_pred_GET_BOOL_OPER BIExp_SignedLessOrEqual = SOME (F, \b1 b2. b2 ==> b1))
End


Theorem bir_bin_pred_GET_BOOL_OPER_THM:
  !uo de b1 b2 bop. (bir_bin_pred_GET_BOOL_OPER uo = SOME (de, bop)) ==>
                      (bir_bin_pred uo (bool2b b1) (bool2b b2) =
                      (bop b1 b2))
Proof
SIMP_TAC (std_ss++holBACore_ss) [bool2b_def, bir_bin_pred_REWRS] >>
Cases_on `uo` >> (
  Cases_on `b1` >> Cases_on `b2` >> (
    SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss++wordsLib.WORD_ss) [bool2w_def, bir_bin_pred_REWRS,
      bool2b_def, bir_bin_pred_GET_BOOL_OPER_def, bir_bin_pred_GET_OPER_def]
  )
)
QED


Theorem bir_bin_pred_BOOL_OPER_EVAL = SIMP_RULE (std_ss++DatatypeSimps.expand_type_quants_ss[``:bir_bin_pred_t``]) [
     FORALL_AND_THM, bir_bin_pred_GET_BOOL_OPER_def] bir_bin_pred_GET_BOOL_OPER_THM


Theorem bir_eval_bool_exp_BExp_BinPred:
  !de uo bop env e1 e2.
       (bir_bin_pred_GET_BOOL_OPER uo = SOME (de, bop)) ==>
       bir_is_bool_exp_env env e1 ==>
       bir_is_bool_exp_env env e2 ==> (
       (bir_eval_bool_exp (BExp_BinPred uo e1 e2) env) <=>
        bop (bir_eval_bool_exp e1 env) (bir_eval_bool_exp e2 env))
Proof
SIMP_TAC std_ss [bir_eval_bool_exp_def, bir_eval_exp_def, bir_eval_bin_pred_def,
   bir_is_bool_exp_env_REWRS] >>
REPEAT STRIP_TAC >>
`?b1. bir_eval_exp e1 env = SOME (bir_mk_bool_val b1)` by METIS_TAC[bir_eval_bool_exp_INTRO] >>
`?b2. bir_eval_exp e2 env = SOME (bir_mk_bool_val b2)` by METIS_TAC[bir_eval_bool_exp_INTRO] >>
FULL_SIMP_TAC std_ss [bir_mk_bool_val_inv] >>
ASM_SIMP_TAC std_ss [bir_eval_bin_pred_def, bir_mk_bool_val_def,
  type_of_bool2b] >>
`bir_bin_pred uo (bool2b b1) (bool2b b2) = bop b1 b2` by METIS_TAC[
   bir_bin_pred_GET_BOOL_OPER_THM] >>
ASM_SIMP_TAC std_ss [bir_mk_bool_val_inv, GSYM bir_mk_bool_val_def]
QED


Theorem bir_eval_bool_exp_BExp_BinPred_REWRS = SIMP_RULE (std_ss++DatatypeSimps.expand_type_quants_ss [``:bir_bin_pred_t``]) [
    bir_bin_pred_GET_BOOL_OPER_def, bir_is_bool_exp_env_REWRS, FORALL_AND_THM]
    bir_eval_bool_exp_BExp_BinPred


Theorem bir_eval_bool_exp_BExp_BinPred_REWRS_GSYM = GSYM (SIMP_RULE (std_ss++DatatypeSimps.expand_type_quants_ss [``:bir_bin_pred_t``]) [
    bir_bin_pred_GET_BOOL_OPER_def, bir_is_bool_exp_env_REWRS, FORALL_AND_THM]
    (SPEC T bir_eval_bool_exp_BExp_BinPred))



(* the first bool seems to be indicating whether the second function is
replaced by the lifter with the corresponding BIR expression, we only want
to do this for a boolean negation operation everything else is not useful *)
Definition bir_unary_exp_GET_BOOL_OPER_def:
  (bir_unary_exp_GET_BOOL_OPER BIExp_Not        = SOME (T, $~)) /\
   (bir_unary_exp_GET_BOOL_OPER BIExp_ChangeSign = SOME (F, (\b. b))) /\
   (bir_unary_exp_GET_BOOL_OPER BIExp_CLZ        = SOME (F, $~)) /\
   (bir_unary_exp_GET_BOOL_OPER BIExp_CLS        = SOME (F, (\b. F))) /\
   (bir_unary_exp_GET_BOOL_OPER _                = NONE) (* Should not fire *)
End


Theorem bir_unary_exp_GET_BOOL_OPER_THM:
  !de uo b bop. (bir_unary_exp_GET_BOOL_OPER uo = SOME (de, bop)) ==>
                  (bir_unary_exp uo (bool2b b) = (bool2b (bop b)))
Proof
SIMP_TAC (std_ss++holBACore_ss) [bool2b_def] >>
Cases_on `uo` >> (
  Cases_on `b` >> (
    SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss++wordsLib.WORD_ss) [bool2w_def,
      bool2b_def, bir_unary_exp_GET_BOOL_OPER_def, bir_unary_exp_GET_OPER_def] >>

    (* for the CLZ and CLS cases *)
    REPEAT GEN_TAC >>
    COND_CASES_TAC >>
    REPEAT STRIP_TAC >>
    POP_ASSUM (ASSUME_TAC o GSYM) >>
    FULL_SIMP_TAC (std_ss++wordsLib.WORD_ss) [] >>

    EVAL_TAC >>
    FULL_SIMP_TAC (std_ss++intSimps.INT_ARITH_ss) []
  )
)
QED


Theorem bir_unary_exp_BOOL_OPER_EVAL = SIMP_RULE (std_ss++DatatypeSimps.expand_type_quants_ss[``:bir_unary_exp_t``]) [
     FORALL_AND_THM, bir_unary_exp_GET_BOOL_OPER_def] bir_unary_exp_GET_BOOL_OPER_THM



Theorem bir_eval_bool_exp_BExp_UnaryExp:
  !de uo bop env e.
       (bir_unary_exp_GET_BOOL_OPER uo = SOME (de, bop)) ==>
       bir_is_bool_exp_env env (BExp_UnaryExp uo e) ==> (
       (bir_eval_bool_exp (BExp_UnaryExp uo e) env) <=>
        bop (bir_eval_bool_exp e env))
Proof
SIMP_TAC std_ss [bir_eval_bool_exp_def, bir_eval_exp_def, bir_is_bool_exp_env_REWRS] >>
REPEAT STRIP_TAC >>
`?b. bir_eval_exp e env = SOME (bir_mk_bool_val b)` by METIS_TAC[bir_eval_bool_exp_INTRO] >>
FULL_SIMP_TAC std_ss [bir_mk_bool_val_inv] >>
ASM_SIMP_TAC std_ss [bir_eval_unary_exp_def, bir_mk_bool_val_def] >>
`bir_unary_exp uo (bool2b b) = bool2b (bop b)` by METIS_TAC[
   bir_unary_exp_GET_BOOL_OPER_THM] >>
ASM_SIMP_TAC std_ss [bir_mk_bool_val_inv, GSYM bir_mk_bool_val_def]
QED



Theorem bir_eval_bool_exp_BExp_UnaryExp_REWRS = SIMP_RULE (std_ss++DatatypeSimps.expand_type_quants_ss [``:bir_unary_exp_t``]) [
    bir_unary_exp_GET_BOOL_OPER_def, bir_is_bool_exp_env_REWRS,
    FORALL_AND_THM]
    bir_eval_bool_exp_BExp_UnaryExp



Theorem bir_eval_bool_exp_BExp_UnaryExp_REWRS_GSYM = GSYM (SIMP_RULE (std_ss++DatatypeSimps.expand_type_quants_ss [``:bir_unary_exp_t``]) [
    bir_unary_exp_GET_BOOL_OPER_def, bir_is_bool_exp_env_REWRS,
    FORALL_AND_THM]
    (SPEC T bir_eval_bool_exp_BExp_UnaryExp))





Theorem bir_eval_bool_exp_BExp_IfThenElse:
  !env e ec e1 e2.
       bir_is_bool_exp_env env (BExp_IfThenElse ec e1 e2) ==> (
       (bir_eval_bool_exp (BExp_IfThenElse ec e1 e2) env) <=>
        if (bir_eval_bool_exp ec env) then (bir_eval_bool_exp e1 env) else (bir_eval_bool_exp e2 env))
Proof
SIMP_TAC std_ss [bir_eval_bool_exp_def, bir_eval_exp_def, bir_is_bool_exp_env_REWRS] >>
REPEAT STRIP_TAC >>
ASM_SIMP_TAC std_ss [bir_eval_bool_exp_INTRO, bir_mk_bool_val_inv] >>
SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss) [bir_mk_bool_val_def, bir_eval_ifthenelse_REWRS,
  type_of_bool2b, bool2b_ELIMS, bool2w_ELIMS, type_of_bir_val_def] >>
ASM_SIMP_TAC std_ss [bir_mk_bool_val_inv, GSYM bir_mk_bool_val_def]
QED


(*********************************************)
(* additional useful lemmas                  *)
(*********************************************)

Theorem bir_eval_bool_exp_EQ:
  !exp env.
      bir_is_bool_exp_env env exp
      ==>
      ((bir_eval_bool_exp exp env) <=> (bir_eval_exp exp env = SOME bir_val_true))
Proof
REPEAT STRIP_TAC >>
  drule bir_is_bool_exp_env_IMPLIES_EVAL_IS_BOOL >>
  STRIP_TAC >> (
    FULL_SIMP_TAC std_ss [bir_val_is_Bool_ALT_DEF,
                          bir_val_true_def, bir_val_false_def,
                          bir_eval_bool_exp_def, bir_dest_bool_val_def] >>
    EVAL_TAC
  )
QED

val _ = export_theory();
