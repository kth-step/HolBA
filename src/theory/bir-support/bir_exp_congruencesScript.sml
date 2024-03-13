open HolKernel Parse boolLib bossLib;
open bir_envTheory bir_valuesTheory;
open bir_immTheory bir_typing_expTheory;
open bir_exp_memTheory bir_expTheory;
open bir_exp_immTheory;
open bir_exp_substitutionsTheory pred_setTheory;
open HolBACoreSimps

(* This theory defines a congruence relation for bir expressions.
   This allows expressions to be simplified. *)


val _ = new_theory "bir_exp_congruences";


(*****************************)
(* Basic congruence relation *)
(*****************************)

(* First just equivalence with evaluation is defined.
   This is a proper congruence. Later, we take
   used variables etc into account, but this will only
   lead to a pre-order, not an equivalence relation.
   This is however sufficient for
   simplification. *)

Definition bir_eval_exp_EQUIV_def:
  bir_eval_exp_EQUIV e1 e2 <=> (!env.
    (bir_eval_exp e1 env = bir_eval_exp e2 env))
End


Theorem bir_eval_exp_EQUIV_IS_EQUIV:
  (!e. bir_eval_exp_EQUIV e e) /\
    (!e1 e2. bir_eval_exp_EQUIV e1 e2 <=> bir_eval_exp_EQUIV e2 e1) /\
    (!e1 e2 e3. bir_eval_exp_EQUIV e1 e2 ==> bir_eval_exp_EQUIV e2 e3 ==>
                bir_eval_exp_EQUIV e1 e3)
Proof
METIS_TAC[bir_eval_exp_EQUIV_def]
QED


(* It is a congruence, it works with substitution *)

Theorem bir_eval_exp_EQUIV_IS_CONG_SUBST:
  !v ve ve' e. bir_eval_exp_EQUIV ve ve' ==>
               bir_eval_exp_EQUIV (bir_exp_subst1 v ve e) (bir_exp_subst1 v ve' e)
Proof
SIMP_TAC std_ss [bir_eval_exp_EQUIV_def] >>
METIS_TAC[bir_exp_subst1_EVAL_EQ_GEN]
QED


(****************************)
(* Real congruence relation *)
(****************************)

(* bir_eval_exp_EQUIV is what we have in mind when talking about equivalent
   expressions. It is really (as shown above) a congruence relation.
   However, it is not very useful in practice. We are not interested in all
   environments usually, but only the ones for which the expression is sensibly
   defined, i.e. only the ones, where all vars are provably initialised and
   we don't get an error message. *)

Definition bir_exp_CONG_def:
  bir_exp_CONG e1 e2 <=> (
    (type_of_bir_exp e1 = type_of_bir_exp e2) /\
    (bir_vars_of_exp e2 = bir_vars_of_exp e1) /\
    (!env ty.  bir_env_vars_are_initialised env (bir_vars_of_exp e1) ==>
               (type_of_bir_exp e1 = SOME ty) ==>
               (bir_eval_exp e1 env = bir_eval_exp e2 env)))
End

Theorem bir_exp_CONG_REFL:
  !e. bir_exp_CONG e e
Proof
SIMP_TAC std_ss [bir_exp_CONG_def]
QED


Theorem bir_exp_CONG_TRANS:
  !e1 e2 e3. bir_exp_CONG e1 e2 ==> bir_exp_CONG e2 e3 ==> bir_exp_CONG e1 e3
Proof
SIMP_TAC std_ss [bir_exp_CONG_def] >>
METIS_TAC[]
QED


Theorem bir_exp_CONG_SYM:
  !e1 e2. bir_exp_CONG e1 e2 <=> bir_exp_CONG e2 e1
Proof
SIMP_TAC (std_ss++boolSimps.EQUIV_EXTRACT_ss) [bir_exp_CONG_def] >>
METIS_TAC[]
QED


Theorem bir_exp_CONG_EQUIV_THM:
  !e1 e2. bir_exp_CONG e1 e2 <=> (bir_exp_CONG e1 = bir_exp_CONG e2)
Proof
SIMP_TAC std_ss [FUN_EQ_THM] >>
SIMP_TAC std_ss [bir_exp_CONG_def] >>
METIS_TAC[]
QED


Theorem bir_exp_CONG_IS_CONG_SUBST:
  !v ve ve' e. bir_exp_CONG ve ve' ==>
               bir_exp_CONG (bir_exp_subst1 v ve e) (bir_exp_subst1 v ve' e)
Proof
REPEAT GEN_TAC >>
Tactical.REVERSE (Cases_on `v IN bir_vars_of_exp e`) >- (
  ASM_SIMP_TAC std_ss [bir_exp_subst1_UNUSED_VAR, bir_exp_CONG_REFL]
) >>
STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_exp_CONG_def, bir_exp_subst1_TYPE_EQ_GEN,
  bir_exp_subst1_USED_VARS, bir_env_oldTheory.bir_env_vars_are_initialised_UNION] >>
REPEAT STRIP_TAC >>
METIS_TAC[bir_exp_subst1_NO_TYPE_SOME, bir_exp_subst1_EVAL_EQ_GEN]
QED


(* For practical purposed more insteresting is however a form that can be used
   as congruence rules. *)

Theorem bir_exp_CONG_BASIC_CONG_RULES:
  (!e e' ty ct.
      bir_exp_CONG e e' ==>
      bir_exp_CONG (BExp_Cast ct e ty) (BExp_Cast ct e' ty))

/\

(!e e' et.
      bir_exp_CONG e e' ==>
      bir_exp_CONG (BExp_UnaryExp et e) (BExp_UnaryExp et e'))

/\

(!e1 e1' e2 e2' et.
      bir_exp_CONG e1 e1' ==>
      bir_exp_CONG e2 e2' ==>
      bir_exp_CONG (BExp_BinExp et e1 e2) (BExp_BinExp et e1' e2'))

/\

(!e1 e1' e2 e2' et.
      bir_exp_CONG e1 e1' ==>
      bir_exp_CONG e2 e2' ==>
      bir_exp_CONG (BExp_BinPred et e1 e2) (BExp_BinPred et e1' e2'))

/\

(!c c' et et' ef ef'.
      bir_exp_CONG c c' ==>
      bir_exp_CONG et et' ==>
      bir_exp_CONG ef ef' ==>
      bir_exp_CONG (BExp_IfThenElse c et ef) (BExp_IfThenElse c' et' ef'))

/\


(!mem_e mem_e' a_e a_e' en ty.
      bir_exp_CONG mem_e mem_e' ==>
      bir_exp_CONG a_e a_e' ==>
      bir_exp_CONG (BExp_Load mem_e a_e en ty) (BExp_Load mem_e' a_e' en ty))

/\

(!mem_e mem_e' a_e a_e' v_e v_e' en.
      bir_exp_CONG mem_e mem_e' ==>
      bir_exp_CONG a_e a_e' ==>
      bir_exp_CONG v_e v_e' ==>
      bir_exp_CONG (BExp_Store mem_e a_e en v_e) (BExp_Store mem_e' a_e' en v_e'))
Proof
SIMP_TAC (std_ss++holBACore_ss) [bir_exp_CONG_def,
  bir_env_oldTheory.bir_env_vars_are_initialised_UNION, type_of_bir_exp_def] >>
REPEAT STRIP_TAC >> ASM_SIMP_TAC std_ss []
QED


(* Now real simplifications.
   TODO: Add Many more! *)

Theorem bir_exp_CONG_simp_IDEMPOTENT_AND:
  !e.
     (?ty. bir_type_is_Imm ty /\ (type_of_bir_exp e = SOME ty)) ==>
     bir_exp_CONG (BExp_BinExp BIExp_And e e) e
Proof
REPEAT STRIP_TAC >>
ASM_SIMP_TAC std_ss [bir_exp_CONG_def, bir_vars_of_exp_def,
  UNION_IDEMPOT, type_of_bir_exp_def, pairTheory.pair_case_thm,
  bir_eval_exp_def] >>
REPEAT STRIP_TAC >>
Cases_on `bir_eval_exp e env` >- (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_eval_bin_exp_def]
) >>
subgoal `ty = type_of_bir_val x` >- (
  IMP_RES_TAC type_of_bir_exp_THM_with_init_vars >>
  `x = va` by FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) []
) >>
Cases_on `x` >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_eval_bin_exp_def]
) >>
rename1 `bir_bin_exp _ v v = v` >>
Cases_on `v` >> (
  SIMP_TAC (std_ss++holBACore_ss) [wordsTheory.WORD_AND_IDEM]
)
QED



Theorem bir_exp_CONG_simp_IDEMPOTENT_OR:
  !e.
     (?ty. bir_type_is_Imm ty /\ (type_of_bir_exp e = SOME ty)) ==>
     bir_exp_CONG (BExp_BinExp BIExp_Or e e) e
Proof
REPEAT STRIP_TAC >>
ASM_SIMP_TAC std_ss [bir_exp_CONG_def, bir_vars_of_exp_def,
  UNION_IDEMPOT, type_of_bir_exp_def, pairTheory.pair_case_thm,
  bir_eval_exp_def] >>
REPEAT STRIP_TAC >>
Cases_on `bir_eval_exp e env` >- (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_eval_bin_exp_def]
) >>
subgoal `ty = type_of_bir_val x` >- (
  IMP_RES_TAC type_of_bir_exp_THM_with_init_vars >>
  `x = va` by FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) []
) >>
Cases_on `x` >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_eval_bin_exp_def]
) >>
rename1 `bir_bin_exp _ v v = v` >>
Cases_on `v` >> (
  SIMP_TAC (std_ss++holBACore_ss) [wordsTheory.WORD_OR_IDEM]
)
QED




(****************************)
(* Weak congruence relation *)
(****************************)

(* One issue with bir_exp_CONJ is that it demands that the set of used vars stays untouched.
   This prevents us from from dropping irrelevant subexpressions. However, if we change this,
   we loose the symmertry of the congruence relation. However, the resulting preorder is still
   good for simplifications. *)

Definition bir_exp_CONG_WEAK_def:
  bir_exp_CONG_WEAK e1 e2 <=> (
    (type_of_bir_exp e1 = type_of_bir_exp e2) /\
    (bir_vars_of_exp e2 SUBSET bir_vars_of_exp e1) /\
    (!env ty.  bir_env_vars_are_initialised env (bir_vars_of_exp e1) ==>
               (type_of_bir_exp e1 = SOME ty) ==>
               (bir_eval_exp e1 env = bir_eval_exp e2 env)))
End

Theorem bir_exp_CONG_WEAK_IS_WEAK:
  !e1 e2. bir_exp_CONG e1 e2 ==> bir_exp_CONG_WEAK e1 e2
Proof
SIMP_TAC std_ss [bir_exp_CONG_def, bir_exp_CONG_WEAK_def, SUBSET_REFL]
QED

Theorem bir_exp_CONG_WEAK_REFL:
  !e. bir_exp_CONG_WEAK e e
Proof
SIMP_TAC std_ss [bir_exp_CONG_WEAK_def, SUBSET_REFL]
QED


Theorem bir_exp_CONG_WEAK_TRANS:
  !e1 e2 e3. bir_exp_CONG_WEAK e1 e2 ==> bir_exp_CONG_WEAK e2 e3 ==> bir_exp_CONG_WEAK e1 e3
Proof
SIMP_TAC std_ss [bir_exp_CONG_WEAK_def, SUBSET_DEF,
  bir_env_oldTheory.bir_env_vars_are_initialised_def] >>
METIS_TAC[]
QED


Theorem bir_exp_CONG_WEAK_IS_CONG_SUBST:
  !v ve ve' e. bir_exp_CONG_WEAK ve ve' ==>
               bir_exp_CONG_WEAK (bir_exp_subst1 v ve e) (bir_exp_subst1 v ve' e)
Proof
REPEAT GEN_TAC >>
Tactical.REVERSE (Cases_on `v IN bir_vars_of_exp e`) >- (
  ASM_SIMP_TAC std_ss [bir_exp_subst1_UNUSED_VAR, bir_exp_CONG_WEAK_REFL]
) >>
SIMP_TAC std_ss [bir_exp_CONG_WEAK_def] >>
STRIP_TAC >>

`bir_vars_of_exp (bir_exp_subst1 v ve' e) SUBSET
 bir_vars_of_exp (bir_exp_subst1 v ve e)` by (
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [SUBSET_DEF, bir_exp_subst1_USED_VARS] >>
  METIS_TAC[]
) >>
ASM_SIMP_TAC std_ss [bir_exp_subst1_TYPE_EQ_GEN] >>
REPEAT STRIP_TAC >>
`bir_eval_exp ve env = bir_eval_exp ve' env` suffices_by
    METIS_TAC[bir_exp_subst1_EVAL_EQ_GEN] >>

`?ty'. type_of_bir_exp ve = SOME ty'` by METIS_TAC[bir_exp_subst1_NO_TYPE_SOME] >>
FULL_SIMP_TAC std_ss [] >>
`(bir_vars_of_exp ve) SUBSET bir_vars_of_exp (bir_exp_subst1 v ve e)` suffices_by (
   METIS_TAC[bir_env_oldTheory.bir_env_vars_are_initialised_SUBSET]) >>
ASM_SIMP_TAC std_ss [bir_exp_subst1_USED_VARS, SUBSET_UNION]
QED


(* For practical purposed more insteresting is however a form that can be used
   as congruence rules. *)
Theorem bir_exp_CONG_WEAK_BASIC_CONG_RULES:
  (!e e' ty ct.
      bir_exp_CONG_WEAK e e' ==>
      bir_exp_CONG_WEAK (BExp_Cast ct e ty) (BExp_Cast ct e' ty))

/\

(!e e' et.
      bir_exp_CONG_WEAK e e' ==>
      bir_exp_CONG_WEAK (BExp_UnaryExp et e) (BExp_UnaryExp et e'))

/\

(!e1 e1' e2 e2' et.
      bir_exp_CONG_WEAK e1 e1' ==>
      bir_exp_CONG_WEAK e2 e2' ==>
      bir_exp_CONG_WEAK (BExp_BinExp et e1 e2) (BExp_BinExp et e1' e2'))

/\

(!e1 e1' e2 e2' et.
      bir_exp_CONG_WEAK e1 e1' ==>
      bir_exp_CONG_WEAK e2 e2' ==>
      bir_exp_CONG_WEAK (BExp_BinPred et e1 e2) (BExp_BinPred et e1' e2'))

/\

(!c c' et et' ef ef'.
      bir_exp_CONG_WEAK c c' ==>
      bir_exp_CONG_WEAK et et' ==>
      bir_exp_CONG_WEAK ef ef' ==>
      bir_exp_CONG_WEAK (BExp_IfThenElse c et ef) (BExp_IfThenElse c' et' ef'))

/\


(!mem_e mem_e' a_e a_e' en ty.
      bir_exp_CONG_WEAK mem_e mem_e' ==>
      bir_exp_CONG_WEAK a_e a_e' ==>
      bir_exp_CONG_WEAK (BExp_Load mem_e a_e en ty) (BExp_Load mem_e' a_e' en ty))

/\

(!mem_e mem_e' a_e a_e' v_e v_e' en.
      bir_exp_CONG_WEAK mem_e mem_e' ==>
      bir_exp_CONG_WEAK a_e a_e' ==>
      bir_exp_CONG_WEAK v_e v_e' ==>
      bir_exp_CONG_WEAK (BExp_Store mem_e a_e en v_e) (BExp_Store mem_e' a_e' en v_e'))
Proof
SIMP_TAC std_ss [bir_exp_CONG_WEAK_def, bir_vars_of_exp_def,
  type_of_bir_exp_EQ_SOME_REWRS, bir_eval_exp_def,
  bir_env_oldTheory.bir_env_vars_are_initialised_UNION, SUBSET_DEF, IN_UNION,
  DISJ_IMP_THM, type_of_bir_exp_def] >>
METIS_TAC[]
QED





Theorem bir_exp_CONG_WEAK_simp_IDEMPOTENT_AND:
  !e. (?ty. bir_type_is_Imm ty /\ (type_of_bir_exp e = SOME ty)) ==>
      bir_exp_CONG_WEAK (BExp_BinExp BIExp_And e e) e
Proof
METIS_TAC[bir_exp_CONG_simp_IDEMPOTENT_AND, bir_exp_CONG_WEAK_IS_WEAK]
QED


Theorem bir_exp_CONG_WEAK_simp_IDEMPOTENT_OR:
  !e. (?ty. bir_type_is_Imm ty /\ (type_of_bir_exp e = SOME ty)) ==>
      bir_exp_CONG_WEAK (BExp_BinExp BIExp_Or e e) e
Proof
METIS_TAC[bir_exp_CONG_simp_IDEMPOTENT_OR, bir_exp_CONG_WEAK_IS_WEAK]
QED


Theorem bir_exp_CONG_WEAK_simp_IF_THEN_ELSE_TF_EQ:
  !c e. (type_of_bir_exp c = SOME BType_Bool) ==>
        bir_exp_CONG_WEAK (BExp_IfThenElse c e e) e
Proof
SIMP_TAC std_ss [bir_exp_CONG_WEAK_def, bir_vars_of_exp_def,
  type_of_bir_exp_def, SUBSET_DEF, IN_UNION,
  bir_env_oldTheory.bir_env_vars_are_initialised_UNION, bir_eval_exp_def,
  pairTheory.pair_case_thm] >>
REPEAT STRIP_TAC >- (
  Cases_on `type_of_bir_exp e` >> ASM_SIMP_TAC std_ss [BType_Bool_def]
) >>
Cases_on `bir_eval_exp c env` >- (
  IMP_RES_TAC type_of_bir_exp_THM_with_init_vars >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) []
) >>
subgoal `BType_Bool = type_of_bir_val x` >- (
  IMP_RES_TAC type_of_bir_exp_THM_with_init_vars >>
  `x = va` by FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) []
) >>
Cases_on `bir_eval_exp e env` >- (
  FULL_SIMP_TAC (std_ss++holBACore_ss) []
) >>
Cases_on `x` >> (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_eval_ifthenelse_def, BType_Bool_def]
)
QED


(* TODO: ADD MANY MORE! *)


val _ = export_theory();
