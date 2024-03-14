open HolKernel Parse boolLib bossLib;
open wordsTheory bitstringTheory;
open bir_auxiliaryTheory bir_immTheory bir_valuesTheory;
open bir_exp_immTheory bir_exp_memTheory bir_envTheory;
open finite_mapTheory;

val _ = new_theory "bir_exp";

val bir_imm_ss = rewrites ((type_rws ``:bir_imm_t``) @ (type_rws ``:bir_immtype_t``));
val bir_type_ss = rewrites ((type_rws ``:bir_type_t``));


(* ------------------------------------------------------------------------- *)
(*  Datatypes                                                                *)
(* ------------------------------------------------------------------------- *)

Datatype:
  bir_exp_t =
    BExp_Const             bir_imm_t
  | BExp_MemConst          bir_immtype_t (*Address type*) bir_immtype_t (* Value type *) (num |-> num)
  | BExp_Den               bir_var_t

  | BExp_Cast              bir_cast_t bir_exp_t bir_immtype_t

  | BExp_UnaryExp          bir_unary_exp_t bir_exp_t
  | BExp_BinExp            bir_bin_exp_t bir_exp_t bir_exp_t
  | BExp_BinPred           bir_bin_pred_t bir_exp_t bir_exp_t
  | BExp_MemEq             bir_exp_t bir_exp_t

  | BExp_IfThenElse        bir_exp_t bir_exp_t bir_exp_t

  | BExp_Load              bir_exp_t bir_exp_t bir_endian_t bir_immtype_t
  | BExp_Store             bir_exp_t bir_exp_t bir_endian_t bir_exp_t
End


(* ------------------------------------------------------------------------- *)
(*  Semantics of expressions                                                 *)
(* ------------------------------------------------------------------------- *)

Definition bir_eval_cast_def:
  (bir_eval_cast ct (SOME (BVal_Imm bi)) ty = SOME (BVal_Imm (bir_gencast ct bi ty))) /\
  (bir_eval_cast _ _ _ = NONE)
End

Definition bir_eval_unary_exp_def:
  (bir_eval_unary_exp et (SOME (BVal_Imm bi)) = SOME (BVal_Imm (bir_unary_exp et bi))) /\
  (bir_eval_unary_exp _ _ = NONE)
End

Definition bir_eval_bin_exp_def:
  (bir_eval_bin_exp et (SOME (BVal_Imm bi1)) (SOME (BVal_Imm bi2)) =
     if (type_of_bir_imm bi1 <> type_of_bir_imm bi2) then NONE else
     SOME (BVal_Imm (bir_bin_exp et bi1 bi2))) /\
  (bir_eval_bin_exp _ _ _ = NONE)
End

Definition bir_eval_bin_pred_def:
  (bir_eval_bin_pred pt (SOME (BVal_Imm bi1)) (SOME (BVal_Imm bi2)) =
     if (type_of_bir_imm bi1 <> type_of_bir_imm bi2) then NONE else
     SOME (BVal_Imm (bool2b (bir_bin_pred pt bi1 bi2)))) /\
  (bir_eval_bin_pred _ _ _ = NONE)
End

Definition bir_eval_memeq_def:
  (bir_eval_memeq (SOME (BVal_Mem at1 vt1 mmap1)) (SOME (BVal_Mem at2 vt2 mmap2)) =
     if ((at1 <> at2) \/ (vt1 <> vt2)) then NONE else
     SOME (BVal_Imm (bool2b (bir_memeq at1 vt1 mmap1 mmap2)))) /\
  (bir_eval_memeq _ _ = NONE)
End

Definition bir_eval_ifthenelse_def:
  (bir_eval_ifthenelse (SOME (BVal_Imm (Imm1 cw))) (SOME v1) (SOME v2) =
     if (type_of_bir_val v1 <> type_of_bir_val v2) then NONE else
       if (cw = 1w) then SOME v1 else SOME v2) /\
  (bir_eval_ifthenelse _ _ _ = NONE)
End

Definition bir_eval_load_def:
  (bir_eval_load (SOME (BVal_Mem ta tv mmap)) (SOME (BVal_Imm a)) en t =
     if ((type_of_bir_imm a) = ta) then
        (case (bir_load_from_mem tv t ta mmap en (b2n a)) of
           NONE => NONE
         | SOME i => SOME (BVal_Imm i))
     else NONE) /\
  (bir_eval_load _ _ _ _ = NONE)
End

Definition bir_eval_store_def:
  (bir_eval_store (SOME (BVal_Mem ta tv mmap)) (SOME (BVal_Imm a)) en (SOME (BVal_Imm v)) =
     if ((type_of_bir_imm a) = ta) then
        (case (bir_store_in_mem tv ta v mmap en (b2n a)) of
           NONE => NONE
         | SOME mmap' => SOME (BVal_Mem ta tv mmap'))
     else NONE) /\
  (bir_eval_store _ _ _ _ = NONE)
End



Definition bir_eval_exp_def:
  (bir_eval_exp (BExp_Const n) env = SOME (BVal_Imm n)) /\

  (bir_eval_exp (BExp_MemConst aty vty mmap) env = SOME (BVal_Mem aty vty mmap)) /\

  (bir_eval_exp (BExp_Den v) env = bir_env_read v env) /\

  (bir_eval_exp (BExp_Cast ct e ty) env = (
     bir_eval_cast ct (bir_eval_exp e env) ty)) /\

  (bir_eval_exp (BExp_UnaryExp et e) env = (
     bir_eval_unary_exp et (bir_eval_exp e env))) /\

  (bir_eval_exp (BExp_BinExp et e1 e2) env = (
     bir_eval_bin_exp et (bir_eval_exp e1 env) (bir_eval_exp e2 env))) /\

  (bir_eval_exp (BExp_BinPred pt e1 e2) env = (
     bir_eval_bin_pred pt (bir_eval_exp e1 env) (bir_eval_exp e2 env))) /\

  (bir_eval_exp (BExp_MemEq e1 e2) env = (
     bir_eval_memeq (bir_eval_exp e1 env) (bir_eval_exp e2 env))) /\


  (bir_eval_exp (BExp_IfThenElse c et ef) env =
     bir_eval_ifthenelse (bir_eval_exp c env) (bir_eval_exp et env) (bir_eval_exp ef env)
  ) /\

  (bir_eval_exp (BExp_Load mem_e a_e en ty) env =
     bir_eval_load (bir_eval_exp mem_e env) (bir_eval_exp a_e env) en ty) /\

  (bir_eval_exp (BExp_Store mem_e a_e en v_e) env =
     bir_eval_store (bir_eval_exp mem_e env) (bir_eval_exp a_e env) en (bir_eval_exp v_e env))
End




(* ------------------------------------------------------------------------- *)
(*  Rewrite theorems for eval                                                *)
(* ------------------------------------------------------------------------- *)

Theorem bir_eval_cast_REWRS:
  (!ct bi ty. (bir_eval_cast ct (SOME (BVal_Imm bi)) ty = SOME (BVal_Imm (bir_gencast ct bi ty)))) /\
  (!ct ty. bir_eval_cast ct NONE ty = NONE) /\
  (!ct at vt mmap ty. bir_eval_cast ct (SOME (BVal_Mem at vt mmap)) ty = NONE)
Proof
SIMP_TAC std_ss [bir_eval_cast_def]
QED

Theorem bir_eval_unary_exp_REWRS:
  (!et bi. (bir_eval_unary_exp et (SOME (BVal_Imm bi)) = SOME (BVal_Imm (bir_unary_exp et bi)))) /\
   (!et. bir_eval_unary_exp et NONE = NONE) /\
   (!et at vt mmap. bir_eval_unary_exp et (SOME (BVal_Mem at vt mmap)) = NONE)
Proof
SIMP_TAC std_ss [bir_eval_unary_exp_def]
QED


Theorem bir_eval_bin_exp_REWRS:
  (!et bi1 bi2. bir_eval_bin_exp et (SOME (BVal_Imm bi1)) (SOME (BVal_Imm bi2)) =
     if (type_of_bir_imm bi1 <> type_of_bir_imm bi2) then NONE else
     SOME (BVal_Imm (bir_bin_exp et bi1 bi2))) /\
  (!et v. bir_eval_bin_exp et NONE v = NONE) /\
  (!et v. bir_eval_bin_exp et v NONE = NONE) /\
  (!et at vt mmap v. bir_eval_bin_exp et (SOME (BVal_Mem at vt mmap)) v = NONE) /\
  (!et at vt mmap v. bir_eval_bin_exp et v (SOME (BVal_Mem at vt mmap)) = NONE)
Proof
SIMP_TAC std_ss [bir_eval_bin_exp_def] >>
CONJ_TAC >> (
  Cases_on `v` >> (TRY (Q.SPEC_TAC (`x`, `k`) >> Cases_on `k`)) >>
    (SIMP_TAC std_ss [bir_eval_bin_exp_def])
)
QED

Theorem bir_eval_bin_pred_REWRS:
  (!et bi1 bi2. bir_eval_bin_pred et (SOME (BVal_Imm bi1)) (SOME (BVal_Imm bi2)) =
     if (type_of_bir_imm bi1 <> type_of_bir_imm bi2) then NONE else
     SOME (BVal_Imm (bool2b (bir_bin_pred et bi1 bi2)))) /\
  (!et v. bir_eval_bin_pred et NONE v = NONE) /\
  (!et v. bir_eval_bin_pred et v NONE = NONE) /\
  (!et at vt mmap v. bir_eval_bin_pred et (SOME (BVal_Mem at vt mmap)) v = NONE) /\
  (!et at vt mmap v. bir_eval_bin_pred et v (SOME (BVal_Mem at vt mmap)) = NONE)
Proof
SIMP_TAC std_ss [bir_eval_bin_pred_def] >>
CONJ_TAC >> (
  Cases_on `v` >> (TRY (Q.SPEC_TAC (`x`, `k`) >> Cases_on `k`)) >>
    (SIMP_TAC std_ss [bir_eval_bin_pred_def])
)
QED

Theorem bir_eval_memeq_REWRS:
  (!at1 vt1 mmap1 at2 vt2 mmap2. (bir_eval_memeq (SOME (BVal_Mem at1 vt1 mmap1)) (SOME (BVal_Mem at2 vt2 mmap2)) =
     if ((at1 <> at2) \/ (vt1 <> vt2)) then NONE else
     SOME (BVal_Imm (bool2b (bir_memeq at1 vt1 mmap1 mmap2))))) /\
   (!v. bir_eval_memeq NONE v = NONE) /\
   (!v. bir_eval_memeq v NONE = NONE) /\
   (!bi v. bir_eval_memeq (SOME (BVal_Imm bi)) v = NONE) /\
   (!bi v. bir_eval_memeq v (SOME (BVal_Imm bi)) = NONE)
Proof
SIMP_TAC std_ss [bir_eval_memeq_def] >>
CONJ_TAC >> (
  Cases_on `v` >> (TRY (Q.SPEC_TAC (`x`, `k`) >> Cases_on `k`)) >>
    (SIMP_TAC std_ss [bir_eval_memeq_def])
)
QED

Theorem bir_eval_ifthenelse_REWRS:
  (!c v1 v2. bir_eval_ifthenelse (SOME (BVal_Imm c)) (SOME v1) (SOME v2) =
     if (type_of_bir_imm c = Bit1) then (
       if (type_of_bir_val v1 <> type_of_bir_val v2) then NONE else
         if (c = Imm1 1w) then (SOME v1) else (SOME v2)
     ) else NONE) /\
  (!c v2. bir_eval_ifthenelse c NONE v2 = NONE) /\
  (!c v1. bir_eval_ifthenelse c v1 NONE = NONE) /\
  (!c e1 e2. bir_eval_ifthenelse NONE e1 e2 = NONE) /\
  (!at vt mmap e1 e2. bir_eval_ifthenelse (SOME (BVal_Mem at vt mmap)) e1 e2 = NONE)
Proof
SIMP_TAC std_ss [bir_eval_ifthenelse_def] >>
REPEAT (CONJ_TAC) >> (
  Cases_on `c` >>
  (TRY (Cases_on `x` >>  Cases_on `b` >> TRY (Cases_on `v1`))) >>
  SIMP_TAC (std_ss++bir_imm_ss) [type_of_bir_imm_def, bir_eval_ifthenelse_def]
)
QED

Theorem bir_eval_ifthenelse_REWRS_NONE:
  (!vc v1 v2.
     (type_of_bir_val vc <> BType_Imm Bit1) ==>
     (bir_eval_ifthenelse (SOME vc) v1 v2 = NONE)) /\
  (!vc v1 v2.
     ~(bir_val_is_Bool vc) ==>
     (bir_eval_ifthenelse (SOME vc) v1 v2 = NONE)) /\
  (!vc v1 v2.
     (type_of_bir_val v1 <> type_of_bir_val v2) ==>
     (bir_eval_ifthenelse vc (SOME v1) (SOME v2) = NONE))
Proof
REPEAT STRIP_TAC >> Cases_on `vc` >> Cases_on `v1` >>  Cases_on `v2` >> (
  TRY (Cases_on `x`) >>
  FULL_SIMP_TAC (std_ss++bir_type_ss++bir_imm_ss++optionSimps.OPTION_ss) [type_of_bir_imm_def, type_of_bir_val_def,
    bir_eval_ifthenelse_REWRS, bir_val_checker_REWRS]
)
QED

Theorem bir_eval_ifthenelse_TF_EQ:
  !c v.
     bir_eval_ifthenelse (SOME c) v v =
     if (bir_val_is_Bool c) then v else NONE
Proof
Cases_on `c` >> Cases_on `b` >> Cases_on `v` >> (
  SIMP_TAC (std_ss++bir_imm_ss++bir_type_ss) [type_of_bir_imm_def, bir_eval_ifthenelse_REWRS,
    bir_val_checker_REWRS]
)
QED


Theorem bir_eval_load_NONE_REWRS1[local]:
  (!mem en t. bir_eval_load mem NONE en t = NONE) /\
    (!mem en t aty vty mmap. bir_eval_load mem (SOME (BVal_Mem aty vty mmap)) en t = NONE)
Proof
SIMP_TAC std_ss [bir_eval_load_def] >>
REPEAT CONJ_TAC >>
Cases_on `mem` >> (TRY (Cases_on `x`)) >> SIMP_TAC std_ss [bir_eval_load_def]
QED

Theorem bir_eval_load_NONE_REWRS2[local]:
  (!a en t. bir_eval_load NONE a en t = NONE) /\
    (!a en t i. bir_eval_load (SOME (BVal_Imm i)) a en t = NONE)
Proof
SIMP_TAC std_ss [bir_eval_load_def]
QED

Theorem bir_eval_load_NONE_REWRS3[local]:
  !a en t i aty vty mmap.
      (type_of_bir_imm i <> aty) ==>
      (bir_eval_load (SOME (BVal_Mem aty vty mmap)) (SOME (BVal_Imm i)) en t = NONE)
Proof
SIMP_TAC std_ss [bir_eval_load_def]
QED


Theorem bir_eval_load_NONE_REWRS4[local]:
  !a en t i aty vty mmap.
      (t <> vty) ==>
      (bir_eval_load (SOME (BVal_Mem aty vty mmap)) (SOME (BVal_Imm i)) BEnd_NoEndian t = NONE)
Proof
SIMP_TAC std_ss [bir_eval_load_def] >>
REPEAT STRIP_TAC >>
Cases_on `t` >> Cases_on `vty` >> SIMP_TAC std_ss [] >>
ASM_SIMP_TAC std_ss [bir_load_from_mem_NO_ENDIAN]
QED

Theorem bir_eval_load_NONE_REWRS5[local]:
  !a en t i aty vty mmap en.
      (bir_number_of_mem_splits vty t aty = NONE) ==>
      (bir_eval_load (SOME (BVal_Mem aty vty mmap)) (SOME (BVal_Imm i)) en t = NONE)
Proof
SIMP_TAC std_ss [bir_eval_load_def] >>
REPEAT STRIP_TAC >>
Cases_on `t` >> Cases_on `vty` >> SIMP_TAC std_ss [] >>
ASM_SIMP_TAC std_ss [bir_load_from_mem_def]
QED


val bir_eval_load_NONE_REWRS = save_thm ("bir_eval_load_NONE_REWRS",
  REWRITE_RULE [GSYM CONJ_ASSOC] (
  LIST_CONJ [bir_eval_load_NONE_REWRS1, bir_eval_load_NONE_REWRS2,
             bir_eval_load_NONE_REWRS3, bir_eval_load_NONE_REWRS4,
             bir_eval_load_NONE_REWRS5]));


Theorem bir_eval_load_SINGLE_REWR:
  !a en t i aty vty mmap en.
      (bir_eval_load (SOME (BVal_Mem aty vty mmap)) (SOME (BVal_Imm i)) en vty) =
      ((if (type_of_bir_imm i = aty) then (SOME (BVal_Imm (n2bs (bir_load_mmap mmap (b2n i)) vty)))
       else NONE))
Proof
SIMP_TAC arith_ss [bir_eval_load_def, bir_load_from_mem_SINGLE] >>
REPEAT STRIP_TAC >>
COND_CASES_TAC >> ASM_REWRITE_TAC[] >>
`bir_mem_addr aty (b2n i) = b2n i` suffices_by ASM_SIMP_TAC std_ss [] >>
MATCH_MP_TAC bir_mem_addr_id >>
METIS_TAC[b2n_lt]
QED


Theorem bir_eval_load_BASIC_REWR:
  !a en t i aty vty ty mmap en.
      (bir_eval_load (SOME (BVal_Mem aty vty mmap)) (SOME (BVal_Imm i)) en ty) =
      (if type_of_bir_imm i = aty then
        case bir_load_from_mem vty ty aty mmap en (b2n i) of
          NONE => NONE
        | SOME i => SOME (BVal_Imm i)
       else NONE)
Proof
SIMP_TAC arith_ss [bir_eval_load_def]
QED


val bir_eval_load_FULL_REWRS = save_thm ("bir_eval_load_FULL_REWRS",
let
Theorem thm_prune0[local]:
  (!ta a.
      (type_of_bir_imm a <> ta) ==>
      (bir_eval_load (SOME (BVal_Mem ta tv mmap)) (SOME (BVal_Imm a)) en tr = NONE)) /\
      (!tr tv.
      (tr <> tv) ==> (bir_number_of_mem_splits tv tr ta <> NONE) ==>
      (bir_eval_load (SOME (BVal_Mem ta tv mmap)) (SOME (BVal_Imm i)) BEnd_NoEndian tr = NONE)) /\
      (!tr tv.
      (bir_number_of_mem_splits tv tr ta = NONE) ==>
      (bir_eval_load (SOME (BVal_Mem ta tv mmap)) (SOME (BVal_Imm i)) en tr = NONE))
Proof
SIMP_TAC std_ss [bir_eval_load_NONE_REWRS]
QED

  val thm_prune1 = SIMP_RULE (std_ss ++ bir_imm_ss ++ DatatypeSimps.expand_type_quants_ss [``:bir_immtype_t``, ``:bir_imm_t``]) [bir_number_of_mem_splits_REWRS, type_of_bir_imm_def] thm_prune0


  val (l1, l2) = partition (is_imp_only o concl) (CONJUNCTS thm_prune1)

  val l1' = map (SIMP_RULE (list_ss++bir_imm_ss++DatatypeSimps.expand_type_quants_ss [``:bir_immtype_t``]) [bir_number_of_mem_splits_REWRS] o (Q.GEN `ta`)) l1

  val thm_prune2 = SIMP_RULE std_ss [FORALL_AND_THM, GSYM CONJ_ASSOC] (GEN_ALL
    (LIST_CONJ (l1' @ l2)))

  val thm0 = bir_eval_load_BASIC_REWR

  val thm1 = SIMP_RULE (list_ss ++ bir_imm_ss ++ DatatypeSimps.expand_type_quants_ss [``:bir_immtype_t``, ``:bir_imm_t``, ``:bir_endian_t``]) [ type_of_bir_imm_def, size_of_bir_immtype_def, bir_number_of_mem_splits_REWRS, bir_load_from_mem_REWRS, thm_prune2]
     thm0

  val thm2 = Ho_Rewrite.REWRITE_RULE [fold_bir_endian_THM] thm1

  val thm3 = SIMP_RULE (list_ss) [
     FORALL_AND_THM, b2n_MOD_2EXP, type_of_bir_imm_def, size_of_bir_immtype_def]
     thm2

  val thm4 = REWRITE_RULE [b2n_def, bir_mem_addr_w2n_SIZES, bir_mem_addr_w2n_add_SIZES, GSYM CONJ_ASSOC] (CONJ thm3 thm_prune2)
in thm4
end);



Theorem bir_eval_store_NONE_REWRS1[local]:
  (!mem en v. bir_eval_store mem NONE en v = NONE) /\
    (!mem en v aty vty mmap. bir_eval_store mem (SOME (BVal_Mem aty vty mmap)) en v = NONE)
Proof
SIMP_TAC std_ss [bir_eval_store_def] >>
REPEAT CONJ_TAC >>
Cases_on `mem` >> (TRY (Cases_on `x`)) >> SIMP_TAC std_ss [bir_eval_store_def]
QED

Theorem bir_eval_store_NONE_REWRS2[local]:
  (!a en v. bir_eval_store NONE a en v = NONE) /\
    (!a en v i. bir_eval_store (SOME (BVal_Imm i)) a en v = NONE)
Proof
SIMP_TAC std_ss [bir_eval_store_def]
QED


Theorem bir_eval_store_NONE_REWRS3[local]:
  (!a en mem. bir_eval_store mem a en NONE = NONE) /\
    (!a en mem ta tv mmap. bir_eval_store mem a en (SOME (BVal_Mem ta tv mmap)) = NONE)
Proof
REPEAT CONJ_TAC >>
Cases_on `mem` >> Cases_on `a` >> (TRY (Cases_on `x`)) >>
  ((TRY (Cases_on `x'`)) >> SIMP_TAC std_ss [bir_eval_store_def])
QED


Theorem bir_eval_store_NONE_REWRS4[local]:
  !en v i aty vty mmap.
      (type_of_bir_imm i <> aty) ==>
      (bir_eval_store (SOME (BVal_Mem aty vty mmap)) (SOME (BVal_Imm i)) en v = NONE)
Proof
Cases_on `v` >> (TRY (Cases_on `x`)) >> (
  SIMP_TAC std_ss [bir_eval_store_def])
QED


Theorem bir_eval_store_NONE_REWRS5[local]:
  !a en v aty vty mmap.
      (type_of_bir_imm v <> vty) ==>
      (bir_eval_store (SOME (BVal_Mem aty vty mmap)) a BEnd_NoEndian (SOME (BVal_Imm v)) = NONE)
Proof
Cases_on `a` >> SIMP_TAC std_ss [bir_eval_store_def] >>
REPEAT STRIP_TAC >>
Cases_on `v` >> Cases_on `vty` >> Cases_on `x` >> SIMP_TAC std_ss [bir_eval_store_def] >>
ASM_SIMP_TAC std_ss [bir_store_in_mem_NO_ENDIAN]
QED


Theorem bir_eval_store_NONE_REWRS6[local]:
  !a en v aty vty mmap en.
      (bir_number_of_mem_splits vty (type_of_bir_imm v) aty = NONE) ==>
      (bir_eval_store (SOME (BVal_Mem aty vty mmap)) a en (SOME (BVal_Imm v)) = NONE)
Proof
Cases_on `a` >> SIMP_TAC std_ss [LET_DEF] >>
REPEAT STRIP_TAC >>
Cases_on `v` >> Cases_on `vty` >> TRY (Cases_on `x`) >> SIMP_TAC std_ss [bir_eval_store_def] >>
ASM_SIMP_TAC std_ss [bir_store_in_mem_def, LET_DEF]
QED


val bir_eval_store_NONE_REWRS = save_thm ("bir_eval_store_NONE_REWRS",
  SIMP_RULE std_ss [GSYM CONJ_ASSOC] (
  LIST_CONJ [bir_eval_store_NONE_REWRS1, bir_eval_store_NONE_REWRS2,
             bir_eval_store_NONE_REWRS3, bir_eval_store_NONE_REWRS4,
             bir_eval_store_NONE_REWRS5, bir_eval_store_NONE_REWRS6]));

Theorem bir_eval_store_SINGLE_REWR:
  !a en t i aty v vty mmap en.
      ((type_of_bir_imm i = aty) /\ (type_of_bir_imm v = vty)) ==>
      (bir_eval_store (SOME (BVal_Mem aty vty mmap)) (SOME (BVal_Imm i)) en (SOME (BVal_Imm v)) =
      SOME (BVal_Mem aty vty (FUPDATE mmap (b2n i, b2n v))))
Proof
SIMP_TAC arith_ss [bir_eval_store_def, bir_store_in_mem_SINGLE] >>
REPEAT STRIP_TAC >>
`bir_mem_addr (type_of_bir_imm i) (b2n i) = b2n i` suffices_by ASM_SIMP_TAC std_ss [] >>
MATCH_MP_TAC bir_mem_addr_id >>
METIS_TAC[b2n_lt]
QED


Theorem bir_eval_store_BASIC_REWR:
  !a en t i aty v vty mmap en.
      (bir_eval_store (SOME (BVal_Mem aty vty mmap)) (SOME (BVal_Imm i)) en (SOME (BVal_Imm v)) =
      (if type_of_bir_imm i = aty then
         case bir_store_in_mem vty aty v mmap en (b2n i) of
           NONE => NONE
         | SOME mmap' => SOME (BVal_Mem aty vty mmap')
       else NONE))
Proof
SIMP_TAC arith_ss [bir_eval_store_def]
QED


val bir_eval_store_FULL_REWRS = save_thm ("bir_eval_store_FULL_REWRS",
let
Theorem thm_prune0[local]:
  (!ta a.
      (type_of_bir_imm a <> ta) ==>
      (bir_eval_store (SOME (BVal_Mem ta tv mmap)) (SOME (BVal_Imm a)) en v = NONE)) /\
      (!i tv.
      (type_of_bir_imm i <> tv) ==> (bir_number_of_mem_splits tv (type_of_bir_imm i) ta <> NONE) ==>
      (bir_eval_store (SOME (BVal_Mem ta tv mmap)) a BEnd_NoEndian (SOME (BVal_Imm i)) = NONE)) /\
      (!i tv.
      (bir_number_of_mem_splits tv (type_of_bir_imm i) ta = NONE) ==>
      (bir_eval_store (SOME (BVal_Mem ta tv mmap)) a en (SOME (BVal_Imm i)) = NONE))
Proof
SIMP_TAC std_ss [bir_eval_store_NONE_REWRS]
QED

  val thm_prune1 = SIMP_RULE (std_ss ++ bir_imm_ss ++ DatatypeSimps.expand_type_quants_ss [``:bir_immtype_t``, ``:bir_imm_t``]) [bir_number_of_mem_splits_REWRS, type_of_bir_imm_def, FORALL_AND_THM] thm_prune0

  val (l1, l2) = partition (is_imp_only o snd o strip_forall o concl) (CONJUNCTS thm_prune1)

  val l1' = map (SIMP_RULE (list_ss++bir_imm_ss++DatatypeSimps.expand_type_quants_ss [``:bir_immtype_t``]) [bir_number_of_mem_splits_REWRS] o (Q.GEN `ta`)) l1

  val thm_prune2 = SIMP_RULE std_ss [FORALL_AND_THM, GSYM CONJ_ASSOC] (GEN_ALL
    (LIST_CONJ (l1' @ l2)))


  val thm0 = SIMP_RULE (std_ss) [bir_eval_store_NONE_REWRS, FORALL_AND_THM] bir_eval_store_BASIC_REWR

  val thm1 = SIMP_RULE (list_ss++ bir_imm_ss ++ DatatypeSimps.expand_type_quants_ss [``:bir_immtype_t``, ``:bir_imm_t``, ``:bir_endian_t``]) [ type_of_bir_imm_def, size_of_bir_immtype_def, bir_number_of_mem_splits_REWRS, bir_store_in_mem_REWRS, thm_prune2]
     thm0

  val thm2 = Ho_Rewrite.REWRITE_RULE [fold_bir_endian_THM] thm1

  val thm3 = SIMP_RULE (list_ss) [
     FORALL_AND_THM, type_of_bir_imm_def, size_of_bir_immtype_def]
     thm2

  val thm4 = REWRITE_RULE [b2n_def, GSYM CONJ_ASSOC] (CONJ thm3 thm_prune2)
in thm4
end);


val _ = export_theory();
