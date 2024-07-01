open HolKernel Parse boolLib bossLib;

open pred_setTheory;
open combinTheory;

val _ = new_theory "symb_interpret";

(*
NOTATION: ALL ABOUT INTERPRETATIONS
=======================================================
*)

Datatype:
  symb_interpret_t =
   SymbInterpret ('a_symbol -> 'b_val option)
End
Definition symb_interpr_get_def:
  symb_interpr_get (SymbInterpret h) symb = h symb
End

Theorem symb_interpr_get_CASES_thm:
  !H symb.
  (?v. symb_interpr_get H symb = SOME v) \/
  (symb_interpr_get H symb = NONE)
Proof
Cases_on `H` >>
  FULL_SIMP_TAC std_ss [symb_interpr_get_def] >>
  REPEAT STRIP_TAC >>
  Cases_on `f symb` >> (
    METIS_TAC []
  )
QED

Definition symb_interpr_update_def:
  symb_interpr_update (SymbInterpret h) (symb, vo) = SymbInterpret ((symb =+ vo) h)
End
Theorem symb_interpr_get_update_id_thm:
  !H symb vo. symb_interpr_get (symb_interpr_update H (symb, vo)) symb = vo
Proof
Cases_on `H` >>
  METIS_TAC [symb_interpr_get_def, symb_interpr_update_def, APPLY_UPDATE_THM]
QED
Theorem symb_interpr_get_update_thm:
  !H symb symb' vo. symb_interpr_get (symb_interpr_update H (symb', vo)) symb =
if symb = symb' then vo else symb_interpr_get H symb
Proof
REPEAT STRIP_TAC >>
  Cases_on `H` >>
  Cases_on `symb = symb'` >> (
    METIS_TAC [symb_interpr_get_def, symb_interpr_update_def, APPLY_UPDATE_THM]
  )
QED

Definition symb_interpr_dom_def:
  symb_interpr_dom (SymbInterpret h) = {symb | h symb <> NONE}
End

Theorem symb_interpr_dom_IMP_get_CASES_thm:
  !H symb.
  (symb IN symb_interpr_dom H ==> ?v. symb_interpr_get H symb = SOME v) /\
  ((~(symb IN symb_interpr_dom H)) ==> symb_interpr_get H symb = NONE)
Proof
  Cases >>
  gs[symb_interpr_get_def, symb_interpr_dom_def] >>
  metis_tac[TypeBase.nchotomy_of “:'a option”]
QED

Theorem symb_interpr_dom_thm:
  !H symb.
  (symb IN symb_interpr_dom H) = (symb_interpr_get H symb <> NONE)
Proof
Cases_on `H` >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss)
    [symb_interpr_dom_def, symb_interpr_get_def]
QED

Definition symb_interprs_eq_for_def:
  symb_interprs_eq_for H1 H2 symbs =
      (!symb. (symb IN symbs) ==> (symb_interpr_get H1 symb = symb_interpr_get H2 symb))
End

val symb_interpret_ss = rewrites (type_rws (mk_type ("symb_interpret_t", [Type.alpha, Type.beta])));
Theorem symb_interprs_eq_for_EQ_thm:
  !H1 H2.
  (symb_interprs_eq_for H1 H2 (UNIV)) <=>
  (H1 = H2)
Proof
REPEAT STRIP_TAC >>
  Cases_on `H1` >> Cases_on `H2` >>
  SIMP_TAC (std_ss++symb_interpret_ss) [symb_interprs_eq_for_def, symb_interpr_get_def, IN_UNIV(*, symb_interpret_t_11*)] >>
  METIS_TAC []
QED

Theorem symb_interpr_EQ_thm:
  !H1 H2.
  (H1 = H2) <=>
  (!symb. symb_interpr_get H1 symb = symb_interpr_get H2 symb)
Proof
SIMP_TAC std_ss [GSYM symb_interprs_eq_for_EQ_thm, symb_interprs_eq_for_def, IN_UNIV]
QED

Theorem symb_interprs_eq_for_ID_thm:
  !H symbs.
  symb_interprs_eq_for H H symbs
Proof
METIS_TAC [symb_interprs_eq_for_def]
QED

Theorem symb_interprs_eq_for_COMM_thm:
  !H1 H2 symbs.
  symb_interprs_eq_for H1 H2 symbs =
  symb_interprs_eq_for H2 H1 symbs
Proof
METIS_TAC [symb_interprs_eq_for_def]
QED

Theorem symb_interprs_eq_for_SUBSET_thm:
  !H1 H2 symbs symbs_sub.
  (symbs_sub SUBSET symbs) ==>
  (symb_interprs_eq_for H1 H2 symbs) ==>
  (symb_interprs_eq_for H1 H2 symbs_sub)
Proof
FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [symb_interprs_eq_for_def] >>
  METIS_TAC [SUBSET_DEF]
QED

Theorem symb_interprs_eq_for_UNION_thm:
  !H1 H2 symbs1 symbs2.
  (symb_interprs_eq_for H1 H2 (symbs1 UNION symbs2)) <=>
  ((symb_interprs_eq_for H1 H2 symbs1) /\
   (symb_interprs_eq_for H1 H2 symbs2))
Proof
FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [symb_interprs_eq_for_def] >>
  METIS_TAC []
QED

Theorem symb_interprs_eq_for_INTER_symbs_thm:
  !H1 H2 H3 symbs1 symbs3.
  (symb_interprs_eq_for H2 H1 symbs1) ==>
  (symb_interprs_eq_for H2 H3 symbs3) ==>
  (symb_interprs_eq_for H1 H3 (symbs1 INTER symbs3))
Proof
FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [symb_interprs_eq_for_def] >>
  METIS_TAC []
QED

Theorem symb_interprs_eq_for_INTER_symbs_thm2:
  !H1 H2 symbs1 symbs2.
  (symb_interprs_eq_for H1 H2 symbs1) ==>
  (symb_interprs_eq_for H1 H2 (symbs1 INTER symbs2))
Proof
SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [symb_interprs_eq_for_def]
QED

Theorem symb_interprs_eq_for_TRANS_thm:
  !H1 H2 H3 symbs.
  (symb_interprs_eq_for H1 H2 symbs) ==>
  (symb_interprs_eq_for H2 H3 symbs) ==>
  (symb_interprs_eq_for H1 H3 symbs)
Proof
METIS_TAC [symb_interprs_eq_for_INTER_symbs_thm, INTER_IDEMPOT, symb_interprs_eq_for_COMM_thm]
QED

Theorem symb_interprs_eq_for_IMP_dom_thm:
  !H1 H2 symbs.
  (symb_interprs_eq_for H1 H2 symbs) ==>
  (symbs SUBSET symb_interpr_dom H1) ==>
  (symbs SUBSET symb_interpr_dom H2)
Proof
Cases_on `H1` >> Cases_on `H2` >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [symb_interprs_eq_for_def, SUBSET_DEF, symb_interpr_dom_def, symb_interpr_get_def]
QED

Theorem symb_interprs_eq_for_UPDATE_dom_thm:
  !H symb vo.
  symb_interprs_eq_for (symb_interpr_update H (symb, vo)) H ((symb_interpr_dom H) DELETE symb)
Proof
Cases_on `H` >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss)
    [symb_interprs_eq_for_def, symb_interpr_update_def, symb_interpr_get_def,
     symb_interpr_dom_def] >>

  METIS_TAC [APPLY_UPDATE_THM]
QED

Theorem symb_interprs_eq_for_update_thm:
  !H1 H2 symb vo symbs.
  (symb_interprs_eq_for (symb_interpr_update H1 (symb, vo)) H2 (symbs DELETE symb)) =
  (symb_interprs_eq_for H1 H2 (symbs DELETE symb))
Proof
FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss)
    [symb_interprs_eq_for_def, symb_interpr_update_def, symb_interpr_get_def,
     symb_interpr_dom_def] >>

  METIS_TAC [symb_interpr_get_update_thm]
QED

Definition symb_interpr_ext_def:
  symb_interpr_ext H1 H2 = symb_interprs_eq_for H1 H2 (symb_interpr_dom H2)
End

Theorem symb_interpr_ext_thm:
  !H1 H2.
  symb_interpr_ext H1 H2 =
    (!symb. (symb_interpr_get H2 symb <> NONE) ==> (symb_interpr_get H1 symb = symb_interpr_get H2 symb))
Proof
Cases_on `H1` >> Cases_on `H2` >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss)
    [symb_interpr_ext_def, symb_interpr_dom_def, symb_interpr_get_def, symb_interprs_eq_for_def]
QED

Theorem symb_interpr_ext_IMP_dom_thm:
  !H1 H2.
  (symb_interpr_ext H1 H2) ==>
  ((symb_interpr_dom H2) SUBSET (symb_interpr_dom H1))
Proof
Cases_on `H1` >> Cases_on `H2` >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss)
    [symb_interpr_ext_def, symb_interpr_dom_def, SUBSET_DEF, symb_interpr_get_def, symb_interprs_eq_for_def]
QED

Theorem symb_interpr_ext_id_thm:
  !H. symb_interpr_ext H H
Proof
STRIP_TAC >>
  Cases_on `H` >>
  METIS_TAC [symb_interpr_ext_def, symb_interprs_eq_for_def]
QED

Theorem symb_interpr_ext_TRANS_thm:
  !H H' H''.
  (symb_interpr_ext H  H' ) ==>
  (symb_interpr_ext H' H'') ==>
  (symb_interpr_ext H  H'' )
Proof
REPEAT STRIP_TAC >>
  Cases_on `H` >> Cases_on `H'` >> Cases_on `H''` >>
  METIS_TAC [symb_interpr_ext_thm]
QED

Theorem symb_interpr_ext_UPDATE_thm:
  !H symb vo.
  (~(symb IN symb_interpr_dom H)) ==>
  (symb_interpr_ext (symb_interpr_update H (symb, vo)) H)
Proof
Cases_on `H` >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss)
    [symb_interpr_ext_thm, APPLY_UPDATE_THM, symb_interpr_update_def, symb_interpr_get_def, symb_interpr_dom_def] >>
  METIS_TAC []
QED

Theorem symb_interpr_ext_symb_NONE_thm:
  !H symb.
  symb_interpr_ext H (symb_interpr_update H (symb, NONE))
Proof
Cases_on `H` >>
  METIS_TAC [symb_interpr_ext_thm, APPLY_UPDATE_THM, symb_interpr_update_def, symb_interpr_get_def]
QED

Theorem symb_interpr_dom_UPDATE_NONE_thm:
  !H symb.
  symb_interpr_dom (symb_interpr_update H (symb, NONE))
  = (symb_interpr_dom H) DELETE symb
Proof
Cases_on `H` >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss)
    [symb_interpr_update_def, symb_interpr_dom_def, DELETE_DEF, DIFF_DEF, EXTENSION] >>

  METIS_TAC [APPLY_UPDATE_THM]
QED

Theorem symb_interpr_dom_UPDATE_SOME_thm:
  !H symb vo.
  symb_interpr_dom (symb_interpr_update H (symb, SOME vo))
  = symb INSERT (symb_interpr_dom H)
Proof
Cases_on `H` >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss)
    [symb_interpr_update_def, symb_interpr_dom_def, EXTENSION] >>

  REPEAT STRIP_TAC >>
  Cases_on `x = symb` >> (
    FULL_SIMP_TAC std_ss [APPLY_UPDATE_THM]
  )
QED

Theorem symb_interpr_ext_IMP_eq_for_thm:
  !H1 H2 symbs.
  (symb_interpr_ext H2 H1) ==>
  (symbs SUBSET (symb_interpr_dom H1)) ==>
  (symb_interprs_eq_for H1 H2 symbs)
Proof
METIS_TAC [symb_interpr_ext_def, symb_interprs_eq_for_SUBSET_thm, SUBSET_TRANS, symb_interprs_eq_for_COMM_thm]
QED

Theorem symb_interpr_ext_IMP_eq_for_SING_thm:
  !H1 H2 symb.
  (symb_interpr_ext H2 H1) ==>
  (symb IN (symb_interpr_dom H1)) ==>
  (symb_interpr_get H1 symb = symb_interpr_get H2 symb)
Proof
METIS_TAC [symb_interpr_ext_IMP_eq_for_thm, symb_interprs_eq_for_def, SUBSET_DEF]
QED

Theorem symb_interpr_ext_IMP_eq_for_SING_thm2:
  !H1 H2 symb v.
  (symb_interpr_ext H2 H1) ==>
  (symb_interpr_get H1 symb = SOME v) ==>
  (symb_interpr_get H1 symb = symb_interpr_get H2 symb)
Proof
METIS_TAC [symb_interpr_ext_IMP_eq_for_SING_thm, symb_interpr_dom_thm, optionTheory.option_CLAUSES]
QED




(*
NOTATION: INCLUSIVE AND MINIMAL INTERPRETATIONS (dealing with the domains of interpretations)
=======================================================
*)
(* a suitable interpretation gives values to all symbols of a set *)
Definition symb_interpr_for_symbs_def:
  symb_interpr_for_symbs symbs H =
      (symbs SUBSET (symb_interpr_dom H))
End

Theorem symb_interpr_for_symbs_thm:
  !symbs H.
    symb_interpr_for_symbs symbs H =
    (!symb. (symb IN symbs) ==> (symb_interpr_get H symb <> NONE))
Proof
FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss)
    [symb_interpr_for_symbs_def, symb_interpr_dom_def, SUBSET_DEF, symb_interpr_dom_thm]
QED

(* a minimal interpretation is a suitable interpretation that does not give a value to any other symbol *)
Definition symb_interpr_for_symbs_min_def:
  symb_interpr_for_symbs_min symbs H =
      (symbs = (symb_interpr_dom H))
End

Theorem symb_interpr_for_symbs_min_thm0:
  !symbs H.
    symb_interpr_for_symbs_min symbs H =
    ((symb_interpr_for_symbs symbs H) /\
     (!symb. (symb_interpr_get H symb <> NONE) ==> (symb IN symbs)))
Proof
FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss)
    [symb_interpr_for_symbs_min_def, symb_interpr_for_symbs_thm, symb_interpr_dom_def, EXTENSION, symb_interpr_dom_thm] >>
  METIS_TAC []
QED

Theorem symb_interpr_for_symbs_min_thm:
  !symbs H.
  (symb_interpr_for_symbs_min symbs H) =
  (!symb. (symb IN symbs) = (symb_interpr_get H symb <> NONE))
Proof
METIS_TAC [symb_interpr_for_symbs_thm, symb_interpr_for_symbs_min_thm0]
QED

(* a restricting interpretation *)
(* ----------------------------------- *)
Definition symb_interpr_restr_def:
  symb_interpr_restr symbs H =
    (SymbInterpret (\symb. if symb IN symbs then symb_interpr_get H symb else NONE))
End

Theorem symb_interpr_restr_IS_eq_for_thm:
  !H symbs.
  (symb_interprs_eq_for H (symb_interpr_restr symbs H) symbs)
Proof
FULL_SIMP_TAC std_ss [symb_interprs_eq_for_def, symb_interpr_restr_def, symb_interpr_get_def]
QED

Theorem symb_interpr_restr_dom_thm:
  !H symbs.
  (symb_interpr_dom (symb_interpr_restr symbs H) = symb_interpr_dom H INTER symbs)
Proof
Cases_on `H` >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss)
    [symb_interpr_ext_def, symb_interprs_eq_for_def,
     symb_interpr_restr_def, symb_interpr_get_def, symb_interpr_dom_def,
     EXTENSION] >>
  METIS_TAC[]
QED

Theorem symb_interpr_restr_ext_thm:
  !H symbs.
  (symb_interpr_ext H (symb_interpr_restr symbs H))
Proof
Cases_on `H` >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss)
    [symb_interpr_ext_def, symb_interprs_eq_for_def,
     symb_interpr_restr_def, symb_interpr_get_def, symb_interpr_dom_def]
QED

Theorem symb_interpr_for_symbs_IMP_restr_thm:
  !H symbs.
  (symb_interpr_for_symbs symbs H) ==>
  (symb_interpr_for_symbs symbs (symb_interpr_restr symbs H))
Proof
FULL_SIMP_TAC std_ss [symb_interpr_for_symbs_thm, symb_interpr_restr_def, symb_interpr_get_def]
QED

Theorem symb_interpr_for_symbs_TO_min_thm:
  !H H' symbs.
  (H' = symb_interpr_restr symbs H) ==>

  (symb_interpr_for_symbs symbs H) ==>

  ((symb_interpr_for_symbs_min symbs H') /\
   (symb_interpr_ext H H'))
Proof
FULL_SIMP_TAC std_ss [symb_interpr_for_symbs_thm, symb_interpr_ext_thm,
     symb_interpr_for_symbs_min_thm, symb_interpr_restr_def, symb_interpr_get_def]
QED

Theorem symb_interpr_restr_thm:
  !H H' symbs symbs'.
  (H' = symb_interpr_restr  symbs' H) ==>
  (symbs SUBSET symbs') ==>

  (!symb. (symb IN symbs) ==> (symb_interpr_get H symb = symb_interpr_get H' symb))
Proof
FULL_SIMP_TAC std_ss [symb_interpr_restr_def, SUBSET_DEF, symb_interpr_get_def]
QED

(* can't remove any symbol from a minimal interpretation *)
Theorem symb_interpr_for_symbs_min_REMOVE_NOT_min_thm:
  !H H' symb symbs s.
  (symb IN (symb_interpr_dom H)) ==>
  (H' = symb_interpr_update H (symb, NONE)) ==>

  (symb_interpr_for_symbs_min symbs H) ==>
  (~(symb_interpr_for_symbs_min symbs H'))
Proof
FULL_SIMP_TAC std_ss [symb_interpr_for_symbs_min_thm, symb_interpr_dom_thm] >>
  METIS_TAC [symb_interpr_get_update_id_thm]
QED


(* domain intersection equality *)
(* ----------------------------------- *)
Definition symb_interprs_eq_for_INTER_def:
  symb_interprs_eq_for_INTER H1 H2 =
      (symb_interprs_eq_for H1 H2 ((symb_interpr_dom H1) INTER (symb_interpr_dom H2)))
End

Theorem symb_interprs_eq_for_INTER_COMM_thm:
  !H1 H2.
  (symb_interprs_eq_for_INTER H1 H2) =
  (symb_interprs_eq_for_INTER H2 H1)
Proof
METIS_TAC [symb_interprs_eq_for_INTER_def, INTER_COMM, symb_interprs_eq_for_COMM_thm]
QED

Theorem symb_interprs_eq_for_INTER_TRANS_thm:
  !H1 H2 H3.
  (symb_interprs_eq_for_INTER H1 H2) ==>
  (symb_interprs_eq_for_INTER H2 H3) ==>
  ((symb_interpr_dom H1) INTER ((symb_interpr_dom H3) DIFF (symb_interpr_dom H2)) = EMPTY) ==>
  (symb_interprs_eq_for_INTER H1 H3)
Proof
Cases_on `H1` >> Cases_on `H2` >> Cases_on `H3` >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss)
    [symb_interprs_eq_for_INTER_def, symb_interprs_eq_for_def, symb_interpr_dom_def,
     symb_interpr_get_def, INTER_DEF, DIFF_DEF, EMPTY_DEF, EXTENSION] >>
  METIS_TAC []
QED

Theorem symb_interpr_ext_IMP_interprs_eq_for_INTER_thm:
  !H1 H2 H3.
  (symb_interpr_ext H2 H1) ==>
  (symb_interpr_ext H2 H3) ==>
  (symb_interprs_eq_for_INTER H1 H3)
Proof
REWRITE_TAC [symb_interpr_ext_def, symb_interprs_eq_for_INTER_def,
               symb_interprs_eq_for_INTER_symbs_thm]
QED

Theorem symb_interprs_eq_for_INTER_doms_thm:
  !H1 H12 H2 H23 H3.
  ((symb_interpr_dom H1) INTER ((symb_interpr_dom H3) DIFF (symb_interpr_dom H2)) = EMPTY) ==>

  (symb_interpr_ext H12 H1) ==>
  (symb_interpr_ext H12 H2) ==>

  (symb_interpr_ext H23 H2) ==>
  (symb_interpr_ext H23 H3) ==>

  (symb_interprs_eq_for_INTER H1 H3)
Proof
METIS_TAC [symb_interpr_ext_IMP_interprs_eq_for_INTER_thm, symb_interprs_eq_for_INTER_TRANS_thm]
QED


(* an extended interpretation (combination) *)
(* ----------------------------------- *)
Definition symb_interpr_extend_def:
  symb_interpr_extend H_extra H_base =
    (SymbInterpret (\symb.
      if symb IN (symb_interpr_dom H_base) then
        symb_interpr_get H_base symb
      else
        symb_interpr_get H_extra symb))
End

Theorem symb_interpr_get_extend_thm:
  !H_extra H_base symb v.
  (symb_interpr_get H_base symb = SOME v) ==>
  (symb_interpr_get (symb_interpr_extend H_extra H_base) symb = SOME v)
Proof
REPEAT STRIP_TAC >>
  Cases_on `H_base` >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [symb_interpr_extend_def, symb_interpr_ext_thm, symb_interpr_dom_def, symb_interpr_get_def]
QED

Theorem symb_interpr_get_extend_dom_thm:
  !H_extra H_base symb.
  (symb IN symb_interpr_dom H_base) ==>
  (symb_interpr_get (symb_interpr_extend H_extra H_base) symb = symb_interpr_get H_base symb)
Proof
REPEAT STRIP_TAC >>
  Cases_on `H_base` >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [symb_interpr_extend_def, symb_interpr_ext_thm, symb_interpr_dom_def, symb_interpr_get_def]
QED

Theorem symb_interpr_get_extend_dom_thm2:
  !H_extra H_base symb.
  (symb_interpr_get (symb_interpr_extend H_extra H_base) symb =
   if symb IN symb_interpr_dom H_base then
     symb_interpr_get H_base symb
   else
     symb_interpr_get H_extra symb)
Proof
REPEAT STRIP_TAC >>
  Cases_on `H_base` >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [symb_interpr_extend_def, symb_interpr_ext_thm, symb_interpr_dom_def, symb_interpr_get_def]
QED

Theorem symb_interpr_dom_extend_thm:
  !H_extra H_base.
  (symb_interpr_dom (symb_interpr_extend H_extra H_base)) =
  ((symb_interpr_dom H_extra) UNION (symb_interpr_dom H_base))
Proof
REPEAT STRIP_TAC >>
  Cases_on `H_base` >> Cases_on `H_extra` >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss)
   [symb_interpr_extend_def, symb_interpr_ext_thm,
    symb_interpr_dom_def, symb_interpr_get_def, EXTENSION] >>

  GEN_TAC >>
  Cases_on `f x <> NONE` >> (
    FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) []
  )
QED

Theorem symb_interpr_extend_IMP_ext_thm:
  !H_extra H_base.
  (symb_interpr_ext (symb_interpr_extend H_extra H_base) H_base)
Proof
REPEAT STRIP_TAC >>
  Cases_on `H_base` >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [symb_interpr_extend_def, symb_interpr_ext_thm, symb_interpr_dom_def, symb_interpr_get_def]
QED

Theorem symb_interpr_extend_IMP_ext_thm2:
  !H_extra H_base.
  (symb_interprs_eq_for_INTER H_extra H_base) ==>
  (symb_interpr_ext (symb_interpr_extend H_extra H_base) H_extra)
Proof
REPEAT STRIP_TAC >>
  Cases_on `H_base` >> Cases_on `H_extra` >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss)
   [symb_interpr_extend_def, symb_interpr_ext_thm,
    symb_interpr_dom_def, symb_interpr_get_def] >>

  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss)
   [symb_interprs_eq_for_INTER_def, symb_interprs_eq_for_def,
    symb_interpr_get_def, symb_interpr_dom_def] >>

  METIS_TAC []
QED


(* an interpretation extended with arbitrary values *)
(* ----------------------------------- *)
Definition symb_interpr_extend_symbs_def:
  symb_interpr_extend_symbs valfun symbs H =
    (SymbInterpret (\symb.
      if symb IN (symb_interpr_dom H) then
        symb_interpr_get H symb
      else if symb IN symbs then
        SOME (valfun symb)
      else
        NONE))
End

Theorem symb_interpr_extend_symbs_IMP_ext_thm:
  !valfun symbs H.
  (symb_interpr_ext (symb_interpr_extend_symbs valfun symbs H) H)
Proof
REPEAT STRIP_TAC >>
  Cases_on `H` >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [symb_interpr_extend_symbs_def, symb_interpr_ext_thm, symb_interpr_dom_def, symb_interpr_get_def]
QED

Theorem symb_interpr_extend_symbs_IMP_for_symbs_thm:
  !valfun symbs H.
  (symb_interpr_for_symbs ((symb_interpr_dom H) UNION symbs) (symb_interpr_extend_symbs valfun symbs H))
Proof
REPEAT STRIP_TAC >>
  Cases_on `H` >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [symb_interpr_extend_symbs_def, symb_interpr_for_symbs_def, symb_interpr_dom_def, symb_interpr_get_def, SUBSET_DEF] >>

  REPEAT STRIP_TAC >>
  Cases_on `f x` >> (
    FULL_SIMP_TAC std_ss []
  )
QED

Theorem symb_interpr_extend_symbs_IMP_dom_thm:
  !valfun symbs H.
  (symb_interpr_dom (symb_interpr_extend_symbs valfun symbs H) = ((symb_interpr_dom H) UNION symbs))
Proof
REPEAT STRIP_TAC >>
  Cases_on `H` >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [symb_interpr_extend_symbs_def, symb_interpr_for_symbs_def, symb_interpr_dom_def, symb_interpr_get_def, SUBSET_DEF, EXTENSION] >>

  REPEAT STRIP_TAC >>
  Cases_on `f x` >> (
    FULL_SIMP_TAC std_ss []
  )
QED

Theorem symb_interpr_extend_symbs_IMP_eq_for_thm:
  !valfun symbs H.
  (symb_interprs_eq_for H (symb_interpr_extend_symbs valfun symbs H) (symb_interpr_dom H))
Proof
REPEAT STRIP_TAC >>
  Cases_on `H` >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [symb_interprs_eq_for_def, symb_interpr_extend_symbs_def, symb_interpr_for_symbs_def, symb_interpr_dom_def, symb_interpr_get_def, SUBSET_DEF, EXTENSION]
QED

Theorem symb_interpr_extend_symbs_IMP_get_thm:
  !valfun symbs H symb.
  (?v. symb_interpr_get H symb = SOME v) ==>
  (symb_interpr_get (symb_interpr_extend_symbs valfun symbs H) symb = symb_interpr_get H symb)
Proof
REPEAT STRIP_TAC >>

  `symb IN symb_interpr_dom H` by (
    FULL_SIMP_TAC std_ss [symb_interpr_dom_thm]
  ) >>

  METIS_TAC [symb_interpr_extend_symbs_IMP_eq_for_thm, symb_interprs_eq_for_def]
QED




val _ = export_theory();
