open HolKernel Parse boolLib bossLib;

open arithmeticTheory;
open pred_setTheory;
open combinTheory;

val _ = new_theory "symb_hl";

(*
``x:(('a, 'b, 'c, 'd) bir_symb_rec_t)``
``x:('c list)``

``x:(bir_symb_state_t)``

*)

(*
RECORD FOR REPRESENTING GENERIC CONCRETE AND SYMBOLIC TRANSITION SYSTEM
=======================================================
*)
val _ = Datatype `symb_concst_t =
   SymbConcSt 'a_label ('b_var -> 'c_val option)
`;
val symb_concst_pc_def = Define `
  symb_concst_pc (SymbConcSt lbl _) = lbl
`;
val symb_concst_store_def = Define `
  symb_concst_store (SymbConcSt _ store) = store
`;
(*
``SymbConcSt (0w:word64) (K (SOME "hallo"))``
*)

val _ = Datatype `symb_symbst_t =
   SymbSymbSt 'a_label ('b_var -> 'c_symbexpr option) 'c_symbexpr
`;
val symb_symbst_pc_def = Define `
  symb_symbst_pc (SymbSymbSt lbl _ _) = lbl
`;
val symb_symbst_store_def = Define `
  symb_symbst_store (SymbSymbSt _ store _) = store
`;
val symb_symbst_store_update_def = Define `
  symb_symbst_store_update var symbexpr (SymbSymbSt lbl store pcond) =
    SymbSymbSt lbl ((var =+ (SOME symbexpr)) store) pcond
`;
val symb_symbst_pcond_def = Define `
  symb_symbst_pcond (SymbSymbSt _ _ pcond) = pcond
`;
val symb_symbst_pcond_update_def = Define `
  symb_symbst_pcond_update pcond_f (SymbSymbSt lbl store pcond) =
    SymbSymbSt lbl store (pcond_f pcond)
`;


val symb_symbst_store_update_READ_thm = store_thm(
   "symb_symbst_store_update_READ_thm", ``
!var1 var2 symbexp sys.
  (symb_symbst_store (symb_symbst_store_update var1 symbexp sys) var2 =
   if var1 = var2 then SOME symbexp else symb_symbst_store sys var2)
``,
  Cases_on `sys` >>
  FULL_SIMP_TAC std_ss [symb_symbst_store_update_def, symb_symbst_store_def, APPLY_UPDATE_THM]
);
val symb_symbst_store_update_UNCHANGED_thm = store_thm(
   "symb_symbst_store_update_UNCHANGED_thm", ``
!var symbexp sys.
  (symb_symbst_pc (symb_symbst_store_update var symbexp sys) = symb_symbst_pc sys) /\
  (symb_symbst_pcond (symb_symbst_store_update var symbexp sys) = symb_symbst_pcond sys)
``,
  Cases_on `sys` >>
  FULL_SIMP_TAC std_ss [symb_symbst_store_update_def, symb_symbst_pc_def, symb_symbst_pcond_def]
);

val symb_symbst_pcond_update_READ_thm = store_thm(
   "symb_symbst_pcond_update_READ_thm", ``
!pcond_f sys.
  (symb_symbst_pcond (symb_symbst_pcond_update pcond_f sys) =
   pcond_f (symb_symbst_pcond sys))
``,
  Cases_on `sys` >>
  FULL_SIMP_TAC std_ss [symb_symbst_pcond_update_def, symb_symbst_pcond_def]
);
val symb_symbst_pcond_update_UNCHANGED_thm = store_thm(
   "symb_symbst_pcond_update_UNCHANGED_thm", ``
!pcond_f sys.
  (symb_symbst_pc (symb_symbst_pcond_update pcond_f sys) = symb_symbst_pc sys) /\
  (symb_symbst_store (symb_symbst_pcond_update pcond_f sys) = symb_symbst_store sys)
``,
  Cases_on `sys` >>
  FULL_SIMP_TAC std_ss [symb_symbst_pcond_update_def, symb_symbst_pc_def, symb_symbst_store_def]
);


(*
NOTATION: ALL ABOUT INTERPRETATIONS
=======================================================
*)

val _ = Datatype `symb_interpret_t =
   SymbInterpret ('a_symbol -> 'b_val option)
`;
val symb_interpr_get_def = Define `
    symb_interpr_get (SymbInterpret h) symb = h symb
`;
val symb_interpr_update_def = Define `
    symb_interpr_update (SymbInterpret h) (symb, vo) = SymbInterpret ((symb =+ vo) h)
`;
val symb_interpr_get_update_id_thm = store_thm(
   "symb_interpr_get_update_id_thm", ``
!H symb vo. symb_interpr_get (symb_interpr_update H (symb, vo)) symb = vo
``,
  Cases_on `H` >>
  METIS_TAC [symb_interpr_get_def, symb_interpr_update_def, APPLY_UPDATE_THM]
);

val symb_interpr_dom_def = Define `
    symb_interpr_dom (SymbInterpret h) = {symb | h symb <> NONE}
`;

val symb_interpr_dom_thm = store_thm("symb_interpr_dom_thm", ``
!H symb.
  (symb IN symb_interpr_dom H) = (symb_interpr_get H symb <> NONE)
``,
  Cases_on `H` >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss)
    [symb_interpr_dom_def, symb_interpr_get_def]
);

val symb_interprs_eq_for_def = Define `
    symb_interprs_eq_for H1 H2 symbs =
      (!symb. (symb IN symbs) ==> (symb_interpr_get H1 symb = symb_interpr_get H2 symb))
`;

val symb_interprs_eq_for_ID_thm = store_thm("symb_interprs_eq_for_ID_thm", ``
!H symbs.
  symb_interprs_eq_for H H symbs
``,
  METIS_TAC [symb_interprs_eq_for_def]
);

val symb_interprs_eq_for_COMM_thm = store_thm("symb_interprs_eq_for_COMM_thm", ``
!H1 H2 symbs.
  symb_interprs_eq_for H1 H2 symbs =
  symb_interprs_eq_for H2 H1 symbs
``,
  METIS_TAC [symb_interprs_eq_for_def]
);

val symb_interprs_eq_for_SUBSET_thm = store_thm("symb_interprs_eq_for_SUBSET_thm", ``
!H1 H2 symbs symbs_sub.
  (symbs_sub SUBSET symbs) ==>
  (symb_interprs_eq_for H1 H2 symbs) ==>
  (symb_interprs_eq_for H1 H2 symbs_sub)
``,
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [symb_interprs_eq_for_def] >>
  METIS_TAC [SUBSET_DEF]
);

val symb_interprs_eq_for_INTER_symbs_thm = store_thm(
   "symb_interprs_eq_for_INTER_symbs_thm", ``
!H1 H2 H3 symbs1 symbs3.
  (symb_interprs_eq_for H2 H1 symbs1) ==>
  (symb_interprs_eq_for H2 H3 symbs3) ==>
  (symb_interprs_eq_for H1 H3 (symbs1 INTER symbs3))
``,
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [symb_interprs_eq_for_def] >>
  METIS_TAC []
);

val symb_interprs_eq_for_TRANS_thm = store_thm(
   "symb_interprs_eq_for_TRANS_thm", ``
!H1 H2 H3 symbs.
  (symb_interprs_eq_for H1 H2 symbs) ==>
  (symb_interprs_eq_for H2 H3 symbs) ==>
  (symb_interprs_eq_for H1 H3 symbs)
``,
  METIS_TAC [symb_interprs_eq_for_INTER_symbs_thm, INTER_IDEMPOT, symb_interprs_eq_for_COMM_thm]
);

val symb_interprs_eq_for_IMP_dom_thm = store_thm(
   "symb_interprs_eq_for_IMP_dom_thm", ``
!H1 H2 symbs.
  (symb_interprs_eq_for H1 H2 symbs) ==>
  (symbs SUBSET symb_interpr_dom H1) ==>
  (symbs SUBSET symb_interpr_dom H2)
``,
  Cases_on `H1` >> Cases_on `H2` >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [symb_interprs_eq_for_def, SUBSET_DEF, symb_interpr_dom_def, symb_interpr_get_def]
);

val symb_interpr_eq_for_UPDATE_dom_thm = store_thm(
   "symb_interpr_eq_for_UPDATE_dom_thm", ``
!H symb vo.
  symb_interprs_eq_for (symb_interpr_update H (symb, vo)) H ((symb_interpr_dom H) DELETE symb)
``,
  Cases_on `H` >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss)
    [symb_interprs_eq_for_def, symb_interpr_update_def, symb_interpr_get_def,
     symb_interpr_dom_def] >>

  METIS_TAC [APPLY_UPDATE_THM]
);

val symb_interpr_ext_def = Define `
  symb_interpr_ext H1 H2 = symb_interprs_eq_for H1 H2 (symb_interpr_dom H2)
`;

val symb_interpr_ext_thm = store_thm("symb_interpr_ext_thm", ``
!H1 H2.
  symb_interpr_ext H1 H2 =
    (!symb. (symb_interpr_get H2 symb <> NONE) ==> (symb_interpr_get H1 symb = symb_interpr_get H2 symb))
``,
  Cases_on `H1` >> Cases_on `H2` >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss)
    [symb_interpr_ext_def, symb_interpr_dom_def, symb_interpr_get_def, symb_interprs_eq_for_def]
);

val symb_interpr_ext_IMP_dom_thm = store_thm("symb_interpr_ext_IMP_dom_thm", ``
!H1 H2.
  (symb_interpr_ext H1 H2) ==>
  ((symb_interpr_dom H2) SUBSET (symb_interpr_dom H1))
``,
  Cases_on `H1` >> Cases_on `H2` >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss)
    [symb_interpr_ext_def, symb_interpr_dom_def, SUBSET_DEF, symb_interpr_get_def, symb_interprs_eq_for_def]
);

val symb_interpr_ext_id_thm = store_thm("symb_interpr_ext_id_thm", ``
!H. symb_interpr_ext H H
``,
  STRIP_TAC >>
  Cases_on `H` >>
  METIS_TAC [symb_interpr_ext_def, symb_interprs_eq_for_def]
);

val symb_interpr_ext_TRANS_thm = store_thm("symb_interpr_ext_TRANS_thm", ``
!H H' H''.
  (symb_interpr_ext H  H' ) ==>
  (symb_interpr_ext H' H'') ==>
  (symb_interpr_ext H  H'' )
``,
  REPEAT STRIP_TAC >>
  Cases_on `H` >> Cases_on `H'` >> Cases_on `H''` >>
  METIS_TAC [symb_interpr_ext_thm]
);

val symb_interpr_ext_UPDATE_thm = store_thm(
   "symb_interpr_ext_UPDATE_thm", ``
!H symb vo.
  (~(symb IN symb_interpr_dom H)) ==>
  (symb_interpr_ext (symb_interpr_update H (symb, vo)) H)
``,
  Cases_on `H` >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss)
    [symb_interpr_ext_thm, APPLY_UPDATE_THM, symb_interpr_update_def, symb_interpr_get_def, symb_interpr_dom_def] >>
  METIS_TAC []
);

val symb_interpr_ext_symb_NONE_thm = store_thm(
   "symb_interpr_ext_symb_NONE_thm", ``
!H symb.
  symb_interpr_ext H (symb_interpr_update H (symb, NONE))
``,
  Cases_on `H` >>
  METIS_TAC [symb_interpr_ext_thm, APPLY_UPDATE_THM, symb_interpr_update_def, symb_interpr_get_def]
);

val symb_interpr_dom_UPDATE_NONE_thm = store_thm(
   "symb_interpr_dom_UPDATE_NONE_thm", ``
!H symb.
  symb_interpr_dom (symb_interpr_update H (symb, NONE))
  = (symb_interpr_dom H) DELETE symb
``,
  Cases_on `H` >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss)
    [symb_interpr_update_def, symb_interpr_dom_def, DELETE_DEF, DIFF_DEF, EXTENSION] >>

  METIS_TAC [APPLY_UPDATE_THM]
);

val symb_interpr_dom_UPDATE_SOME_thm = store_thm(
   "symb_interpr_dom_UPDATE_SOME_thm", ``
!H symb vo.
  symb_interpr_dom (symb_interpr_update H (symb, SOME vo))
  = symb INSERT (symb_interpr_dom H)
``,
  Cases_on `H` >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss)
    [symb_interpr_update_def, symb_interpr_dom_def, EXTENSION] >>

  REPEAT STRIP_TAC >>
  Cases_on `x = symb` >> (
    FULL_SIMP_TAC std_ss [APPLY_UPDATE_THM]
  )
);

val symb_interpr_ext_IMP_eq_for_thm = store_thm(
   "symb_interpr_ext_IMP_eq_for_thm", ``
!H1 H2 symbs.
  (symb_interpr_ext H2 H1) ==>
  (symbs SUBSET (symb_interpr_dom H1)) ==>
  (symb_interprs_eq_for H1 H2 symbs)
``,
  METIS_TAC [symb_interpr_ext_def, symb_interprs_eq_for_SUBSET_thm, SUBSET_TRANS, symb_interprs_eq_for_COMM_thm]
);




(*
NOTATION: INCLUSIVE AND MINIMAL INTERPRETATIONS (dealing with the domains of interpretations)
=======================================================
*)
(* a suitable interpretation gives values to all symbols of a set *)
val symb_interpr_for_symbs_def = Define `
    symb_interpr_for_symbs symbs H =
      (symbs SUBSET (symb_interpr_dom H))
`;

val symb_interpr_for_symbs_thm = store_thm(
   "symb_interpr_for_symbs_thm", ``
!symbs H.
    symb_interpr_for_symbs symbs H =
    (!symb. (symb IN symbs) ==> (symb_interpr_get H symb <> NONE))
``,
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss)
    [symb_interpr_for_symbs_def, symb_interpr_dom_def, SUBSET_DEF, symb_interpr_dom_thm]
);

(* a minimal interpretation is a suitable interpretation that does not give a value to any other symbol *)
val symb_interpr_for_symbs_min_def = Define `
    symb_interpr_for_symbs_min symbs H =
      (symbs = (symb_interpr_dom H))
`;

val symb_interpr_for_symbs_min_thm0 = store_thm(
   "symb_interpr_for_symbs_min_thm0", ``
!symbs H.
    symb_interpr_for_symbs_min symbs H =
    ((symb_interpr_for_symbs symbs H) /\
     (!symb. (symb_interpr_get H symb <> NONE) ==> (symb IN symbs)))
``,
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss)
    [symb_interpr_for_symbs_min_def, symb_interpr_for_symbs_thm, symb_interpr_dom_def, EXTENSION, symb_interpr_dom_thm] >>
  METIS_TAC []
);

val symb_interpr_for_symbs_min_thm = store_thm(
   "symb_interpr_for_symbs_min_thm", ``
!symbs H.
  (symb_interpr_for_symbs_min symbs H) =
  (!symb. (symb IN symbs) = (symb_interpr_get H symb <> NONE))
``,
  METIS_TAC [symb_interpr_for_symbs_thm, symb_interpr_for_symbs_min_thm0]
);

(* a restricting interpretation *)
(* ----------------------------------- *)
val symb_interpr_restr_def = Define `
    symb_interpr_restr symbs H =
    (SymbInterpret (\symb. if symb IN symbs then symb_interpr_get H symb else NONE))
`;

val symb_interpr_restr_IS_eq_for_thm = store_thm(
   "symb_interpr_restr_IS_eq_for_thm", ``
!H symbs.
  (symb_interprs_eq_for H (symb_interpr_restr symbs H) symbs)
``,
  FULL_SIMP_TAC std_ss [symb_interprs_eq_for_def, symb_interpr_restr_def, symb_interpr_get_def]
);

val symb_interpr_for_symbs_IMP_restr_thm = store_thm(
   "symb_interpr_for_symbs_IMP_restr_thm", ``
!H symbs.
  (symb_interpr_for_symbs symbs H) ==>
  (symb_interpr_for_symbs symbs (symb_interpr_restr symbs H))
``,
  FULL_SIMP_TAC std_ss [symb_interpr_for_symbs_thm, symb_interpr_restr_def, symb_interpr_get_def]
);

val symb_interpr_for_symbs_TO_min_thm = store_thm(
   "symb_interpr_for_symbs_TO_min_thm", ``
!H H' symbs.
  (H' = symb_interpr_restr symbs H) ==>

  (symb_interpr_for_symbs symbs H) ==>

  ((symb_interpr_for_symbs_min symbs H') /\
   (symb_interpr_ext H H'))
``,
  FULL_SIMP_TAC std_ss [symb_interpr_for_symbs_thm, symb_interpr_ext_thm,
     symb_interpr_for_symbs_min_thm, symb_interpr_restr_def, symb_interpr_get_def]
);

val symb_interpr_restr_thm = store_thm(
   "symb_interpr_restr_thm", ``
!H H' symbs symbs'.
  (H' = symb_interpr_restr  symbs' H) ==>
  (symbs SUBSET symbs') ==>

  (!symb. (symb IN symbs) ==> (symb_interpr_get H symb = symb_interpr_get H' symb))
``,
  FULL_SIMP_TAC std_ss [symb_interpr_restr_def, pred_setTheory.SUBSET_DEF, symb_interpr_get_def]
);

(* can't remove any symbol from a minimal interpretation *)
val symb_interpr_for_symbs_min_REMOVE_NOT_min_thm = store_thm(
   "symb_interpr_for_symbs_min_REMOVE_NOT_min_thm", ``
!H H' symb symbs s.
  (symb IN (symb_interpr_dom H)) ==>
  (H' = symb_interpr_update H (symb, NONE)) ==>

  (symb_interpr_for_symbs_min symbs H) ==>
  (~(symb_interpr_for_symbs_min symbs H'))
``,
  FULL_SIMP_TAC std_ss [symb_interpr_for_symbs_min_thm, symb_interpr_dom_thm] >>
  METIS_TAC [symb_interpr_get_update_id_thm]
);


(* domain intersection equality *)
(* ----------------------------------- *)
val symb_interprs_eq_for_INTER_def = Define `
    symb_interprs_eq_for_INTER H1 H2 =
      (symb_interprs_eq_for H1 H2 ((symb_interpr_dom H1) INTER (symb_interpr_dom H2)))
`;

val symb_interprs_eq_for_INTER_COMM_thm = store_thm(
   "symb_interprs_eq_for_INTER_COMM_thm", ``
!H1 H2.
  (symb_interprs_eq_for_INTER H1 H2) =
  (symb_interprs_eq_for_INTER H2 H1)
``,
  METIS_TAC [symb_interprs_eq_for_INTER_def, INTER_COMM, symb_interprs_eq_for_COMM_thm]
);

val symb_interprs_eq_for_INTER_TRANS_thm = store_thm(
   "symb_interprs_eq_for_INTER_TRANS_thm", ``
!H1 H2 H3.
  (symb_interprs_eq_for_INTER H1 H2) ==>
  (symb_interprs_eq_for_INTER H2 H3) ==>
  ((symb_interpr_dom H1) INTER ((symb_interpr_dom H3) DIFF (symb_interpr_dom H2)) = EMPTY) ==>
  (symb_interprs_eq_for_INTER H1 H3)
``,
  Cases_on `H1` >> Cases_on `H2` >> Cases_on `H3` >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss)
    [symb_interprs_eq_for_INTER_def, symb_interprs_eq_for_def, symb_interpr_dom_def,
     symb_interpr_get_def, INTER_DEF, DIFF_DEF, EMPTY_DEF, EXTENSION] >>
  METIS_TAC []
);

val symb_interpr_ext_IMP_interprs_eq_for_INTER_thm = store_thm(
   "symb_interpr_ext_IMP_interprs_eq_for_INTER_thm", ``
!H1 H2 H3.
  (symb_interpr_ext H2 H1) ==>
  (symb_interpr_ext H2 H3) ==>
  (symb_interprs_eq_for_INTER H1 H3)
``,
  REWRITE_TAC [symb_interpr_ext_def, symb_interprs_eq_for_INTER_def,
               symb_interprs_eq_for_INTER_symbs_thm]
);


(* an extended interpretation (combination) *)
(* ----------------------------------- *)
val symb_interpr_extend_def = Define `
    symb_interpr_extend H_extra H_base =
    (SymbInterpret (\symb.
      if symb IN (symb_interpr_dom H_base) then
        symb_interpr_get H_base symb
      else
        symb_interpr_get H_extra symb))
`;

val symb_interpr_extend_IMP_ext_thm = store_thm(
   "symb_interpr_extend_IMP_ext_thm", ``
!H_extra H_base.
  (symb_interpr_ext (symb_interpr_extend H_extra H_base) H_base)
``,
  REPEAT STRIP_TAC >>
  Cases_on `H_base` >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [symb_interpr_extend_def, symb_interpr_ext_thm, symb_interpr_dom_def, symb_interpr_get_def]
);

val symb_interpr_extend_IMP_ext_thm2 = store_thm(
   "symb_interpr_extend_IMP_ext_thm2", ``
!H_extra H_base.
  (symb_interprs_eq_for_INTER H_extra H_base) ==>
  (symb_interpr_ext (symb_interpr_extend H_extra H_base) H_extra)
``,
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
);


(* an interpretation extended with arbitrary values *)
(* ----------------------------------- *)
val symb_interpr_extend_symbs_def = Define `
    symb_interpr_extend_symbs symbs H =
    (SymbInterpret (\symb.
      if symb IN (symb_interpr_dom H) then
        symb_interpr_get H symb
      else if symb IN symbs then
        SOME ARB (* TODO: need to become correctly typed values later *)
      else
        NONE))
`;

val symb_interpr_extend_symbs_IMP_ext_thm = store_thm(
   "symb_interpr_extend_symbs_IMP_ext_thm", ``
!symbs H.
  (symb_interpr_ext (symb_interpr_extend_symbs symbs H) H)
``,
  REPEAT STRIP_TAC >>
  Cases_on `H` >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [symb_interpr_extend_symbs_def, symb_interpr_ext_thm, symb_interpr_dom_def, symb_interpr_get_def]
);

val symb_interpr_extend_symbs_IMP_for_symbs_thm = store_thm(
   "symb_interpr_extend_symbs_IMP_for_symbs_thm", ``
!symbs H.
  (symb_interpr_for_symbs ((symb_interpr_dom H) UNION symbs) (symb_interpr_extend_symbs symbs H))
``,
  REPEAT STRIP_TAC >>
  Cases_on `H` >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [symb_interpr_extend_symbs_def, symb_interpr_for_symbs_def, symb_interpr_dom_def, symb_interpr_get_def, SUBSET_DEF] >>

  REPEAT STRIP_TAC >>
  Cases_on `f x` >> (
    FULL_SIMP_TAC std_ss []
  )
);


(*
NOTION: INSTANTIATION DATATYPE
=======================================================
*)
val _ = Datatype `symb_rec_t =
   <|
      (* required symbolic expression building blocks *)
      sr_val_true        : 'c_val;

      sr_mk_exp_symb_f   : 'd_symbol -> 'e_symbexpr;

      sr_mk_exp_conj_f   : 'e_symbexpr -> 'e_symbexpr -> 'e_symbexpr;

      sr_mk_exp_eq_f     : 'e_symbexpr -> 'e_symbexpr -> 'e_symbexpr;

      sr_subst_f         : ('d_symbol # 'e_symbexpr) -> 'e_symbexpr -> 'e_symbexpr;

      (* symbols of symbolic exepressions *)
      sr_symbols_f       : 'e_symbexpr ->
                           ('d_symbol -> bool);

      (* interpretation business, type error returns NONE value *)
      sr_interpret_f     : (('d_symbol, 'c_val) symb_interpret_t) ->
                           'e_symbexpr ->
                           'c_val option;

      (* finally, concrete and symbolic executions *)
      sr_step_conc       : (('a_label, 'b_var, 'c_val) symb_concst_t) ->
                           (('a_label, 'b_var, 'c_val) symb_concst_t);

      sr_step_symb       : (('a_label, 'b_var, 'e_symbexpr) symb_symbst_t) ->
                           ((('a_label, 'b_var, 'e_symbexpr) symb_symbst_t) ->
                           bool);
   |>`;

val symb_rec_t_tm = ``: ('a, 'b, 'c, 'd, 'e) symb_rec_t``;
val symb_concst_t_tm = ``: ('a, 'b, 'c) symb_concst_t``;

val symb_list_of_types = [
  (*mk_thy_type {Tyop="symb_concst_t",   Thy="scratch", Args=[Type.alpha, Type.beta, Type.gamma]}*)
  mk_type ("symb_concst_t", [Type.alpha, Type.beta, Type.gamma]),
  mk_type ("symb_symbst_t", [Type.alpha, Type.beta, Type.gamma]),
  mk_type ("symb_interpret_t", [Type.alpha, Type.beta])
];

val symb_TYPES_thms = (flatten (map type_rws symb_list_of_types));
val symb_TYPES_ss = rewrites symb_TYPES_thms;


(*
DEFINITIONS: INSTANTIATION FOR BIR/SBIR
=======================================================
*)
(*
val _ = Datatype `bir_conc_state_t = int`;
val _ = Datatype `bir_symb_state_t = int`;

val bir_symb_rec_sbir_def = Define `
  bir_symb_rec_sbir a b c d =
    <|
      sr_val_true        := a;
      sr_interpret_f     := b;
      sr_step_conc       := c;
      sr_step_symb       := d;
   |>
`;
*)


(*
ASSUMPTION: sr_symbols_f
=======================================================
*)
(* the symbols of a symbolic expression are sound if, for any symbolic expression,
   equal valuation of those in two interpretations implies the same value for the interpretation of the symbolic expression *)
val symb_symbols_f_sound_def = Define `
    symb_symbols_f_sound sr =
    (!symbexp H H'.
       (symb_interprs_eq_for H H' (sr.sr_symbols_f symbexp)) ==>
       (sr.sr_interpret_f H  symbexp =
        sr.sr_interpret_f H' symbexp))
`;

val symb_symbols_f_sound_thm = store_thm(
   "symb_symbols_f_sound_thm", ``
!sr.
    symb_symbols_f_sound sr =
    (!symbexp H H'.
       (!symb. (symb IN (sr.sr_symbols_f symbexp)) ==> (symb_interpr_get H symb = symb_interpr_get H' symb)) ==>
       (sr.sr_interpret_f H  symbexp =
        sr.sr_interpret_f H' symbexp))
``,
  REWRITE_TAC [symb_symbols_f_sound_def, symb_interprs_eq_for_def]
);

val symb_interpr_restr_interpret_EQ_thm = store_thm(
   "symb_interpr_restr_interpret_EQ_thm", ``
!sr.
!H symbs symbexp.
  (symb_symbols_f_sound sr) ==>

  ((sr.sr_symbols_f symbexp) SUBSET symbs) ==>

  (sr.sr_interpret_f H symbexp = sr.sr_interpret_f (symb_interpr_restr symbs H) symbexp)
``,
  FULL_SIMP_TAC std_ss [symb_symbols_f_sound_thm] >>
  METIS_TAC [symb_interpr_restr_thm]
);

(*
NOTION: SYMBOL DEPENDENCE FOR STORE AND STATE AND SET OF STATES
=======================================================
*)

val symb_symbols_store_def = Define `
    symb_symbols_store sr store =
      BIGUNION ({sr.sr_symbols_f symbexp | ?var. store var = SOME symbexp})
`;
val symb_symbols_def = Define `
    symb_symbols sr sys =
      (symb_symbols_store sr (symb_symbst_store sys) UNION
       sr.sr_symbols_f (symb_symbst_pcond sys))
`;

val symb_symbols_SUBSET_pcond_thm = store_thm(
   "symb_symbols_SUBSET_pcond_thm", ``
!sr.
!sys.
  (sr.sr_symbols_f (symb_symbst_pcond sys))
  SUBSET
  (symb_symbols sr sys)
``,
  METIS_TAC [symb_symbols_def, SUBSET_UNION]
);

val symb_symbols_SUBSET_store_thm = store_thm(
   "symb_symbols_SUBSET_store_thm", ``
!sr.
!sys.
  (symb_symbols_store sr (symb_symbst_store sys))
  SUBSET
  (symb_symbols sr sys)
``,
  METIS_TAC [symb_symbols_def, SUBSET_UNION]
);

val symb_symbols_SUBSET_store_exps_thm = store_thm(
   "symb_symbols_SUBSET_store_exps_thm", ``
!sr.
!store var symbexp.
  ((store var) = SOME symbexp) ==>
  ((sr.sr_symbols_f symbexp)
   SUBSET
   (symb_symbols_store sr store))
``,
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [symb_symbols_store_def, SUBSET_DEF] >>
  METIS_TAC []
);

val symb_symbols_SUBSET_store_exps_thm2 = store_thm(
   "symb_symbols_SUBSET_store_exps_thm2", ``
!sr.
!sys var symbexp.
  (((symb_symbst_store sys) var) = SOME symbexp) ==>
  ((sr.sr_symbols_f symbexp)
   SUBSET
   (symb_symbols sr sys))
``,
  METIS_TAC [symb_symbols_def, symb_symbols_SUBSET_store_exps_thm, symb_symbols_SUBSET_store_thm, UNION_SUBSET, SUBSET_TRANS]
);

val symb_symbols_set_def = Define `
    symb_symbols_set sr Pi =
      BIGUNION ({symb_symbols sr sys | sys IN Pi})
`;

val symb_symbols_set_SUBSET_thm = store_thm(
   "symb_symbols_set_SUBSET_thm", ``
!sr.
!sys Pi.
  (sys IN Pi) ==>
  ((symb_symbols sr sys) SUBSET (symb_symbols_set sr Pi))
``,
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [symb_symbols_set_def, BIGUNION, SUBSET_DEF] >>
  METIS_TAC []
);

val symb_symbols_of_symb_symbst_store_update_SUBSET_store_exps_thm2 = store_thm(
   "symb_symbols_of_symb_symbst_store_update_SUBSET_store_exps_thm2", ``
!sr.
!var symbexp sys.
  (sr.sr_symbols_f symbexp) SUBSET (symb_symbols sr (symb_symbst_store_update var symbexp sys))
``,
  REPEAT STRIP_TAC >>
  Cases_on `sys` >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss)
    [symb_symbst_store_update_def, symb_symbols_def,
     symb_symbst_store_def, symb_symbols_store_def] >>

  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss)
    [symb_symbols_store_def, SUBSET_DEF] >>

  METIS_TAC [APPLY_UPDATE_THM]
);

val symb_symbols_of_symb_symbst_store_update_SUBSET1_thm = store_thm(
   "symb_symbols_of_symb_symbst_store_update_SUBSET1_thm", ``
!sr.
!var symbexp sys.
  ((symb_symbols sr (symb_symbst_store_update var symbexp sys)) SUBSET
   ((symb_symbols sr sys) UNION (sr.sr_symbols_f symbexp)))
``,
  REPEAT STRIP_TAC >>
  Cases_on `sys` >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss)
    [symb_symbst_store_update_def, symb_symbols_def,
     symb_symbst_store_def, symb_symbst_pcond_def] >>

  REPEAT STRIP_TAC >- (
    FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss)
      [symb_symbols_store_def, BIGUNION_SUBSET] >>

    FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss)
      [symb_symbols_store_def, SUBSET_DEF] >>

    REPEAT STRIP_TAC >>
    Cases_on `var = var'` >- (
      FULL_SIMP_TAC std_ss [] >>
      REV_FULL_SIMP_TAC std_ss [APPLY_UPDATE_THM]
    ) >>

    METIS_TAC [APPLY_UPDATE_THM]
  ) >>

  METIS_TAC [SUBSET_UNION, SUBSET_TRANS]
);

val symb_symbols_of_symb_symbst_store_update_SUBSET2_thm = store_thm(
   "symb_symbols_of_symb_symbst_store_update_SUBSET2_thm", ``
!sr.
!var symbexp symbexp' sys.
  ((symb_symbst_store sys) var = SOME symbexp') ==>
  ((symb_symbols sr sys) SUBSET
   ((symb_symbols sr (symb_symbst_store_update var symbexp sys)) UNION
    (sr.sr_symbols_f (symbexp')))
  )
``,
  REPEAT STRIP_TAC >>
  Cases_on `sys` >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss)
    [symb_symbst_store_update_def, symb_symbols_def,
     symb_symbst_store_def, symb_symbst_pcond_def] >>

  REPEAT STRIP_TAC >- (
    FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss)
      [symb_symbols_store_def, BIGUNION_SUBSET] >>

    FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss)
      [symb_symbols_store_def, SUBSET_DEF] >>

    REPEAT STRIP_TAC >>
    Cases_on `var = var'` >- (
      FULL_SIMP_TAC std_ss [] >>
      REV_FULL_SIMP_TAC std_ss []
    ) >>

    METIS_TAC [APPLY_UPDATE_THM]
  ) >>

  METIS_TAC [SUBSET_UNION, SUBSET_TRANS]
);

val symb_symbols_of_symb_symbst_pcond_update_SUBSET1_thm = store_thm(
   "symb_symbols_of_symb_symbst_pcond_update_SUBSET1_thm", ``
!sr.
!pcond_f sys.
  ((symb_symbols sr (symb_symbst_pcond_update pcond_f sys)) SUBSET
   ((symb_symbols sr sys) UNION (sr.sr_symbols_f (pcond_f (symb_symbst_pcond sys)))))
``,
  REPEAT STRIP_TAC >>
  Cases_on `sys` >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss)
    [symb_symbst_pcond_update_def, symb_symbols_def,
     symb_symbst_store_def, symb_symbst_pcond_def] >>
  METIS_TAC [SUBSET_UNION, SUBSET_TRANS]
);

val symb_symbols_of_symb_symbst_pcond_update_SUBSET2_thm = store_thm(
   "symb_symbols_of_symb_symbst_pcond_update_SUBSET2_thm", ``
!sr.
!pcond_f sys.
  ((symb_symbols sr sys) SUBSET
   ((symb_symbols sr (symb_symbst_pcond_update pcond_f sys)) UNION
    (sr.sr_symbols_f (symb_symbst_pcond sys)))
  )
``,
  REPEAT STRIP_TAC >>
  Cases_on `sys` >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss)
    [symb_symbst_pcond_update_def, symb_symbols_def,
     symb_symbst_store_def, symb_symbst_pcond_def] >>
  METIS_TAC [SUBSET_UNION, SUBSET_TRANS]
);





(*
NOTATION: INTERPRETATION OF SYMBOLIC STATES AND SYMBOLIC PATH CONDITIONS
=======================================================
*)
val symb_interpr_symbstore_def = Define `
  symb_interpr_symbstore sr H sys s =
    (!var. (symb_symbst_store sys var <> NONE \/ symb_concst_store s var <> NONE) ==>
         ?symbexp v.
            symb_symbst_store sys var = SOME symbexp /\
            symb_concst_store s var = SOME v /\
            sr.sr_interpret_f H symbexp = SOME v)
`;

val symb_interprs_eq_for_store_IMP_EQ_thm = store_thm(
   "symb_interprs_eq_for_store_IMP_EQ_thm", ``
!sr.
!H1 H2 sys s.
  (symb_symbols_f_sound sr) ==>

  (symb_interprs_eq_for H1 H2 (symb_symbols_store sr (symb_symbst_store sys))) ==>
  ((symb_interpr_symbstore sr H1 sys s) =
   (symb_interpr_symbstore sr H2 sys s))
``,
  FULL_SIMP_TAC std_ss [symb_interpr_symbstore_def] >>
  REPEAT STRIP_TAC >>

  EQ_TAC >> (
    REPEAT STRIP_TAC >>
    PAT_X_ASSUM ``!x.A`` (ASSUME_TAC o (Q.SPEC `var`)) >>
    REV_FULL_SIMP_TAC std_ss [] >>

    METIS_TAC [symb_symbols_SUBSET_store_exps_thm,
               symb_symbols_f_sound_def, symb_interprs_eq_for_SUBSET_thm, SUBSET_TRANS]
  )
);

val symb_symbst_store_IMP_EQ_thm = store_thm(
   "symb_symbst_store_IMP_EQ_thm", ``
!sr.
!H sys1 sys2 s.
  (symb_symbst_store sys1 = symb_symbst_store sys2) ==>
  ((symb_interpr_symbstore sr H sys1 s) =
   (symb_interpr_symbstore sr H sys2 s))
``,
  FULL_SIMP_TAC std_ss [symb_interpr_symbstore_def]
);

val symb_symbst_store_update_IMP_EQ_thm = store_thm(
   "symb_symbst_store_update_IMP_EQ_thm", ``
!sr.
!H sys1 sys2 var symbexp symbexp' s.
  ((symb_symbst_store sys1) var = SOME symbexp) ==>
  (sys2 = symb_symbst_store_update var symbexp' sys1) ==>

  (sr.sr_interpret_f H symbexp =
   sr.sr_interpret_f H symbexp') ==>

  ((symb_interpr_symbstore sr H sys1 s) =
   (symb_interpr_symbstore sr H sys2 s))
``,
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [symb_interpr_symbstore_def] >>

  (* proof as two implications considering all variables var' *)
  EQ_TAC >> (
    REPEAT STRIP_TAC >>
    Cases_on `var = var'` >> (
      PAT_X_ASSUM ``!x. A`` (ASSUME_TAC o (Q.SPEC `var'`)) >>
      FULL_SIMP_TAC std_ss [symb_symbst_store_update_READ_thm] >>
      REV_FULL_SIMP_TAC std_ss []
    )
  )
);

val symb_interpr_symbpcond_def = Define `
  symb_interpr_symbpcond sr H sys =
    (sr.sr_interpret_f H (symb_symbst_pcond sys) = SOME sr.sr_val_true)
`;

val symb_interprs_eq_for_pcond_IMP_EQ_thm = store_thm(
   "symb_interprs_eq_for_pcond_IMP_EQ_thm", ``
!sr.
!H1 H2 sys.
  (symb_symbols_f_sound sr) ==>

  (symb_interprs_eq_for H1 H2 (sr.sr_symbols_f (symb_symbst_pcond sys))) ==>
  ((symb_interpr_symbpcond sr H1 sys) =
   (symb_interpr_symbpcond sr H2 sys))
``,
  FULL_SIMP_TAC std_ss [symb_interpr_symbpcond_def] >>
  METIS_TAC [symb_symbols_SUBSET_pcond_thm,
             symb_symbols_f_sound_def, symb_interprs_eq_for_SUBSET_thm, SUBSET_TRANS]
);

val symb_symbst_pcond_IMP_EQ_thm = store_thm(
   "symb_symbst_pcond_IMP_EQ_thm", ``
!sr.
!H sys1 sys2 s.
  (symb_symbst_pcond sys1 = symb_symbst_pcond sys2) ==>
  ((symb_interpr_symbpcond sr H sys1) =
   (symb_interpr_symbpcond sr H sys2))
``,
  FULL_SIMP_TAC std_ss [symb_interpr_symbpcond_def]
);

val symb_symbst_pcond_update_IMP_EQ_thm = store_thm(
   "symb_symbst_pcond_update_IMP_EQ_thm", ``
!sr.
!H sys1 sys2 pcond pcond_f.
  (symb_symbst_pcond sys1 = pcond) ==>
  (sys2 = symb_symbst_pcond_update pcond_f sys1) ==>

  (sr.sr_interpret_f H pcond =
   sr.sr_interpret_f H (pcond_f pcond)) ==>

  ((symb_interpr_symbpcond sr H sys1) =
   (symb_interpr_symbpcond sr H sys2))
``,
  REPEAT STRIP_TAC >>
  Cases_on `sys1` >>
  FULL_SIMP_TAC std_ss [symb_interpr_symbpcond_def, symb_symbst_pcond_update_READ_thm]
);




(*
NOTATION: STATE MATCHING
=======================================================
*)
val symb_suitable_interpretation_def = Define `
    symb_suitable_interpretation sr sys H =
      symb_interpr_for_symbs (symb_symbols sr sys) H
`;

val symb_suitable_interpretation_SUBSET_dom_thm = store_thm(
   "symb_suitable_interpretation_SUBSET_dom_thm", ``
!sr.
!sys H.
  (symb_suitable_interpretation sr sys H) =
  ((symb_symbols sr sys) SUBSET (symb_interpr_dom H))
``,
  REWRITE_TAC [symb_suitable_interpretation_def, symb_interpr_for_symbs_def]
);

val symb_minimal_interpretation_def = Define `
    symb_minimal_interpretation sr sys H =
      symb_interpr_for_symbs_min (symb_symbols sr sys) H
`;

val symb_minimal_interpretation_EQ_dom_thm = store_thm(
   "symb_minimal_interpretation_EQ_dom_thm", ``
!sr.
!sys H.
  (symb_minimal_interpretation sr sys H) =
  (symb_symbols sr sys = symb_interpr_dom H)
``,
  REWRITE_TAC [symb_minimal_interpretation_def, symb_interpr_for_symbs_min_def]
);

(*
(syl,syst,syp)
(l, st)
*)
val symb_matchstate_def = Define `
  symb_matchstate ^(mk_var("sr", symb_rec_t_tm)) sys H ^(mk_var("s", symb_concst_t_tm)) =
    (symb_suitable_interpretation sr sys H /\
     symb_symbst_pc sys = symb_concst_pc s /\
     symb_interpr_symbstore sr H sys s /\
     symb_interpr_symbpcond sr H sys)
`;

val symb_interprs_eq_for_matchstate_IMP_matchstate_thm = store_thm(
   "symb_interprs_eq_for_matchstate_IMP_matchstate_thm", ``
!sr.
!sys H1 H2 s.
  (symb_symbols_f_sound sr) ==>

  (symb_interprs_eq_for H1 H2 (symb_symbols sr sys)) ==>
  ((symb_matchstate sr sys H1 s) =
   (symb_matchstate sr sys H2 s))
``,
  FULL_SIMP_TAC std_ss [symb_matchstate_def, symb_suitable_interpretation_SUBSET_dom_thm] >>
  REPEAT STRIP_TAC >>

  EQ_TAC >> (
    FULL_SIMP_TAC std_ss [] >>
    REPEAT STRIP_TAC >> (
      METIS_TAC ( [symb_interprs_eq_for_IMP_dom_thm, symb_interprs_eq_for_COMM_thm]
                 @[SUBSET_TRANS, symb_interprs_eq_for_SUBSET_thm]
                 @[symb_symbols_SUBSET_store_thm, symb_interprs_eq_for_store_IMP_EQ_thm]
                 @[symb_symbols_SUBSET_pcond_thm, symb_interprs_eq_for_pcond_IMP_EQ_thm])
    )
  )
);

val symb_symbst_store_update_IMP_matchstate_EQ_thm = store_thm(
   "symb_symbst_store_update_IMP_matchstate_EQ_thm", ``
!sr.
!H sys1 sys2 var symbexp symbexp' s.
  ((symb_symbst_store sys1) var = SOME symbexp) ==>
  (sys2 = symb_symbst_store_update var symbexp' sys1) ==>

  (((sr.sr_symbols_f symbexp) UNION
    (sr.sr_symbols_f symbexp')) SUBSET (symb_interpr_dom H)) ==>

  (sr.sr_interpret_f H symbexp =
   sr.sr_interpret_f H symbexp') ==>

  ((symb_matchstate sr sys1 H s) =
   (symb_matchstate sr sys2 H s))
``,
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [symb_matchstate_def] >>

  EQ_TAC >> (
    FULL_SIMP_TAC std_ss [symb_interpr_symbpcond_def, symb_symbst_store_update_UNCHANGED_thm] >>
    REPEAT STRIP_TAC >> (
      FULL_SIMP_TAC std_ss [symb_suitable_interpretation_def, symb_interpr_for_symbs_def] >>
      METIS_TAC
       [symb_symbst_store_update_IMP_EQ_thm, SUBSET_TRANS, UNION_SUBSET,
        symb_symbols_of_symb_symbst_store_update_SUBSET1_thm,
        symb_symbols_of_symb_symbst_store_update_SUBSET2_thm]
    )
  )
);

val symb_symbst_pcond_update_IMP_matchstate_EQ_thm = store_thm(
   "symb_symbst_pcond_update_IMP_matchstate_EQ_thm", ``
!sr.
!H sys1 sys2 pcond pcond_f s.
  (symb_symbst_pcond sys1 = pcond) ==>
  (sys2 = symb_symbst_pcond_update pcond_f sys1) ==>

  (((sr.sr_symbols_f pcond) UNION
    (sr.sr_symbols_f (pcond_f pcond))) SUBSET (symb_interpr_dom H)) ==>

  (sr.sr_interpret_f H pcond =
   sr.sr_interpret_f H (pcond_f pcond)) ==>

  ((symb_matchstate sr sys1 H s) =
   (symb_matchstate sr sys2 H s))
``,
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [symb_matchstate_def] >>

  EQ_TAC >> (
    FULL_SIMP_TAC std_ss [symb_symbst_pcond_update_UNCHANGED_thm] >>
    REPEAT STRIP_TAC >> (
      FULL_SIMP_TAC std_ss [symb_suitable_interpretation_def, symb_interpr_for_symbs_def] >>
      METIS_TAC
       [symb_symbst_pcond_update_IMP_EQ_thm, SUBSET_TRANS, UNION_SUBSET,
        symb_symbols_of_symb_symbst_pcond_update_SUBSET1_thm,
        symb_symbols_of_symb_symbst_pcond_update_SUBSET2_thm,
        symb_symbst_store_IMP_EQ_thm, symb_symbst_pcond_update_UNCHANGED_thm]
    )
  )
);


(* matching gives a UNIQUE store *)
val symb_matchstate_UNIQUE_store_thm = store_thm(
   "symb_matchstate_UNIQUE_store_thm", ``
!sr.
!sys H s s'.
  (symb_matchstate sr sys H s) ==>
  (symb_matchstate sr sys H s') ==>

  (symb_concst_store s = symb_concst_store s')
``,
  REPEAT GEN_TAC >>
  Cases_on `sys` >> Cases_on `s` >> Cases_on `s'` >>
  FULL_SIMP_TAC (std_ss++symb_TYPES_ss)
    [symb_matchstate_def,
     symb_interpr_symbstore_def, symb_concst_store_def, symb_symbst_store_def] >>
  REPEAT STRIP_TAC >>

  HO_MATCH_MP_TAC EQ_EXT >> STRIP_TAC >>
  (* show that the concrete store functions are equivalent for all x *)

  REPEAT (PAT_X_ASSUM ``!var. A`` (ASSUME_TAC o (Q.SPEC `x`))) >>

  Cases_on `f x` >> Cases_on `f' x` >> Cases_on `f'' x` >> (
    FULL_SIMP_TAC std_ss []
  )
);

(* matching is unique *)
val symb_matchstate_UNIQUE_thm = store_thm(
   "symb_matchstate_UNIQUE_thm", ``
!sr.
!sys H s s'.
  (symb_matchstate sr sys H s) ==>
  (symb_matchstate sr sys H s') ==>

  (s = s')
``,
  REPEAT GEN_TAC >>
  Cases_on `s` >> Cases_on `s'` >>
  FULL_SIMP_TAC (std_ss++symb_TYPES_ss) [] >>

  REPEAT STRIP_TAC >- (
    (* first take care of the pc *)
    FULL_SIMP_TAC (std_ss++symb_TYPES_ss)
      [symb_matchstate_def, symb_concst_pc_def, symb_symbst_pc_def]
  ) >>

  (* and now the concrete store *)
  METIS_TAC [symb_concst_store_def, symb_matchstate_UNIQUE_store_thm]
);

(* matching implies matching the restricted interpretation *)
val symb_matchstate_TO_min_RESTR_thm = store_thm(
   "symb_matchstate_TO_min_RESTR_thm", ``
!sr.
!H sys s.
  (symb_symbols_f_sound sr) ==>

  (symb_matchstate sr sys H  s) ==>

  (symb_matchstate sr sys (symb_interpr_restr (symb_symbols sr sys) H) s)
``,
  METIS_TAC [symb_interpr_restr_IS_eq_for_thm, symb_interprs_eq_for_matchstate_IMP_matchstate_thm]
);

(* matching implies matching a minimal interpretation *)
val symb_matchstate_TO_minimal_thm = store_thm(
   "symb_matchstate_TO_minimal_thm", ``
!sr.
!sys H s.
  (symb_symbols_f_sound sr) ==>

  (symb_matchstate sr sys H s) ==>

  (?H'. (symb_interpr_ext H H')/\
        (symb_minimal_interpretation sr sys H') /\
        (symb_matchstate sr sys H' s)
  )
``,
  METIS_TAC [symb_minimal_interpretation_def, symb_matchstate_TO_min_RESTR_thm,
    symb_interpr_for_symbs_TO_min_thm, symb_matchstate_def, symb_suitable_interpretation_def]
);

val symb_interpr_ext_matchstate_IMP_matchstate_thm = store_thm(
   "symb_interpr_ext_matchstate_IMP_matchstate_thm", ``
!sr.
!sys H1 H2 s.
  (symb_symbols_f_sound sr) ==>

  (symb_interpr_ext H2 H1) ==>
  (symb_matchstate sr sys H1 s) ==>
  (symb_matchstate sr sys H2 s)
``,
  REPEAT STRIP_TAC >>

  `symb_interprs_eq_for H1 H2 (symb_symbols sr sys)` by (
    FULL_SIMP_TAC std_ss [symb_matchstate_def, symb_suitable_interpretation_SUBSET_dom_thm] >>
    METIS_TAC [symb_interpr_ext_IMP_eq_for_thm]
  ) >>

  METIS_TAC [symb_interprs_eq_for_matchstate_IMP_matchstate_thm]
);


val symb_interpr_extend_IMP_symb_matchstate_thm = store_thm(
   "symb_interpr_extend_IMP_symb_matchstate_thm", ``
!sr.
!sys H_extra H_base s.
  (symb_symbols_f_sound sr) ==>

  (symb_matchstate sr sys H_base s) ==>
  (symb_matchstate sr sys (symb_interpr_extend H_extra H_base) s)
``,
  METIS_TAC [symb_interpr_extend_IMP_ext_thm, symb_interpr_ext_matchstate_IMP_matchstate_thm]
);


val symb_matchstate_ext_def = Define `
  symb_matchstate_ext sr sys H s =
    (?H'. symb_interpr_ext H' H /\
          symb_matchstate sr sys H' s)
`;

val symb_matchstate_ext_w_ext_thm = store_thm(
   "symb_matchstate_ext_w_ext_thm", ``
!sr.
!H H' sys s.
  (symb_interpr_ext H' H) ==>

  (symb_matchstate_ext sr sys H' s) ==>
  (symb_matchstate_ext sr sys H  s)
``,
  METIS_TAC [symb_matchstate_ext_def, symb_interpr_ext_TRANS_thm]
);

(*
GOAL: SINGLE STEP SOUNDNESS
=======================================================
*)
(* this definition assumes that the concrete transition function is total,
   if it wasn't we needed more here and also needed to take special care *)
val symb_step_sound_def = Define `
  symb_step_sound sr =
    (!sys Pi.
     (sr.sr_step_symb sys = Pi) ==>
     (!s H s'.
       (symb_matchstate sr sys H s) ==>
       (sr.sr_step_conc s = s') ==>
       (?sys'. sys' IN Pi /\ symb_matchstate sr sys' H s')
     )
    )
`;



(*
NOTATION: MULTISTEP WITH LABEL SET
=======================================================
*)

(* n steps deterministic transition relation with using FUNPOW *)
val step_n_def = Define `
  (step_n stepf s n s' = (FUNPOW stepf n s = s'))
`;

val step_n_deterministic_thm = store_thm("step_n_deterministic_thm", ``
!stepf.
!s n s' s''.
(step_n stepf s n s') ==>
(step_n stepf s n s'') ==>
(s' = s'')
``,
  SIMP_TAC std_ss [step_n_def]
);
val step_n_total_thm = store_thm("step_n_total_thm", ``
!stepf.
!s n.
?s'.
step_n stepf s n s'
``,
  SIMP_TAC std_ss [step_n_def]
);

val step_n_in_L_relaxed_def = Define `
  step_n_in_L_relaxed pcf stepf s n L s' =
    (step_n stepf s n s' /\
     (n > 0) /\
     (!n'. 0 < n' ==> n' < n ==>
        ?s''. step_n stepf s n' s'' /\ pcf(s'') IN L))
`;

val step_n_in_L_def = Define `
  step_n_in_L pcf stepf s n L s' =
    ((pcf s) IN L /\
     (step_n_in_L_relaxed pcf stepf s n L s'))
`;

val step_n_in_L_thm = save_thm("step_n_in_L_thm",
  REWRITE_RULE [step_n_in_L_relaxed_def] step_n_in_L_def
);

val step_n_in_L_onlyL_thm = store_thm("step_n_in_L_onlyL_thm", ``
!pcf stepf.
!s n L s'.
(step_n_in_L pcf stepf s n L s') ==>
(
  (* ((pcf s) IN L) /\ *)
  (!n' s''. n' < n ==> step_n stepf s n' s'' ==> pcf(s'') IN L)
)
``,
  SIMP_TAC std_ss [step_n_in_L_thm] >>
  REPEAT STRIP_TAC >>
  Cases_on `n'` >- (
    FULL_SIMP_TAC std_ss [step_n_def, FUNPOW]
  ) >>
  `0 < SUC n''` by (SIMP_TAC arith_ss []) >>
  METIS_TAC [step_n_deterministic_thm]
);

val step_n_in_L_IMP_SUPER_thm = store_thm("step_n_in_L_IMP_SUPER_thm", ``
!pcf stepf.
!s n L L' s'.
  (L SUBSET L') ==>
  (step_n_in_L pcf stepf s n L  s') ==>
  (step_n_in_L pcf stepf s n L' s')
``,
  REWRITE_TAC [step_n_in_L_thm, SUBSET_DEF] >>
  METIS_TAC []
);

val step_n_in_L_SEQ_thm = store_thm("step_n_in_L_SEQ_thm", ``
!pcf stepf.
!s n_A L_A s' n_B L_B s''.
  (step_n_in_L pcf stepf s  n_A L_A s') ==>
  (step_n_in_L pcf stepf s' n_B L_B s'') ==>
  (step_n_in_L pcf stepf s (n_A + n_B) (L_A UNION L_B) s'')
``,
  REWRITE_TAC [step_n_in_L_thm, step_n_def] >>
  REPEAT STRIP_TAC >> (
    ASM_SIMP_TAC (arith_ss++pred_setSimps.PRED_SET_ss) []
  ) >> (
    REWRITE_TAC [Once ADD_SYM] >>
    ASM_SIMP_TAC (arith_ss++pred_setSimps.PRED_SET_ss) [step_n_def, FUNPOW_ADD]
  ) >>

  Cases_on `n' < n_A` >- (
    METIS_TAC []
  ) >>

  (* n' = n_A + some difference *)
  `?diff. n' = diff + n_A` by (
    METIS_TAC [LESS_EQ_EXISTS, NOT_LESS, ADD_SYM]
  ) >>

  (* that difference < n_B *)
  `diff < n_B` by (
    ASM_SIMP_TAC (arith_ss) []
  ) >>

  (* with that, just solve with assumptions and FUNPOW_ADD *)
  Cases_on `diff = 0` >> (
    FULL_SIMP_TAC (arith_ss) [FUNPOW_ADD, FUNPOW_0]
  )
);

val conc_step_n_in_L_relaxed_def = Define `
  conc_step_n_in_L_relaxed sr = step_n_in_L_relaxed symb_concst_pc sr.sr_step_conc
`;

val conc_step_n_in_L_def = Define `
  conc_step_n_in_L sr = step_n_in_L symb_concst_pc sr.sr_step_conc
`;

val conc_step_n_in_L_IMP_relaxed_thm = store_thm("conc_step_n_in_L_IMP_relaxed_thm", ``
!sr.
!s n L s'.
(conc_step_n_in_L sr s n L s') ==>
(conc_step_n_in_L_relaxed sr s n L s')
``,
  METIS_TAC [conc_step_n_in_L_def, conc_step_n_in_L_relaxed_def, step_n_in_L_def]
);



(*
GOAL: MULTISTEP SOUNDNESS
=======================================================
*)
val symb_hl_step_in_L_sound_def = Define `
  symb_hl_step_in_L_sound sr (sys, L, Pi) =
    !s H.
    (symb_minimal_interpretation sr sys H) ==>
    (symb_matchstate sr sys H s) ==>
    (?n s'.
      (conc_step_n_in_L sr s n L s') /\
      (?sys'. sys' IN Pi /\ symb_matchstate_ext sr sys' H s')
    )
`;

(* TODO: for rules use DELETE (..) instead of DIFF {..} *)

(*
(*
WIP: SANITY: MULTISTEP SOUNDNESS IMPLIES INCLUSION OF ALL STARTING STATES IN REACHABLE STATE PATH CONDITIONS
=======================================================
*)
(* something similar could be proven for the transformations of Pi with the rules,
   i.e. path conditions in the reachable states as a whole can only get less restrictive and never more restrictive *)
(* no underapproximation *)
val symb_hl_step_in_L_sound_IMP_overapprox_thm = store_thm(
   "symb_hl_step_in_L_sound_IMP_overapprox_thm", ``
!sr.
!sys L Pi.
  (symb_hl_step_in_L_sound sr (sys, L, Pi)) ==>
  (!s H.
     (symb_interpr_symbpcond sr H sys) ==>
     (?sys'. sys' IN Pi /\ )
symb_interpr_ext H' H
  )
``,
  cheat
);
*)


(*
GOAL: INFERENCE RULES
=======================================================
*)
val symb_rule_STEP_thm = store_thm("symb_rule_STEP_thm", ``
!sr.
!sys L Pi.
  (symb_step_sound sr) ==>
  (sr.sr_step_symb sys = Pi) ==>
  ((symb_symbst_pc sys) IN L) ==>
  (symb_hl_step_in_L_sound sr (sys, L, Pi))
``,
  REWRITE_TAC [symb_step_sound_def, symb_matchstate_ext_def, symb_hl_step_in_L_sound_def, conc_step_n_in_L_def, step_n_in_L_thm] >>
  REPEAT STRIP_TAC >>

  Q.EXISTS_TAC `SUC 0` >>
  Q.EXISTS_TAC `sr.sr_step_conc s` >>

  SIMP_TAC arith_ss [step_n_def, FUNPOW] >>
  METIS_TAC [symb_interpr_ext_id_thm, symb_matchstate_def]
);


(* TODO: this should go to auxTheory *)
val SUBSET_of_DIFF_thm = store_thm("SUBSET_of_DIFF_thm",
  ``!s t v.
    s SUBSET t ==>
    ((s DIFF v) SUBSET (t DIFF v))
``,
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [SUBSET_DEF]
);



val symb_interprs_eq_for_INTER_doms_thm = store_thm(
   "symb_interprs_eq_for_INTER_doms_thm", ``
!sr.
!H1 H12 H2 H23 H3.
  (symb_symbols_f_sound sr) ==>

  ((symb_interpr_dom H1) INTER ((symb_interpr_dom H3) DIFF (symb_interpr_dom H2)) = EMPTY) ==>

  (symb_interpr_ext H12 H1) ==>
  (symb_interpr_ext H12 H2) ==>

  (symb_interpr_ext H23 H2) ==>
  (symb_interpr_ext H23 H3) ==>

  (symb_interprs_eq_for_INTER H1 H3)
``,
  METIS_TAC [symb_interpr_ext_IMP_interprs_eq_for_INTER_thm, symb_interprs_eq_for_INTER_TRANS_thm]
);

val symb_matchstate_interpr_ext_EXISTS_thm = store_thm(
   "symb_matchstate_interpr_ext_EXISTS_thm", ``
!sr.
!H1 H12 H2 H23 H3 sys s.
  (symb_symbols_f_sound sr) ==>

  ((symb_interpr_dom H1) INTER ((symb_interpr_dom H3) DIFF (symb_interpr_dom H2)) = EMPTY) ==>

  (symb_interpr_ext H12 H1) ==>
  (symb_interpr_ext H12 H2) ==>

  (symb_interpr_ext H23 H2) ==>
  (symb_interpr_ext H23 H3) ==>

  (symb_matchstate sr sys H3 s) ==>

  (?H4. symb_interpr_ext H4 H1 /\ symb_matchstate sr sys H4 s)
``,
  REPEAT STRIP_TAC >>

  (* the intersection of H1 and H3 is equally mapped in both interpretations *)
  `symb_interprs_eq_for_INTER H1 H3` by (
    METIS_TAC [symb_interprs_eq_for_INTER_doms_thm]
  ) >>

  METIS_TAC [symb_interpr_extend_IMP_ext_thm2, symb_interpr_extend_IMP_symb_matchstate_thm]
);

val symb_SEQ_interpr_dom_INTER_thm = store_thm(
   "symb_SEQ_interpr_dom_INTER_thm", ``
!sr.
!sys_A sys_B Pi_B sys_Pi_B H1 H2 H3 sys s.
  ((symb_symbols sr sys_A)
   INTER
   ((symb_symbols_set sr Pi_B) DIFF (symb_symbols sr sys_B))
   = EMPTY) ==>

  (sys_Pi_B IN Pi_B) ==>

  (symb_minimal_interpretation sr sys_A H1) ==>
  (symb_minimal_interpretation sr sys_B H2) ==>
  (symb_minimal_interpretation sr sys_Pi_B H3) ==>

  ((symb_interpr_dom H1) INTER ((symb_interpr_dom H3) DIFF (symb_interpr_dom H2)) = EMPTY)
``,
  METIS_TAC [symb_minimal_interpretation_EQ_dom_thm,
             symb_symbols_set_SUBSET_thm, bir_auxiliaryTheory.INTER_SUBSET_EMPTY_thm, SUBSET_of_DIFF_thm]
);

val symb_rule_SEQ_thm = store_thm("symb_rule_SEQ_thm", ``
!sr.
!sys_A L_A Pi_A sys_B L_B Pi_B.
  (symb_symbols_f_sound sr) ==>

  (* can't reintroduce symbols in fragment B that have been lost in A *)
  (((symb_symbols sr sys_A) (* DIFF (symb_symbols sr sys_B) *))
       INTER ((symb_symbols_set sr Pi_B) DIFF (symb_symbols sr sys_B))
   = EMPTY) ==>

  (symb_hl_step_in_L_sound sr (sys_A, L_A, Pi_A)) ==>
  (symb_hl_step_in_L_sound sr (sys_B, L_B, Pi_B)) ==>
  (symb_hl_step_in_L_sound sr (sys_A, L_A UNION L_B, (Pi_A DIFF {sys_B}) UNION Pi_B))
``,
  REWRITE_TAC [symb_hl_step_in_L_sound_def, conc_step_n_in_L_def] >>
  REPEAT STRIP_TAC >>

  PAT_X_ASSUM ``!s H. symb_minimal_interpretation sr sys_A H ==> A`` (ASSUME_TAC o (Q.SPECL [`s`, `H`])) >>
  REV_FULL_SIMP_TAC std_ss [symb_matchstate_ext_def] >>

  (* the case when after A we don't execute through sys_B *)
  Cases_on `sys' = sys_B` >| [
    ALL_TAC
  ,
    ASM_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>
    METIS_TAC [step_n_in_L_IMP_SUPER_thm, SUBSET_UNION]
  ] >>

  (* the case when after A we actually execute through sys_B *)
  ASSUME_TAC (Q.SPECL [`sr`, `sys_B`, `H'`, `s'`] symb_matchstate_TO_minimal_thm) >>
  FULL_SIMP_TAC std_ss [] >>
  REV_FULL_SIMP_TAC std_ss [] >>

  (* execute from s' (sys') with fragment B *)
  PAT_X_ASSUM ``!s H. symb_minimal_interpretation sr sys_B H ==> A`` (ASSUME_TAC o (Q.SPECL [`s'`, `H''`])) >>
  FULL_SIMP_TAC std_ss [] >>
  REV_FULL_SIMP_TAC std_ss [] >>

  (* the sequential complete composition to the state after executing in B *)
  Q.EXISTS_TAC `n+n'` >> Q.EXISTS_TAC `s''` >>
  STRIP_TAC >- (
    METIS_TAC [step_n_in_L_SEQ_thm]
  ) >>

  (* establish the properties for the reached state *)
  Q.EXISTS_TAC `sys''` >>
  ASM_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>

  (* construct the interpretation where all lost symbols in A are
     mapped as initially and prove it to extend the initial interpretation *)
  rename1 `symb_matchstate sr sys'' H_f s''` >>

  (* first, make H_f minimal w.r.t. sys'' *)
  ASSUME_TAC (Q.SPECL [`sr`, `sys''`, `H_f`, `s''`] symb_matchstate_TO_minimal_thm) >>
  FULL_SIMP_TAC std_ss [] >>
  REV_FULL_SIMP_TAC std_ss [] >>
  rename1 `symb_minimal_interpretation sr sys_B H_i` >>
  rename1 `symb_minimal_interpretation sr sys'' H_e` >>

  (* we can conlude that this intersection is empty *)
  `(symb_interpr_dom H) INTER ((symb_interpr_dom H_e) DIFF (symb_interpr_dom H_i)) = EMPTY` by (
    METIS_TAC [symb_SEQ_interpr_dom_INTER_thm]
  ) >>

  (* we can construct an interpretation that both matches this symbolic state
     with the concrete final state and is an extension of the initial interpretation *)
  METIS_TAC [symb_matchstate_interpr_ext_EXISTS_thm]
);

val symb_rule_INF_thm = store_thm("symb_rule_INF_thm", ``
!sr.
!sys L Pi sys'.
  (symb_hl_step_in_L_sound sr (sys, L, Pi)) ==>
  (!H. ~(symb_interpr_symbpcond sr H sys')) ==>
  (symb_hl_step_in_L_sound sr (sys, L, Pi DIFF {sys'}))
``,
  REWRITE_TAC [symb_hl_step_in_L_sound_def] >>
  REPEAT STRIP_TAC >>

  PAT_X_ASSUM ``!s H. symb_minimal_interpretation sr sys H ==> A`` (ASSUME_TAC o (Q.SPECL [`s`, `H`])) >>
  REV_FULL_SIMP_TAC std_ss [symb_matchstate_def, symb_matchstate_ext_def] >>

  SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>
  Cases_on `sys' = sys''` >> (
    METIS_TAC []
  )
);

val symb_pcondwiden_def = Define `
  symb_pcondwiden sr sys sys' = (
    (symb_symbst_pc sys =
     symb_symbst_pc sys') /\
    (symb_symbst_store sys =
     symb_symbst_store sys') /\
    (!H.
      (symb_interpr_for_symbs ((sr.sr_symbols_f (symb_symbst_pcond sys)) UNION (sr.sr_symbols_f (symb_symbst_pcond sys'))) H) ==>
      (symb_interpr_symbpcond sr H sys) ==>
      (symb_interpr_symbpcond sr H sys'))
  )
`;

val symb_pcondwiden_matchstate_IMP_matchstate_thm = store_thm(
   "symb_pcondwiden_matchstate_IMP_matchstate_thm", ``
!sr.
!sys sys' H s.
  (symb_symbols_f_sound sr) ==>

  (symb_pcondwiden sr sys sys') ==>
  (symb_matchstate sr sys H s) ==>

  (symb_matchstate sr sys' (symb_interpr_extend_symbs (symb_symbols sr sys') H) s)
``,
  REPEAT STRIP_TAC >>
  Q.ABBREV_TAC `H' = (symb_interpr_extend_symbs (symb_symbols sr sys') H)` >>

  `symb_matchstate sr sys H' s` by (
    METIS_TAC [symb_interpr_ext_matchstate_IMP_matchstate_thm, symb_interpr_extend_symbs_IMP_ext_thm]
  ) >>

  `symb_interpr_for_symbs
     ((symb_symbols sr sys ) UNION
      (symb_symbols sr sys')) H'` by (
    METIS_TAC
      ( [symb_interpr_extend_symbs_IMP_for_symbs_thm,
         symb_suitable_interpretation_SUBSET_dom_thm, symb_matchstate_def]
       @[symb_interpr_for_symbs_def, SUBSET_TRANS, UNION_SUBSET, SUBSET_UNION])
  ) >>

  `symb_interpr_for_symbs ((sr.sr_symbols_f (symb_symbst_pcond sys)) UNION (sr.sr_symbols_f (symb_symbst_pcond sys'))) H'` by (
    METIS_TAC
      [symb_interpr_for_symbs_def, symb_symbols_SUBSET_pcond_thm, SUBSET_TRANS, UNION_SUBSET, SUBSET_UNION]
  ) >>

  `symb_suitable_interpretation sr sys' H'` by (
    METIS_TAC [symb_suitable_interpretation_def, symb_interpr_for_symbs_def, SUBSET_TRANS, SUBSET_UNION]
  ) >>

  FULL_SIMP_TAC std_ss [symb_pcondwiden_def, symb_matchstate_def] >>

  METIS_TAC [symb_symbst_store_IMP_EQ_thm]
);

val symb_pcondwiden_matchstate_IMP_matchstate_EXISTS_thm = store_thm(
   "symb_pcondwiden_matchstate_IMP_matchstate_EXISTS_thm", ``
!sr.
!sys1 sys2 s H1 H2.
  (symb_symbols_f_sound sr) ==>

  (symb_pcondwiden sr sys1 sys2) ==>

  (symb_matchstate sr sys1 H1 s) ==>
  (?H2.
    (symb_interpr_ext H2 H1) /\
    (symb_matchstate sr sys2 H2 s))
``,
  REPEAT STRIP_TAC >>
  Q.EXISTS_TAC `symb_interpr_extend_symbs (symb_symbols sr sys2) H1` >>

  FULL_SIMP_TAC std_ss [symb_interpr_extend_symbs_IMP_ext_thm] >>

  METIS_TAC [symb_pcondwiden_matchstate_IMP_matchstate_thm]
);

val symb_rule_CONS_S_thm = store_thm("symb_rule_CONS_S_thm", ``
!sr.
!sys' sys L Pi.
  (symb_symbols_f_sound sr) ==>

  (* can't reintroduce symbols in fragment that have been lost in the path condition widening *)
  (((symb_symbols sr sys) (*  DIFF (symb_symbols sr sys') *))
   INTER ((symb_symbols_set sr Pi) DIFF (symb_symbols sr sys')) = EMPTY) ==>

  (symb_hl_step_in_L_sound sr (sys', L, Pi)) ==>
  (symb_pcondwiden sr sys sys') ==>
  (symb_hl_step_in_L_sound sr (sys, L, Pi))
``,
  REWRITE_TAC [symb_hl_step_in_L_sound_def] >>
  REPEAT STRIP_TAC >>
  rename1 `symb_minimal_interpretation sr sys H1` >>

  (* extend H to include arbitrary mappings for everything missing w.r.t. sys',
       this is like the other rule CONS_E *)
  (* Q.ABBREV_TAC `H_a = symb_interpr_extend_symbs (symb_symbols sr sys') H1` >> *)
  (* this can now match sys' with s *)
  IMP_RES_TAC symb_pcondwiden_matchstate_IMP_matchstate_EXISTS_thm >>
  rename1 `symb_matchstate sr sys' H_a s` >>

  (* then get a minimal interpretation for sys' *)
  ASSUME_TAC (Q.SPECL [`sr`, `sys'`, `H_a`, `s`] symb_matchstate_TO_minimal_thm) >>
  FULL_SIMP_TAC std_ss [] >>
  REV_FULL_SIMP_TAC std_ss [] >>
  rename1 `symb_minimal_interpretation sr sys' H2` >>

  (* then execute *)
  PAT_X_ASSUM ``!x. A`` (ASSUME_TAC o (Q.SPECL [`s`, `H2`])) >>
  REV_FULL_SIMP_TAC std_ss [symb_matchstate_ext_def] >>

  Q.EXISTS_TAC `n` >> Q.EXISTS_TAC `s'` >>
  STRIP_TAC >- (
    METIS_TAC [step_n_in_L_SEQ_thm]
  ) >>
  rename1 `symb_matchstate sr sys'' H_b s'` >>

  (* establish the properties for the reached state *)
  Q.EXISTS_TAC `sys''` >>
  ASM_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>

  (* must make H_b minimal w.r.t. sys'' *)
  ASSUME_TAC (Q.SPECL [`sr`, `sys''`, `H_b`, `s'`] symb_matchstate_TO_minimal_thm) >>
  FULL_SIMP_TAC std_ss [] >>
  REV_FULL_SIMP_TAC std_ss [] >>
  rename1 `symb_minimal_interpretation sr sys'' H3` >>

  (* extend the interpretation with mappings from the original H
       to get an extension from H that can match the state,
       this is like in the sequential composition proof *)
  (* finally relate the final interpretation back to the initial state *)
  `(symb_interpr_dom H1) INTER ((symb_interpr_dom H3) DIFF (symb_interpr_dom H2)) = EMPTY` by (
    METIS_TAC [symb_SEQ_interpr_dom_INTER_thm]
  ) >>
  METIS_TAC [symb_matchstate_interpr_ext_EXISTS_thm]
);

val symb_rule_CONS_E_thm = store_thm("symb_rule_CONS_E_thm", ``
!sr.
!sys L Pi sys2 sys2'.
  (symb_symbols_f_sound sr) ==>

  (symb_hl_step_in_L_sound sr (sys, L, Pi)) ==>
  (symb_pcondwiden sr sys2 sys2') ==>
  (symb_hl_step_in_L_sound sr (sys, L, (Pi DIFF {sys2}) UNION {sys2'}))
``,
  REWRITE_TAC [symb_hl_step_in_L_sound_def] >>
  REPEAT STRIP_TAC >>

  PAT_X_ASSUM ``!s H. symb_minimal_interpretation sr sys H ==> A`` (ASSUME_TAC o (Q.SPECL [`s`, `H`])) >>
  REV_FULL_SIMP_TAC std_ss [symb_matchstate_ext_def] >>

  Cases_on `sys' = sys2` >| [
    ALL_TAC
  ,
    ASM_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>
    METIS_TAC []
  ] >>

  (* the case when we would execute to sys2 *)
  Q.EXISTS_TAC `n` >> Q.EXISTS_TAC `s'` >>
  ASM_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>

  Q.EXISTS_TAC `sys2'` >>
  ASM_SIMP_TAC std_ss [] >>

  (* have to proof that we can match with an extension of H for sys' *)
  (* start with H', rename to H_m *)
  rename1 `symb_matchstate sr sys' H_m s'` >>
  Q.ABBREV_TAC `H_e = symb_interpr_extend_symbs (symb_symbols sr sys2') H_m` >>
  Q.EXISTS_TAC `H_e` >>

  (* this is an extension from H *)
  `symb_interpr_ext H_e H` by (
    METIS_TAC [symb_interpr_extend_symbs_IMP_ext_thm, symb_interpr_ext_TRANS_thm]
  ) >>
  FULL_SIMP_TAC std_ss [] >>

  METIS_TAC [symb_pcondwiden_matchstate_IMP_matchstate_thm]
);

val symb_rule_CONS_thm = store_thm("symb_rule_CONS_thm", ``
!sr.
!sys1' sys1 L Pi sys2 sys2'.
  (symb_symbols_f_sound sr) ==>

  (* can't reintroduce symbols in fragment that have been lost in the path condition widening *)
  (((symb_symbols sr sys1) (*  DIFF (symb_symbols sr sys') *))
   INTER ((symb_symbols_set sr ((Pi DIFF {sys2}) UNION {sys2'})) DIFF (symb_symbols sr sys1')) = EMPTY) ==>

  (symb_hl_step_in_L_sound sr (sys1', L, Pi)) ==>
  (symb_pcondwiden sr sys1 sys1') ==>
  (symb_pcondwiden sr sys2 sys2') ==>
  (symb_hl_step_in_L_sound sr (sys1, L, (Pi DIFF {sys2}) UNION {sys2'}))
``,
  METIS_TAC [symb_rule_CONS_S_thm, symb_rule_CONS_E_thm]
);

(*
      sr_subst_f         : ('d_symbol # 'e_symbexpr) -> 'e_symbexpr -> 'e_symbexpr;
*)

(* construct symbolic expression with semantics of
     conjuncting an expression with an equality of two other expressions
   e.g.: e1 = (v), e2 = (5), conj1 = (x > 10)
     then: (v) = (5) /\ (x > 10) *)
val symb_mk_exp_eq_f_sound_def = Define `
    symb_mk_exp_eq_f_sound sr =
      ((!e1 e2. !H.
         (sr.sr_interpret_f H (sr.sr_mk_exp_eq_f e1 e2) = SOME sr.sr_val_true) =
         ((sr.sr_interpret_f H e1 <> NONE) /\
          (sr.sr_interpret_f H e1 =
           sr.sr_interpret_f H e2))) /\
       (!e1 e2. sr.sr_symbols_f (sr.sr_mk_exp_eq_f e1 e2) =
         sr.sr_symbols_f e1 UNION sr.sr_symbols_f e2))
`;
val symb_mk_exp_conj_f_sound_def = Define `
    symb_mk_exp_conj_f_sound sr =
      ((!e1 e2. !H.
         (sr.sr_interpret_f H (sr.sr_mk_exp_conj_f e1 e2) = SOME sr.sr_val_true) =
         ((sr.sr_interpret_f H e1 = SOME sr.sr_val_true) /\
          (sr.sr_interpret_f H e2 = SOME sr.sr_val_true))) /\
       (!e1 e2. sr.sr_symbols_f (sr.sr_mk_exp_conj_f e1 e2) =
         sr.sr_symbols_f e1 UNION sr.sr_symbols_f e2))
`;
val symb_expr_conj_eq_def = Define `
    symb_expr_conj_eq sr e1 e2 conj1 =
      sr.sr_mk_exp_conj_f (sr.sr_mk_exp_eq_f e1 e2) conj1
`;
val symb_expr_conj_eq_thm = store_thm(
   "symb_expr_conj_eq_thm", ``
!sr.
  (symb_mk_exp_eq_f_sound sr) ==>
  (symb_mk_exp_conj_f_sound sr) ==>
    ((!e1 e2 conj1. !H.
       (sr.sr_interpret_f H (symb_expr_conj_eq sr e1 e2 conj1) = SOME sr.sr_val_true) =
       ((sr.sr_interpret_f H conj1 = SOME sr.sr_val_true) /\
        (sr.sr_interpret_f H e1 <> NONE) /\
        (sr.sr_interpret_f H e1 =
         sr.sr_interpret_f H e2))) /\
     (!e1 e2 conj1.sr.sr_symbols_f (symb_expr_conj_eq sr e1 e2 conj1) =
         sr.sr_symbols_f e1 UNION
         sr.sr_symbols_f e2 UNION
         sr.sr_symbols_f conj1))
``,
  METIS_TAC [symb_expr_conj_eq_def, symb_mk_exp_eq_f_sound_def, symb_mk_exp_conj_f_sound_def]
);

(* predicate for functions that make expressions that represent exactly a symbol *)
val symb_mk_exp_symb_f_sound_def = Define `
    symb_mk_exp_symb_f_sound sr =
      ((!H symb v.
         (symb_interpr_get H symb = SOME v) ==>
         (sr.sr_interpret_f H (sr.sr_mk_exp_symb_f symb) = SOME v)) /\
       (!symb. sr.sr_symbols_f (sr.sr_mk_exp_symb_f symb) = {symb}))
`;

val symb_matchstate_IMP_interpret_exp_SOME_thm = store_thm(
   "symb_matchstate_IMP_interpret_exp_SOME_thm", ``
!sr.
!sys var symbexp H s.
  (symb_symbst_store sys var = SOME symbexp) ==>

  (symb_matchstate sr sys H s) ==>

  (?v. sr.sr_interpret_f H symbexp = SOME v)
``,
  REPEAT STRIP_TAC >>
  Cases_on `sys` >>
  FULL_SIMP_TAC std_ss [symb_symbst_store_def, symb_matchstate_def, symb_interpr_symbstore_def] >>

  PAT_X_ASSUM ``!x. A`` (ASSUME_TAC o (Q.SPECL [`var`])) >>
  FULL_SIMP_TAC std_ss [] >>
  REV_FULL_SIMP_TAC std_ss []
);

val symb_matchstate_ext_IMP_SAME_interpret_exp_thm = store_thm(
   "symb_matchstate_ext_IMP_SAME_interpret_exp_thm", ``
!sr.
!sys var symbexp H H' s v.
  (symb_symbst_store sys var = SOME symbexp) ==>

  (symb_interpr_ext H' H) ==>
  (symb_matchstate sr sys H  s) ==>
  (symb_matchstate sr sys H' s) ==>

  (sr.sr_interpret_f H  symbexp =
   sr.sr_interpret_f H' symbexp)
``,
  REPEAT STRIP_TAC >>
  Cases_on `sys` >>
  FULL_SIMP_TAC std_ss [symb_symbst_store_def, symb_matchstate_def, symb_interpr_symbstore_def] >>

  REPEAT (PAT_X_ASSUM ``!x. A`` (ASSUME_TAC o (Q.SPECL [`var`]))) >>
  FULL_SIMP_TAC std_ss [] >>
  REV_FULL_SIMP_TAC std_ss [] >>

  FULL_SIMP_TAC std_ss []
);

val symb_FRESH_matchstate_IMP_matchstate_ext_thm = store_thm(
   "symb_FRESH_matchstate_IMP_matchstate_ext_thm", ``
!sr.
(symb_symbols_f_sound sr) ==>
(symb_mk_exp_conj_f_sound sr) ==>
(symb_mk_exp_eq_f_sound sr) ==>
(symb_mk_exp_symb_f_sound sr) ==>

(!var symbexp symb sys sys' H s.
  (~(symb IN symb_interpr_dom H)) ==>
  (~(symb IN symb_symbols sr sys)) ==>

  ((symb_symbst_store sys) var = SOME symbexp) ==>
  (symb_symbst_pcond_update
     (symb_expr_conj_eq sr (sr.sr_mk_exp_symb_f symb) symbexp)
     (symb_symbst_store_update var (sr.sr_mk_exp_symb_f symb) sys)
   = sys'
  ) ==>

  (symb_matchstate sr sys  H  s) ==>
  (symb_matchstate_ext sr sys' H s)
)
``,
  REWRITE_TAC [symb_matchstate_ext_def] >>
  REPEAT STRIP_TAC >>

  Q.ABBREV_TAC `H1 = symb_interpr_update H (symb, sr.sr_interpret_f H symbexp)` >>
  Q.EXISTS_TAC `H1` >>

  `symb_interpr_ext H1 H` by (
    METIS_TAC [symb_interpr_ext_UPDATE_thm]
  ) >>
  FULL_SIMP_TAC std_ss [] >>
  `symb_matchstate sr sys H1 s` by (
    METIS_TAC [symb_interpr_ext_matchstate_IMP_matchstate_thm]
  ) >>

  `?var_v. sr.sr_interpret_f H symbexp = SOME var_v` by (
    METIS_TAC [symb_matchstate_IMP_interpret_exp_SOME_thm]
  ) >>
  `sr.sr_interpret_f H1 symbexp = SOME var_v` by (
    METIS_TAC [symb_matchstate_ext_IMP_SAME_interpret_exp_thm]
  ) >>
  FULL_SIMP_TAC std_ss [] >>

  (* now the prerequisites for the store update *)
  Q.ABBREV_TAC `symbexp' = (sr.sr_mk_exp_symb_f symb)` >>
  `sr.sr_symbols_f symbexp SUBSET symb_interpr_dom H1` by (
    METIS_TAC
      [symb_matchstate_def, symb_suitable_interpretation_def, symb_interpr_for_symbs_def,
       symb_symbols_SUBSET_store_exps_thm2, SUBSET_TRANS]
  ) >>
  `sr.sr_symbols_f symbexp' SUBSET symb_interpr_dom H1` by (
    METIS_TAC
      [symb_mk_exp_symb_f_sound_def, symb_interpr_dom_UPDATE_SOME_thm,
       INSERT_SING_UNION, SUBSET_UNION]
  ) >>

  `sr.sr_symbols_f symbexp UNION sr.sr_symbols_f (sr.sr_mk_exp_symb_f symb) SUBSET
       symb_interpr_dom H1` by (
    METIS_TAC [UNION_SUBSET]
  ) >>

  `sr.sr_interpret_f H1 symbexp = sr.sr_interpret_f H1 symbexp'` by (
    METIS_TAC
      [symb_mk_exp_symb_f_sound_def, symb_interpr_get_update_id_thm]
  ) >>

  (* now the store update *)
  Q.ABBREV_TAC `sys_i = (symb_symbst_store_update var (sr.sr_mk_exp_symb_f symb) sys)` >>
  `symb_matchstate sr sys_i H1 s` by (
    METIS_TAC [symb_symbst_store_update_IMP_matchstate_EQ_thm]
  ) >>

  (* now the prerequisites for the pcond update *)
  Q.ABBREV_TAC `pcond_f = (symb_expr_conj_eq sr symbexp' symbexp)` >>
  Q.ABBREV_TAC `pcond = symb_symbst_pcond sys_i` >>
  `sr.sr_symbols_f pcond SUBSET symb_interpr_dom H1` by (
    METIS_TAC
      [symb_matchstate_def, symb_suitable_interpretation_def, symb_interpr_for_symbs_def,
       symb_symbols_SUBSET_pcond_thm, SUBSET_TRANS]
  ) >>

  `sr.sr_symbols_f pcond UNION sr.sr_symbols_f (pcond_f pcond) SUBSET
       symb_interpr_dom H1` by (
    METIS_TAC [UNION_SUBSET, symb_expr_conj_eq_thm]
  ) >>

  `sr.sr_interpret_f H1 pcond = sr.sr_interpret_f H1 (pcond_f pcond)` by (
    `(sr.sr_interpret_f H1 pcond = SOME sr.sr_val_true)` by (
      METIS_TAC [symb_matchstate_def, symb_interpr_symbpcond_def]
    ) >>

    `sr.sr_interpret_f H1 symbexp <> NONE` by (
      FULL_SIMP_TAC std_ss [symb_expr_conj_eq_thm]
    ) >>

    METIS_TAC [symb_expr_conj_eq_thm]
  ) >>

  (* now the the final pcond update *)
  METIS_TAC [symb_symbst_pcond_update_IMP_matchstate_EQ_thm]
);


val symb_matchstate_ext_WITHOUT_thm = store_thm(
   "symb_matchstate_ext_WITHOUT_thm", ``
!sr.
!sys H s symb.
  (symb_symbols_f_sound sr) ==>

  (~(symb IN symb_interpr_dom H)) ==>
  (~(symb IN symb_symbols sr sys)) ==>

  (symb_matchstate_ext sr sys H s) ==>

  (?H'. (symb_interpr_ext H' H) /\
        (symb_matchstate sr sys H' s) /\
        (~(symb IN symb_interpr_dom H')))
``,
  REWRITE_TAC [symb_matchstate_ext_def] >>
  REPEAT STRIP_TAC >>

  Q.ABBREV_TAC `H1 = symb_interpr_update H' (symb, NONE)` >>
  Q.EXISTS_TAC `H1` >>

  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss)
    [symb_interpr_update_def, symb_interpr_dom_def, APPLY_UPDATE_THM] >>

  `symb_interprs_eq_for H1 H' (symb_interpr_dom H)` by (
    `symb_interpr_dom H SUBSET (symb_interpr_dom H' DELETE symb)` by (
      METIS_TAC
        [symb_interpr_ext_IMP_dom_thm, SUBSET_DELETE]
    ) >>
    METIS_TAC [symb_interpr_eq_for_UPDATE_dom_thm, symb_interprs_eq_for_SUBSET_thm]
  ) >>

  `symb_interprs_eq_for H' H1 (symb_symbols sr sys)` by (
    `symb_symbols sr sys SUBSET (symb_interpr_dom H' DELETE symb)` by (
      METIS_TAC
        [symb_matchstate_def, symb_suitable_interpretation_def,
         symb_interpr_for_symbs_def, SUBSET_DELETE]
    ) >>

  METIS_TAC
    [symb_interpr_eq_for_UPDATE_dom_thm,
     symb_interprs_eq_for_SUBSET_thm, symb_interprs_eq_for_COMM_thm]
  ) >>

  METIS_TAC
    ( [symb_interpr_ext_def, symb_interprs_eq_for_TRANS_thm]
     @[symb_interprs_eq_for_matchstate_IMP_matchstate_thm]
     @[symb_interpr_dom_UPDATE_NONE_thm, ELT_IN_DELETE])
);

(* rule to introduce fresh symbols as values of store variables
     (as abbreviations or as first step of forgetting values) *)
val symb_rule_FRESH_thm = store_thm("symb_rule_FRESH_thm", ``
!sr.
(symb_symbols_f_sound sr) ==>
(symb_mk_exp_eq_f_sound sr) ==>
(symb_mk_exp_conj_f_sound sr) ==>
(symb_mk_exp_symb_f_sound sr) ==>

(!sys L Pi sys2 sys2' var symbexp symb.
  (~(symb IN symb_symbols sr sys )) ==>
  (~(symb IN symb_symbols sr sys2)) ==>

  (symb_hl_step_in_L_sound sr (sys, L, Pi)) ==>
  ((symb_symbst_store sys2) var = SOME symbexp) ==>
  (symb_symbst_pcond_update
     (symb_expr_conj_eq sr (sr.sr_mk_exp_symb_f symb) symbexp)
     (symb_symbst_store_update var (sr.sr_mk_exp_symb_f symb) sys2)
   = sys2'
  ) ==>
  (symb_hl_step_in_L_sound sr (sys, L, (Pi DIFF {sys2}) UNION {sys2'}))
)
``,
  REWRITE_TAC [symb_hl_step_in_L_sound_def] >>
  REPEAT STRIP_TAC >>

  PAT_X_ASSUM ``!x. A`` (ASSUME_TAC o (Q.SPECL [`s`, `H`])) >>
  REV_FULL_SIMP_TAC std_ss [] >>

  REWRITE_TAC [symb_matchstate_ext_def] >>

  Cases_on `sys' = sys2` >| [
    ALL_TAC
  ,
    ASM_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>
    METIS_TAC [symb_matchstate_ext_def]
  ] >>

  (* the case when we would execute to sys2 *)
  Q.EXISTS_TAC `n` >> Q.EXISTS_TAC `s'` >>
  ASM_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>

  Q.EXISTS_TAC `sys2'` >>
  ASM_SIMP_TAC std_ss [] >>

  ASSUME_TAC (Q.SPECL [`sr`, `sys2`, `H`, `s'`, `symb`] symb_matchstate_ext_WITHOUT_thm) >>
  FULL_SIMP_TAC std_ss [symb_minimal_interpretation_def, symb_interpr_for_symbs_min_def] >>
  REV_FULL_SIMP_TAC std_ss [] >>

  METIS_TAC
   [symb_FRESH_matchstate_IMP_matchstate_ext_thm,
    symb_matchstate_ext_def, symb_interpr_ext_TRANS_thm,
    symb_FRESH_matchstate_IMP_matchstate_ext_thm,
    symb_matchstate_ext_def]
);


val symb_simplification_def = Define `
  symb_simplification sr sys symbexp symbexp' =
    (* (((sr.sr_symbols_f symbexp') SUBSET (sr.sr_symbols_f symbexp)) /\ *)
    (!H.
     (symb_interpr_for_symbs ((sr.sr_symbols_f (symb_symbst_pcond sys)) UNION
                              (sr.sr_symbols_f symbexp) UNION
                              (sr.sr_symbols_f symbexp')) H) ==>

     (symb_interpr_symbpcond sr H sys) ==>
     (sr.sr_interpret_f H symbexp = sr.sr_interpret_f H symbexp')
    )
`;

val symb_simplification_matchstate_IMP_matchstate_thm = store_thm(
   "symb_simplification_matchstate_IMP_matchstate_thm", ``
!sr.
!var symbexp symbexp' sys sys' H H' s.
  (symb_symbols_f_sound sr) ==>

  ((symb_symbst_store sys) var = SOME symbexp) ==>
  (symb_simplification sr sys symbexp symbexp') ==>
  (symb_symbst_store_update var symbexp' sys = sys') ==>

  (symb_matchstate sr sys H s) ==>

  ((symb_interpr_extend_symbs (symb_symbols sr sys') H) = H') ==>

  (symb_matchstate sr sys' H' s)
``,
  REPEAT STRIP_TAC >>

  `symb_matchstate sr sys H' s` by (
    METIS_TAC [symb_interpr_ext_matchstate_IMP_matchstate_thm, symb_interpr_extend_symbs_IMP_ext_thm]
  ) >>

  `symb_interpr_for_symbs
     ((symb_symbols sr sys ) UNION
      (symb_symbols sr sys')) H'` by (
    METIS_TAC
      ( [symb_interpr_extend_symbs_IMP_for_symbs_thm,
         symb_suitable_interpretation_SUBSET_dom_thm, symb_matchstate_def]
       @[symb_interpr_for_symbs_def, SUBSET_TRANS, UNION_SUBSET, SUBSET_UNION])
  ) >>

  `symb_interpr_for_symbs
              (sr.sr_symbols_f (symb_symbst_pcond sys) UNION
               sr.sr_symbols_f symbexp UNION sr.sr_symbols_f symbexp') H'` by (
    METIS_TAC
      [symb_interpr_for_symbs_def, UNION_SUBSET, SUBSET_TRANS,
       symb_symbols_SUBSET_store_exps_thm2,
       symb_symbols_of_symb_symbst_store_update_SUBSET_store_exps_thm2,
       symb_symbols_SUBSET_pcond_thm]
  ) >>

  `sr.sr_symbols_f symbexp UNION sr.sr_symbols_f symbexp' SUBSET
       symb_interpr_dom H'` by (
    METIS_TAC [symb_interpr_for_symbs_def, SUBSET_UNION, SUBSET_TRANS, UNION_ASSOC]
  ) >>

  `symb_interpr_symbpcond sr H' sys` by (
    METIS_TAC
      [symb_matchstate_def]
  ) >>

  METIS_TAC [symb_symbst_store_update_IMP_matchstate_EQ_thm, symb_simplification_def]
);

val symb_rule_SUBST_thm = store_thm("symb_rule_SUBST_thm", ``
!sr.
!sys L Pi sys2 sys2' var symbexp symbexp'.
  (symb_symbols_f_sound sr) ==>

  (symb_hl_step_in_L_sound sr (sys, L, Pi)) ==>
  ((symb_symbst_store sys2) var = SOME symbexp) ==>
  (symb_simplification sr sys2 symbexp symbexp') ==>
  (sys2' = symb_symbst_store_update var symbexp' sys2) ==>
  (symb_hl_step_in_L_sound sr (sys, L, (Pi DIFF {sys2}) UNION {sys2'}))
``,
  REWRITE_TAC [symb_hl_step_in_L_sound_def] >>
  REPEAT STRIP_TAC >>

  PAT_X_ASSUM ``!s H. symb_minimal_interpretation sr sys H ==> A`` (ASSUME_TAC o (Q.SPECL [`s`, `H`])) >>
  REV_FULL_SIMP_TAC std_ss [symb_matchstate_ext_def] >>

  Cases_on `sys' = sys2` >| [
    ALL_TAC
  ,
    ASM_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>
    METIS_TAC []
  ] >>

  (* the case when we would execute to sys2 *)
  Q.EXISTS_TAC `n` >> Q.EXISTS_TAC `s'` >>
  ASM_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>

  Q.EXISTS_TAC `sys2'` >>
  ASM_SIMP_TAC std_ss [] >>

  (* have to proof that we can match with an extension of H for sys' *)
  (* start with H', rename to H_m *)
  rename1 `symb_matchstate sr sys' H_m s'` >>
  Q.ABBREV_TAC `H_e = symb_interpr_extend_symbs (symb_symbols sr sys2') H_m` >>
  Q.EXISTS_TAC `H_e` >>

  (* this is an extension from H *)
  `symb_interpr_ext H_e H` by (
    METIS_TAC [symb_interpr_extend_symbs_IMP_ext_thm, symb_interpr_ext_TRANS_thm]
  ) >>
  FULL_SIMP_TAC std_ss [] >>

  METIS_TAC [symb_simplification_matchstate_IMP_matchstate_thm]
);


val symb_sound_subst_def = Define `
    symb_sound_subst sr substfun =
    (!symb symb_inst symbexp symbexp_r.
     (!H H' vo.
        (substfun (symb, symb_inst) symbexp = symbexp_r) ==>
        (* NOTICE: this also captures failing interpretation, i.e. type errors *)
        (sr.sr_interpret_f H symb_inst = vo) ==>
        (* just a thought: we may want/need to require vo = SOME v, but I think it's not needed *)
        ((symb_interpr_update H (symb, vo)) = H') ==>
        (sr.sr_interpret_f H' symbexp =
         sr.sr_interpret_f H  symbexp_r)) /\
     ((substfun (symb, symb_inst) symbexp = symbexp_r) ==>
      (sr.sr_symbols_f symbexp_r = ((sr.sr_symbols_f symbexp) DIFF {symb}) UNION (sr.sr_symbols_f symb_inst)))
    )
`;

(*
val symb_rule_INST_thm = store_thm("symb_rule_INST_thm", ``
!sr substfun.
  (symb_sound_subst sr substfun) ==>

!sys L Pi symb symb_inst.
  (symb_hl_step_in_L_sound sr (sys, L, Pi)) ==>
  (symb_hl_step_in_L_sound sr (substfun_st symb symb_inst sys, L, substfun_sts symb symb_inst Pi))
``,
  cheat
);
*)



(*
NOTATION: DEFINE PROPERTY TRANSFER ASSUMPTIONS AND GOAL
=======================================================
*)
val P_entails_an_interpret_def = Define `
  P_entails_an_interpret sr P sys =
    (!s.
     (symb_concst_pc s = symb_symbst_pc sys) ==>
     (P s) ==>
     (?H. symb_matchstate sr sys H s))
`;

val Pi_overapprox_Q_def = Define `
  Pi_overapprox_Q sr P sys Pi Q =
    (!sys' s s' H.
     (sys' IN Pi) ==>
     (P s) ==>
     (symb_matchstate sr sys H s) ==>
     (symb_matchstate_ext sr sys' H s') ==>
     (Q s s'))
`;

val prop_holds_def = Define `
  prop_holds sr l L P Q =
    (!s.
     (symb_concst_pc s = l) ==>
     (P s) ==>
     (?n s'.
       conc_step_n_in_L sr s n L s' /\
       Q s s'))
`;


(*
GOAL: PROPERTY TRANSFER THEOREM
=======================================================
*)
val symb_prop_transfer_thm = store_thm("symb_prop_transfer_thm", ``
!sr.
!sys L Pi P Q.
  (symb_symbols_f_sound sr) ==>
  (P_entails_an_interpret sr P sys) ==>
  (Pi_overapprox_Q sr P sys Pi Q) ==>
  (symb_hl_step_in_L_sound sr (sys, L, Pi)) ==>
  (prop_holds sr (symb_symbst_pc sys) L P Q)
``,
  REWRITE_TAC [P_entails_an_interpret_def, Pi_overapprox_Q_def, prop_holds_def, symb_hl_step_in_L_sound_def] >>
  REPEAT STRIP_TAC >>
  METIS_TAC [symb_matchstate_TO_minimal_thm]
);


(*
GOAL: PROPERTY TRANSFER COMPATIBILITY (BINARY HOARE LOGIC)
=======================================================
*)
local
  open abstract_hoare_logicTheory;
  open abstract_hoare_logicSimps;
in

(*
  it seems we can in principle produce contracts of all code fragments
  - unless the start label is in the end label set, because in this case the transition system could not "start"
  - unless it cannot be exhaustively symbolically executed, like if they contain unbound loops, or impractically largely bound loops
*)

val symb_hl_trs_def = Define `
  symb_hl_trs sr st = SOME (sr.sr_step_conc st)
`;

val symb_hl_weak_def = Define `
  symb_hl_weak sr st ls st' =
    (?n. (conc_step_n_in_L_relaxed sr st n (COMPL ls) st' /\ (~((symb_concst_pc st') IN (COMPL ls)))))
`;

val symb_hl_etl_wm_def =
  Define `symb_hl_etl_wm sr = <|
    trs  := symb_hl_trs sr;
    weak := symb_hl_weak sr;
    pc   := symb_concst_pc
  |>`;

val symb_prop_transfer_binHoare_thm = store_thm("symb_prop_transfer_binHoare_thm", ``
!sr.
!Q' l L P Q.
  (Q' = \s. \s'. Q s' /\ (~((symb_concst_pc s') IN (COMPL L)))) ==>
  (prop_holds sr l (COMPL L) P Q') ==>
  (abstract_jgmt (symb_hl_etl_wm sr) l L P Q)
``,
  REWRITE_TAC [prop_holds_def, abstract_jgmt_def] >>
  REPEAT STRIP_TAC >>

  PAT_X_ASSUM ``!x. y`` (ASSUME_TAC o (Q.SPEC `ms`)) >>

  REV_FULL_SIMP_TAC (std_ss++bir_wm_SS) [symb_hl_etl_wm_def, symb_hl_weak_def] >>

  METIS_TAC [conc_step_n_in_L_IMP_relaxed_thm]
);

(* should go to BIR auxTheory *)
val FUNPOW_OPT_SOME_thm = store_thm("FUNPOW_OPT_SOME_thm", ``
!f g.
   (!y. f y = SOME (g y)) ==>
   (!n x.
      (FUNPOW_OPT f n x = SOME (FUNPOW g n x)))
``,
  GEN_TAC >> GEN_TAC >> STRIP_TAC >>
  Induct_on `n` >- (
    REWRITE_TAC [bir_auxiliaryTheory.FUNPOW_OPT_def, FUNPOW]
  ) >>
  REWRITE_TAC [bir_auxiliaryTheory.FUNPOW_OPT_def, FUNPOW] >>
  ASM_SIMP_TAC std_ss [GSYM bir_auxiliaryTheory.FUNPOW_OPT_def]
);


val symb_hl_trs_thm = store_thm("symb_hl_trs_thm",
  ``!sr. !x. (symb_hl_trs sr x) = SOME (sr.sr_step_conc x)``,
  METIS_TAC [symb_hl_trs_def]
);

val FUNPOW_OPT_SOME_symb_hl_trs_thm = store_thm("FUNPOW_OPT_SOME_symb_hl_trs_thm",
  ``!sr. !n x.
      (FUNPOW_OPT (symb_hl_trs sr) n x = SOME (FUNPOW sr.sr_step_conc n x))``,
  METIS_TAC [FUNPOW_OPT_SOME_thm, symb_hl_trs_thm]
);


val symb_hl_is_weak = store_thm("symb_hl_is_weak",
  ``!sr.
      weak_model (symb_hl_etl_wm sr)``,
  SIMP_TAC (std_ss++bir_wm_SS) [weak_model_def, symb_hl_etl_wm_def, symb_hl_weak_def, symb_hl_trs_def] >>

  REWRITE_TAC [conc_step_n_in_L_relaxed_def, step_n_in_L_relaxed_def, step_n_in_L_thm, step_n_def, FUNPOW_OPT_SOME_symb_hl_trs_thm] >>

  REPEAT STRIP_TAC >>
  EQ_TAC >> (
    REPEAT STRIP_TAC >>
    Q.EXISTS_TAC `n` >>

    (*`n > 0` by () >>*)
    FULL_SIMP_TAC std_ss [IN_COMPL, GREATER_DEF]
  )
);

end;


val _ = export_theory();
