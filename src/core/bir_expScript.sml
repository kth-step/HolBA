open HolKernel Parse boolLib bossLib;
open wordsTheory bitstringTheory;
open bir_auxiliaryTheory bir_immTheory bir_valuesTheory;
open bir_imm_expTheory bir_mem_expTheory bir_envTheory;

val _ = new_theory "bir_exp";

val bir_imm_ss = rewrites ((type_rws ``:bir_imm_t``) @ (type_rws ``:bir_immtype_t``));
val bir_type_ss = rewrites ((type_rws ``:bir_type_t``));


(* ------------------------------------------------------------------------- *)
(*  Datatypes                                                                *)
(* ------------------------------------------------------------------------- *)

val _ = Datatype `bir_exp_t =
    BExp_Const             bir_imm_t
  | BExp_Den               bir_var_t

  | BExp_Cast              bir_cast_t bir_exp_t bir_immtype_t

  | BExp_UnaryExp          bir_unary_exp_t bir_exp_t
  | BExp_BinExp            bir_bin_exp_t bir_exp_t bir_exp_t
  | BExp_BinPred           bir_bin_pred_t bir_exp_t bir_exp_t
  | BExp_MemEq             bir_exp_t bir_exp_t

    (* For some reason if-then-else officially misses in BAP documentation *)
  | BExp_IfThenElse        bir_exp_t bir_exp_t bir_exp_t

  | BExp_Load              bir_exp_t bir_exp_t bir_endian_t bir_immtype_t
  | BExp_Store             bir_exp_t bir_exp_t bir_endian_t bir_exp_t
`;


(* ------------------------------------------------------------------------- *)
(*  Semantics of expressions                                                 *)
(* ------------------------------------------------------------------------- *)

val bir_eval_cast_def = Define `
  (bir_eval_cast ct (BVal_Imm bi) ty = BVal_Imm (bir_gencast ct bi ty)) /\
  (bir_eval_cast _ _ _ = BVal_Unknown)`;

val bir_eval_unary_exp_def = Define `
  (bir_eval_unary_exp et (BVal_Imm bi) = BVal_Imm (bir_unary_exp et bi)) /\
  (bir_eval_unary_exp _ _ = BVal_Unknown)`;

val bir_eval_bin_exp_def = Define `
  (bir_eval_bin_exp et (BVal_Imm bi1) (BVal_Imm bi2) =
     if (type_of_bir_imm bi1 <> type_of_bir_imm bi2) then BVal_Unknown else
     BVal_Imm (bir_bin_exp et bi1 bi2)) /\
  (bir_eval_bin_exp _ _ _ = BVal_Unknown)`;

val bir_eval_bin_pred_def = Define `
  (bir_eval_bin_pred pt (BVal_Imm bi1) (BVal_Imm bi2) =
     if (type_of_bir_imm bi1 <> type_of_bir_imm bi2) then BVal_Unknown else
     BVal_Imm (bool2b (bir_bin_pred pt bi1 bi2))) /\
  (bir_eval_bin_pred _ _ _ = BVal_Unknown)`;

val bir_eval_memeq_def = Define `
  (bir_eval_memeq (BVal_Mem at1 vt1 mmap1) (BVal_Mem at2 vt2 mmap2) =
     if ((at1 <> at2) \/ (vt1 <> vt2)) then BVal_Unknown else
     BVal_Imm (bool2b (bir_memeq at1 vt1 mmap1 mmap2))) /\
  (bir_eval_memeq _ _ = BVal_Unknown)`;

val bir_eval_ifthenelse_def = Define `
  (bir_eval_ifthenelse (BVal_Imm (Imm1 cw)) v1 v2 =
     if (type_of_bir_val v1 <> type_of_bir_val v2) then BVal_Unknown else
       if (cw = 1w) then v1 else v2) /\
  (bir_eval_ifthenelse _ _ _ = BVal_Unknown)`;

val bir_eval_load_def = Define `
  (bir_eval_load (BVal_Mem ta tv mmap) (BVal_Imm a) en t =
     if ((type_of_bir_imm a) = ta) then
        (case (bir_load_from_mem tv t ta mmap en (b2n a)) of
           NONE => BVal_Unknown
         | SOME i => BVal_Imm i)
     else BVal_Unknown) /\
  (bir_eval_load _ _ _ _ = BVal_Unknown)`;

val bir_eval_store_def = Define `
  (bir_eval_store (BVal_Mem ta tv mmap) (BVal_Imm a) en (BVal_Imm v) =
     if ((type_of_bir_imm a) = ta) then
        (case (bir_store_in_mem tv ta v mmap en (b2n a)) of
           NONE => BVal_Unknown
         | SOME mmap' => BVal_Mem ta tv mmap')
     else BVal_Unknown) /\
  (bir_eval_store _ _ _ _ = BVal_Unknown)`;



val bir_eval_exp_def = Define `
  (bir_eval_exp (BExp_Const n) env = BVal_Imm n) /\

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
`;




(* ------------------------------------------------------------------------- *)
(*  Rewrite theorems for eval                                                *)
(* ------------------------------------------------------------------------- *)

val bir_eval_cast_REWRS = store_thm ("bir_eval_cast_REWRS",
``(!ct bi ty. (bir_eval_cast ct (BVal_Imm bi) ty = BVal_Imm (bir_gencast ct bi ty))) /\
  (!ct ty. bir_eval_cast ct BVal_Unknown ty = BVal_Unknown) /\
  (!ct at vt mmap ty. bir_eval_cast ct (BVal_Mem at vt mmap) ty = BVal_Unknown)``,
SIMP_TAC std_ss [bir_eval_cast_def]);

val bir_eval_unary_exp_REWRS = store_thm ("bir_eval_unary_exp_REWRS",
 ``(!et bi. (bir_eval_unary_exp et (BVal_Imm bi) = BVal_Imm (bir_unary_exp et bi))) /\
   (!et. bir_eval_unary_exp et BVal_Unknown = BVal_Unknown) /\
   (!et at vt mmap. bir_eval_unary_exp et (BVal_Mem at vt mmap) = BVal_Unknown)``,
SIMP_TAC std_ss [bir_eval_unary_exp_def]);


val bir_eval_bin_exp_REWRS = store_thm ("bir_eval_bin_exp_REWRS",
``(!et bi1 bi2. bir_eval_bin_exp et (BVal_Imm bi1) (BVal_Imm bi2) =
     if (type_of_bir_imm bi1 <> type_of_bir_imm bi2) then BVal_Unknown else
     BVal_Imm (bir_bin_exp et bi1 bi2)) /\
  (!et v. bir_eval_bin_exp et BVal_Unknown v = BVal_Unknown) /\
  (!et v. bir_eval_bin_exp et v BVal_Unknown = BVal_Unknown) /\
  (!et at vt mmap v. bir_eval_bin_exp et (BVal_Mem at vt mmap) v = BVal_Unknown) /\
  (!et at vt mmap v. bir_eval_bin_exp et v (BVal_Mem at vt mmap) = BVal_Unknown)``,
SIMP_TAC std_ss [bir_eval_bin_exp_def] >>
CONJ_TAC >| [
  Cases_on `v` >> SIMP_TAC std_ss [bir_eval_bin_exp_def],
  Cases_on `v` >> SIMP_TAC std_ss [bir_eval_bin_exp_def]
]);

val bir_eval_bin_pred_REWRS = store_thm ("bir_eval_bin_pred_REWRS",
``(!et bi1 bi2. bir_eval_bin_pred et (BVal_Imm bi1) (BVal_Imm bi2) =
     if (type_of_bir_imm bi1 <> type_of_bir_imm bi2) then BVal_Unknown else
     BVal_Imm (bool2b (bir_bin_pred et bi1 bi2))) /\
  (!et v. bir_eval_bin_pred et BVal_Unknown v = BVal_Unknown) /\
  (!et v. bir_eval_bin_pred et v BVal_Unknown = BVal_Unknown) /\
  (!et at vt mmap v. bir_eval_bin_pred et (BVal_Mem at vt mmap) v = BVal_Unknown) /\
  (!et at vt mmap v. bir_eval_bin_pred et v (BVal_Mem at vt mmap) = BVal_Unknown)``,
SIMP_TAC std_ss [bir_eval_bin_pred_def] >>
CONJ_TAC >| [
  Cases_on `v` >> SIMP_TAC std_ss [bir_eval_bin_pred_def],
  Cases_on `v` >> SIMP_TAC std_ss [bir_eval_bin_pred_def]
]);

val bir_eval_memeq_REWRS = store_thm ("bir_eval_memeq_REWRS",
 ``(!at1 vt1 mmap1 at2 vt2 mmap2. (bir_eval_memeq (BVal_Mem at1 vt1 mmap1) (BVal_Mem at2 vt2 mmap2) =
     if ((at1 <> at2) \/ (vt1 <> vt2)) then BVal_Unknown else
     BVal_Imm (bool2b (bir_memeq at1 vt1 mmap1 mmap2)))) /\
   (!v. bir_eval_memeq BVal_Unknown v = BVal_Unknown) /\
   (!v. bir_eval_memeq v BVal_Unknown = BVal_Unknown) /\
   (!bi v. bir_eval_memeq (BVal_Imm bi) v = BVal_Unknown) /\
   (!bi v. bir_eval_memeq v (BVal_Imm bi) = BVal_Unknown)``,
SIMP_TAC std_ss [bir_eval_memeq_def] >>
CONJ_TAC >> (
  Cases_on `v` >> SIMP_TAC std_ss [bir_eval_memeq_def]
));


val bir_eval_ifthenelse_REWRS = store_thm ("bir_eval_ifthenelse_REWRS",
``(!c v1 v2. bir_eval_ifthenelse (BVal_Imm c) v1 v2 =
     if (type_of_bir_imm c = Bit1) then (
       if (type_of_bir_val v1 <> type_of_bir_val v2) then BVal_Unknown else
         if (c = Imm1 1w) then v1 else v2
     ) else BVal_Unknown) /\
  (!c e1 e2. bir_eval_ifthenelse BVal_Unknown e1 e2 = BVal_Unknown) /\
  (!at vt mmap e1 e2. bir_eval_ifthenelse (BVal_Mem at vt mmap) e1 e2 = BVal_Unknown)``,
SIMP_TAC std_ss [bir_eval_ifthenelse_def] >>
Cases_on `c` >> (
  SIMP_TAC (std_ss++bir_imm_ss) [type_of_bir_imm_def, bir_eval_ifthenelse_def]
));

val bir_eval_ifthenelse_REWRS_Unknown = store_thm ("bir_eval_ifthenelse_REWRS_Unknown",
``(!vc v1 v2.
     (type_of_bir_val vc <> SOME (BType_Imm Bit1)) ==>
     (bir_eval_ifthenelse vc v1 v2 = BVal_Unknown)) /\
  (!vc v1 v2.
     ~(bir_val_is_Bool vc) ==>
     (bir_eval_ifthenelse vc v1 v2 = BVal_Unknown)) /\
  (!vc v1 v2.
     (type_of_bir_val v1 <> type_of_bir_val v2) ==>
     (bir_eval_ifthenelse vc v1 v2 = BVal_Unknown))``,

REPEAT STRIP_TAC >> Cases_on `vc` >> (
  FULL_SIMP_TAC (std_ss++bir_type_ss++bir_imm_ss) [type_of_bir_imm_def, type_of_bir_val_def,
    bir_eval_ifthenelse_REWRS, bir_val_checker_REWRS]
));

val bir_eval_ifthenelse_TF_EQ = store_thm ("bir_eval_ifthenelse_TF_EQ",
``!c v.
     bir_eval_ifthenelse c v v =
     if (bir_val_is_Bool c) then v else BVal_Unknown``,
Cases_on `c` >> (
  SIMP_TAC (std_ss++bir_imm_ss++bir_type_ss) [type_of_bir_imm_def, bir_eval_ifthenelse_REWRS,
    bir_val_checker_REWRS]
));


val bir_eval_load_Unknown_REWRS1 = prove (
  ``(!mem en t. bir_eval_load mem BVal_Unknown en t = BVal_Unknown) /\
    (!mem en t aty vty mmap. bir_eval_load mem (BVal_Mem aty vty mmap) en t = BVal_Unknown)``,

SIMP_TAC std_ss [bir_eval_load_def] >>
REPEAT CONJ_TAC >>
Cases_on `mem` >> SIMP_TAC std_ss [bir_eval_load_def]);

val bir_eval_load_Unknown_REWRS2 = prove (
  ``(!a en t. bir_eval_load BVal_Unknown a en t = BVal_Unknown) /\
    (!a en t i. bir_eval_load (BVal_Imm i) a en t = BVal_Unknown)``,

SIMP_TAC std_ss [bir_eval_load_def]);

val bir_eval_load_Unknown_REWRS3 = prove (
  ``!a en t i aty vty mmap.
      (type_of_bir_imm i <> aty) ==>
      (bir_eval_load (BVal_Mem aty vty mmap) (BVal_Imm i) en t = BVal_Unknown)``,

SIMP_TAC std_ss [bir_eval_load_def]);


val bir_eval_load_Unknown_REWRS4 = prove (
  ``!a en t i aty vty mmap.
      (t <> vty) ==>
      (bir_eval_load (BVal_Mem aty vty mmap) (BVal_Imm i) BEnd_NoEndian t = BVal_Unknown)``,

SIMP_TAC std_ss [bir_eval_load_def] >>
REPEAT STRIP_TAC >>
COND_CASES_TAC >> SIMP_TAC std_ss [] >>
ASM_SIMP_TAC std_ss [bir_load_from_mem_NO_ENDIAN]);

val bir_eval_load_Unknown_REWRS5 = prove (
  ``!a en t i aty vty mmap en.
      (bir_number_of_mem_splits vty t aty = NONE) ==>
      (bir_eval_load (BVal_Mem aty vty mmap) (BVal_Imm i) en t = BVal_Unknown)``,

SIMP_TAC std_ss [bir_eval_load_def] >>
REPEAT STRIP_TAC >>
COND_CASES_TAC >> SIMP_TAC std_ss [] >>
ASM_SIMP_TAC std_ss [bir_load_from_mem_def]);


val bir_eval_load_Unknown_REWRS = save_thm ("bir_eval_load_Unknown_REWRS",
  REWRITE_RULE [GSYM CONJ_ASSOC] (
  LIST_CONJ [bir_eval_load_Unknown_REWRS1, bir_eval_load_Unknown_REWRS2,
             bir_eval_load_Unknown_REWRS3, bir_eval_load_Unknown_REWRS4,
             bir_eval_load_Unknown_REWRS5]));


val bir_eval_load_SINGLE_REWR = store_thm ("bir_eval_load_SINGLE_REWR",
  ``!a en t i aty vty mmap en.
      (bir_eval_load (BVal_Mem aty vty mmap) (BVal_Imm i) en vty) =
      ((if (type_of_bir_imm i = aty) then (BVal_Imm (n2bs (mmap (b2n i)) vty))
       else BVal_Unknown))``,

SIMP_TAC arith_ss [bir_eval_load_def, bir_load_from_mem_SINGLE] >>
REPEAT STRIP_TAC >>
COND_CASES_TAC >> ASM_REWRITE_TAC[] >>
`bir_mem_addr aty (b2n i) = b2n i` suffices_by ASM_SIMP_TAC std_ss [] >>
MATCH_MP_TAC bir_mem_addr_id >>
METIS_TAC[b2n_lt]
);


val bir_eval_load_BASIC_REWR = store_thm ("bir_eval_load_BASIC_REWR",
  ``!a en t i aty vty ty mmap en.
      (bir_eval_load (BVal_Mem aty vty mmap) (BVal_Imm i) en ty) =
      (if type_of_bir_imm i = aty then
        case bir_load_from_mem vty ty aty mmap en (b2n i) of
          NONE => BVal_Unknown
        | SOME i => BVal_Imm i
       else BVal_Unknown)``,
SIMP_TAC arith_ss [bir_eval_load_def]);


val bir_eval_load_FULL_REWRS = save_thm ("bir_eval_load_FULL_REWRS",
let
  val thm_prune0 = prove (``(!ta a.
      (type_of_bir_imm a <> ta) ==>
      (bir_eval_load (BVal_Mem ta tv mmap) (BVal_Imm a) en tr = BVal_Unknown)) /\
      (!tr tv.
      (tr <> tv) ==> (bir_number_of_mem_splits tv tr ta <> NONE) ==>
      (bir_eval_load (BVal_Mem ta tv mmap) (BVal_Imm i) BEnd_NoEndian tr = BVal_Unknown)) /\
      (!tr tv.
      (bir_number_of_mem_splits tv tr ta = NONE) ==>
      (bir_eval_load (BVal_Mem ta tv mmap) (BVal_Imm i) en tr = BVal_Unknown))``,
   SIMP_TAC std_ss [bir_eval_load_Unknown_REWRS])

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



val bir_eval_store_Unknown_REWRS1 = prove (
  ``(!mem en v. bir_eval_store mem BVal_Unknown en v = BVal_Unknown) /\
    (!mem en v aty vty mmap. bir_eval_store mem (BVal_Mem aty vty mmap) en v = BVal_Unknown)``,

SIMP_TAC std_ss [bir_eval_store_def] >>
REPEAT CONJ_TAC >>
Cases_on `mem` >> SIMP_TAC std_ss [bir_eval_store_def]);

val bir_eval_store_Unknown_REWRS2 = prove (
  ``(!a en v. bir_eval_store BVal_Unknown a en v = BVal_Unknown) /\
    (!a en v i. bir_eval_store (BVal_Imm i) a en v = BVal_Unknown)``,

SIMP_TAC std_ss [bir_eval_store_def]);


val bir_eval_store_Unknown_REWRS3 = prove (
  ``(!a en mem. bir_eval_store mem a en BVal_Unknown = BVal_Unknown) /\
    (!a en mem ta tv mmap. bir_eval_store mem a en (BVal_Mem ta tv mmap) = BVal_Unknown)``,

REPEAT CONJ_TAC >>
Cases_on `mem` >> Cases_on `a` >> SIMP_TAC std_ss [bir_eval_store_def]);


val bir_eval_store_Unknown_REWRS4 = prove (
  ``!en v i aty vty mmap.
      (type_of_bir_imm i <> aty) ==>
      (bir_eval_store (BVal_Mem aty vty mmap) (BVal_Imm i) en v = BVal_Unknown)``,
Cases_on `v` >>
SIMP_TAC std_ss [bir_eval_store_def]);


val bir_eval_store_Unknown_REWRS5 = prove (
  ``!a en v aty vty mmap.
      (type_of_bir_imm v <> vty) ==>
      (bir_eval_store (BVal_Mem aty vty mmap) a BEnd_NoEndian (BVal_Imm v) = BVal_Unknown)``,

Cases_on `a` >> SIMP_TAC std_ss [bir_eval_store_def] >>
REPEAT STRIP_TAC >>
COND_CASES_TAC >> SIMP_TAC std_ss [] >>
ASM_SIMP_TAC std_ss [bir_store_in_mem_NO_ENDIAN]);


val bir_eval_store_Unknown_REWRS6 = prove (
  ``!a en v aty vty mmap en.
      (bir_number_of_mem_splits vty (type_of_bir_imm v) aty = NONE) ==>
      (bir_eval_store (BVal_Mem aty vty mmap) a en (BVal_Imm v) = BVal_Unknown)``,

Cases_on `a` >> SIMP_TAC std_ss [bir_eval_store_def, LET_DEF] >>
REPEAT STRIP_TAC >>
COND_CASES_TAC >> SIMP_TAC std_ss [] >>
ASM_SIMP_TAC std_ss [bir_store_in_mem_def, LET_DEF]);


val bir_eval_store_Unknown_REWRS = save_thm ("bir_eval_store_Unknown_REWRS",
  SIMP_RULE std_ss [GSYM CONJ_ASSOC] (
  LIST_CONJ [bir_eval_store_Unknown_REWRS1, bir_eval_store_Unknown_REWRS2,
             bir_eval_store_Unknown_REWRS3, bir_eval_store_Unknown_REWRS4,
             bir_eval_store_Unknown_REWRS5, bir_eval_store_Unknown_REWRS6]));

val bir_eval_store_SINGLE_REWR = store_thm ("bir_eval_store_SINGLE_REWR",
  ``!a en t i aty v vty mmap en.
      ((type_of_bir_imm i = aty) /\ (type_of_bir_imm v = vty)) ==>
      (bir_eval_store (BVal_Mem aty vty mmap) (BVal_Imm i) en (BVal_Imm v) =
      (BVal_Mem aty vty ((b2n i =+ b2n v) mmap)))``,

SIMP_TAC arith_ss [bir_eval_store_def, bir_store_in_mem_SINGLE] >>
REPEAT STRIP_TAC >>
`bir_mem_addr (type_of_bir_imm i) (b2n i) = b2n i` suffices_by ASM_SIMP_TAC std_ss [] >>
MATCH_MP_TAC bir_mem_addr_id >>
METIS_TAC[b2n_lt]);


val bir_eval_store_BASIC_REWR = store_thm ("bir_eval_store_BASIC_REWR",
  ``!a en t i aty v vty mmap en.
      (bir_eval_store (BVal_Mem aty vty mmap) (BVal_Imm i) en (BVal_Imm v) =
      (if type_of_bir_imm i = aty then
         case bir_store_in_mem vty aty v mmap en (b2n i) of
           NONE => BVal_Unknown
         | SOME mmap' => BVal_Mem aty vty mmap'
       else BVal_Unknown))``,

SIMP_TAC arith_ss [bir_eval_store_def]);


val bir_eval_store_FULL_REWRS = save_thm ("bir_eval_store_FULL_REWRS",
let
  val thm_prune0 = prove (``(!ta a.
      (type_of_bir_imm a <> ta) ==>
      (bir_eval_store (BVal_Mem ta tv mmap) (BVal_Imm a) en v = BVal_Unknown)) /\
      (!i tv.
      (type_of_bir_imm i <> tv) ==> (bir_number_of_mem_splits tv (type_of_bir_imm i) ta <> NONE) ==>
      (bir_eval_store (BVal_Mem ta tv mmap) a BEnd_NoEndian (BVal_Imm i) = BVal_Unknown)) /\
      (!i tv.
      (bir_number_of_mem_splits tv (type_of_bir_imm i) ta = NONE) ==>
      (bir_eval_store (BVal_Mem ta tv mmap) a en (BVal_Imm i) = BVal_Unknown))``,
   SIMP_TAC std_ss [bir_eval_store_Unknown_REWRS])

  val thm_prune1 = SIMP_RULE (std_ss ++ bir_imm_ss ++ DatatypeSimps.expand_type_quants_ss [``:bir_immtype_t``, ``:bir_imm_t``]) [bir_number_of_mem_splits_REWRS, type_of_bir_imm_def, FORALL_AND_THM] thm_prune0

  val (l1, l2) = partition (is_imp_only o snd o strip_forall o concl) (CONJUNCTS thm_prune1)

  val l1' = map (SIMP_RULE (list_ss++bir_imm_ss++DatatypeSimps.expand_type_quants_ss [``:bir_immtype_t``]) [bir_number_of_mem_splits_REWRS] o (Q.GEN `ta`)) l1

  val thm_prune2 = SIMP_RULE std_ss [FORALL_AND_THM, GSYM CONJ_ASSOC] (GEN_ALL
    (LIST_CONJ (l1' @ l2)))


  val thm0 = SIMP_RULE (std_ss) [bir_eval_store_Unknown_REWRS, FORALL_AND_THM] bir_eval_store_BASIC_REWR

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
