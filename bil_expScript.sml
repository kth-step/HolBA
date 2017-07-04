(* ========================================================================= *)
(* FILE          : bil_mem_expScript.sml                                     *)
(* DESCRIPTION   : A model of expressions                                    *)
(* AUTHOR        : (c) Thomas Tuerk <tuerk@kth.se> based on previous work    *)
(*                 by Roberto Metere, KTH - Royal Institute of Technology    *)
(* DATE          : 2017                                                      *)
(* ========================================================================= *)

open HolKernel Parse boolLib bossLib;
open wordsTheory bitstringTheory;
open bil_auxiliaryTheory bil_immTheory bil_valuesTheory;
open bil_imm_expTheory bil_mem_expTheory bil_envTheory;

val _ = new_theory "bil_exp";

val bil_imm_ss = rewrites ((type_rws ``:bil_imm_t``) @ (type_rws ``:bil_immtype_t``));
val bil_type_ss = rewrites ((type_rws ``:bil_type_t``));


(* ------------------------------------------------------------------------- *)
(*  Datatypes                                                                *)
(* ------------------------------------------------------------------------- *)

val _ = Datatype `bil_exp_t =
    BExp_Const             bil_imm_t
  | BExp_Den               bil_var_t

  | BExp_Cast              bil_cast_t bil_exp_t bil_immtype_t

  | BExp_UnaryExp          bil_unary_exp_t bil_exp_t
  | BExp_BinExp            bil_bin_exp_t bil_exp_t bil_exp_t
  | BExp_BinPred           bil_bin_pred_t bil_exp_t bil_exp_t

    (* For some reason if-then-else officially misses in BAP documentation *)
  | BExp_IfThenElse        bil_exp_t bil_exp_t bil_exp_t

  | BExp_Load              bil_exp_t bil_exp_t bil_endian_t bil_immtype_t
  | BExp_Store             bil_exp_t bil_exp_t bil_endian_t bil_exp_t
`;


(* ------------------------------------------------------------------------- *)
(*  Semantics of expressions                                                 *)
(* ------------------------------------------------------------------------- *)

val bil_eval_cast_def = Define `
  (bil_eval_cast ct (BVal_Imm bi) ty = BVal_Imm (bil_gencast ct bi ty)) /\
  (bil_eval_cast _ _ _ = BVal_Unknown)`;

val bil_eval_unary_exp_def = Define `
  (bil_eval_unary_exp et (BVal_Imm bi) = BVal_Imm (bil_unary_exp et bi)) /\
  (bil_eval_unary_exp _ _ = BVal_Unknown)`;

val bil_eval_bin_exp_def = Define `
  (bil_eval_bin_exp et (BVal_Imm bi1) (BVal_Imm bi2) =
     if (type_of_bil_imm bi1 <> type_of_bil_imm bi2) then BVal_Unknown else
     BVal_Imm (bil_bin_exp et bi1 bi2)) /\
  (bil_eval_bin_exp _ _ _ = BVal_Unknown)`;

val bil_eval_bin_pred_def = Define `
  (bil_eval_bin_pred pt (BVal_Imm bi1) (BVal_Imm bi2) =
     if (type_of_bil_imm bi1 <> type_of_bil_imm bi2) then BVal_Unknown else
     BVal_Imm (bool2b (bil_bin_pred pt bi1 bi2))) /\
  (bil_eval_bin_pred _ _ _ = BVal_Unknown)`;

val bil_eval_ifthenelse_def = Define `
  (bil_eval_ifthenelse (BVal_Imm (Imm1 cw)) e1 e2 =
     if (cw = 1w) then e1 else e2) /\
  (bil_eval_ifthenelse _ _ _ = BVal_Unknown)`;

val bil_eval_load_def = Define `
  (bil_eval_load (BVal_Mem ta tv mmap) (BVal_Imm a) en t =
     if ((type_of_bil_imm a) = ta) then
        (case (bil_load_from_mem tv t mmap en (b2n a)) of
           NONE => BVal_Unknown
         | SOME i => BVal_Imm i)
     else BVal_Unknown) /\
  (bil_eval_load _ _ _ _ = BVal_Unknown)`;

val bil_eval_store_def = Define `
  (bil_eval_store (BVal_Mem ta tv mmap) (BVal_Imm a) en (BVal_Imm v) =
     if ((type_of_bil_imm a) = ta) then
        (case (bil_store_in_mem tv v mmap en (b2n a)) of
           NONE => BVal_Unknown
         | SOME mmap' => BVal_Mem ta tv mmap')
     else BVal_Unknown) /\
  (bil_eval_store _ _ _ _ = BVal_Unknown)`;



val bil_eval_exp_def = Define `
  (bil_eval_exp (BExp_Const n) env = BVal_Imm n) /\

  (bil_eval_exp (BExp_Den v) env = bil_env_read v env) /\

  (bil_eval_exp (BExp_Cast ct e ty) env = (
     bil_eval_cast ct (bil_eval_exp e env) ty)) /\

  (bil_eval_exp (BExp_UnaryExp et e) env = (
     bil_eval_unary_exp et (bil_eval_exp e env))) /\

  (bil_eval_exp (BExp_BinExp et e1 e2) env = (
     bil_eval_bin_exp et (bil_eval_exp e1 env) (bil_eval_exp e2 env))) /\

  (bil_eval_exp (BExp_BinPred pt e1 e2) env = (
     bil_eval_bin_pred pt (bil_eval_exp e1 env) (bil_eval_exp e2 env))) /\

  (bil_eval_exp (BExp_IfThenElse c et ef) env =
     bil_eval_ifthenelse (bil_eval_exp c env) (bil_eval_exp et env) (bil_eval_exp ef env)
  ) /\

  (bil_eval_exp (BExp_Load mem_e a_e en ty) env =
     bil_eval_load (bil_eval_exp mem_e env) (bil_eval_exp a_e env) en ty) /\

  (bil_eval_exp (BExp_Store mem_e a_e en v_e) env =
     bil_eval_store (bil_eval_exp mem_e env) (bil_eval_exp a_e env) en (bil_eval_exp v_e env))
`;




(* ------------------------------------------------------------------------- *)
(*  Rewrite theorems for eval                                                *)
(* ------------------------------------------------------------------------- *)

val bil_eval_cast_REWRS = store_thm ("bil_eval_cast_REWRS",
``(!ct bi ty. (bil_eval_cast ct (BVal_Imm bi) ty = BVal_Imm (bil_gencast ct bi ty))) /\
  (!ct ty. bil_eval_cast ct BVal_Unknown ty = BVal_Unknown) /\
  (!ct at vt mmap ty. bil_eval_cast ct (BVal_Mem at vt mmap) ty = BVal_Unknown)``,
SIMP_TAC std_ss [bil_eval_cast_def]);

val bil_eval_unary_exp_REWRS = store_thm ("bil_eval_unary_exp_REWRS",
 ``(!et bi. (bil_eval_unary_exp et (BVal_Imm bi) = BVal_Imm (bil_unary_exp et bi))) /\
   (!et. bil_eval_unary_exp et BVal_Unknown = BVal_Unknown) /\
   (!et at vt mmap. bil_eval_unary_exp et (BVal_Mem at vt mmap) = BVal_Unknown)``,
SIMP_TAC std_ss [bil_eval_unary_exp_def]);


val bil_eval_bin_exp_REWRS = store_thm ("bil_eval_bin_exp_REWRS",
``(!et bi1 bi2. bil_eval_bin_exp et (BVal_Imm bi1) (BVal_Imm bi2) =
     if (type_of_bil_imm bi1 <> type_of_bil_imm bi2) then BVal_Unknown else
     BVal_Imm (bil_bin_exp et bi1 bi2)) /\
  (!et v. bil_eval_bin_exp et BVal_Unknown v = BVal_Unknown) /\
  (!et v. bil_eval_bin_exp et v BVal_Unknown = BVal_Unknown) /\
  (!et at vt mmap v. bil_eval_bin_exp et (BVal_Mem at vt mmap) v = BVal_Unknown) /\
  (!et at vt mmap v. bil_eval_bin_exp et v (BVal_Mem at vt mmap) = BVal_Unknown)``,
SIMP_TAC std_ss [bil_eval_bin_exp_def] >>
CONJ_TAC >| [
  Cases_on `v` >> SIMP_TAC std_ss [bil_eval_bin_exp_def],
  Cases_on `v` >> SIMP_TAC std_ss [bil_eval_bin_exp_def]
]);

val bil_eval_bin_pred_REWRS = store_thm ("bil_eval_bin_pred_REWRS",
``(!et bi1 bi2. bil_eval_bin_pred et (BVal_Imm bi1) (BVal_Imm bi2) =
     if (type_of_bil_imm bi1 <> type_of_bil_imm bi2) then BVal_Unknown else
     BVal_Imm (bool2b (bil_bin_pred et bi1 bi2))) /\
  (!et v. bil_eval_bin_pred et BVal_Unknown v = BVal_Unknown) /\
  (!et v. bil_eval_bin_pred et v BVal_Unknown = BVal_Unknown) /\
  (!et at vt mmap v. bil_eval_bin_pred et (BVal_Mem at vt mmap) v = BVal_Unknown) /\
  (!et at vt mmap v. bil_eval_bin_pred et v (BVal_Mem at vt mmap) = BVal_Unknown)``,
SIMP_TAC std_ss [bil_eval_bin_pred_def] >>
CONJ_TAC >| [
  Cases_on `v` >> SIMP_TAC std_ss [bil_eval_bin_pred_def],
  Cases_on `v` >> SIMP_TAC std_ss [bil_eval_bin_pred_def]
]);


val bil_eval_ifthenelse_REWRS = store_thm ("bil_eval_ifthenelse_REWRS",
``(!c e1 e2. bil_eval_ifthenelse (BVal_Imm c) e1 e2 =
     if (type_of_bil_imm c = Bit1) then (
       if (c = Imm1 1w) then e1 else e2
     ) else BVal_Unknown) /\
  (!c e1 e2. bil_eval_ifthenelse BVal_Unknown e1 e2 = BVal_Unknown) /\
  (!at vt mmap e1 e2. bil_eval_ifthenelse (BVal_Mem at vt mmap) e1 e2 = BVal_Unknown)``,
SIMP_TAC std_ss [bil_eval_ifthenelse_def] >>
Cases_on `c` >> (
  SIMP_TAC (std_ss++bil_imm_ss) [type_of_bil_imm_def, bil_eval_ifthenelse_def]
));

val bil_eval_ifthenelse_REWRS_Unknown = store_thm ("bil_eval_ifthenelse_REWRS_Unknown",
``(!ec e1 e2.
     (type_of_bil_val ec <> SOME (BType_Imm Bit1)) ==>
     (bil_eval_ifthenelse ec e1 e2 = BVal_Unknown))``,

Cases_on `ec` >> (
  SIMP_TAC (std_ss++bil_type_ss++bil_imm_ss) [type_of_bil_imm_def, type_of_bil_val_def,
    bil_eval_ifthenelse_REWRS]
));

val bil_eval_ifthenelse_TF_EQ = store_thm ("bil_eval_ifthenelse_TF_EQ",
``!c e.
     bil_eval_ifthenelse c e e =
     if (bil_val_is_Bool c) then e else BVal_Unknown``,
Cases_on `c` >> (
  SIMP_TAC (std_ss++bil_imm_ss++bil_type_ss) [type_of_bil_imm_def, bil_eval_ifthenelse_REWRS,
    bil_val_checker_REWRS]
));


val bil_eval_load_Unknown_REWRS1 = prove (
  ``(!mem en t. bil_eval_load mem BVal_Unknown en t = BVal_Unknown) /\
    (!mem en t aty vty mmap. bil_eval_load mem (BVal_Mem aty vty mmap) en t = BVal_Unknown)``,

SIMP_TAC std_ss [bil_eval_load_def] >>
REPEAT CONJ_TAC >>
Cases_on `mem` >> SIMP_TAC std_ss [bil_eval_load_def]);

val bil_eval_load_Unknown_REWRS2 = prove (
  ``(!a en t. bil_eval_load BVal_Unknown a en t = BVal_Unknown) /\
    (!a en t i. bil_eval_load (BVal_Imm i) a en t = BVal_Unknown)``,

SIMP_TAC std_ss [bil_eval_load_def]);

val bil_eval_load_Unknown_REWRS3 = prove (
  ``!a en t i aty vty mmap.
      (type_of_bil_imm i <> aty) ==>
      (bil_eval_load (BVal_Mem aty vty mmap) (BVal_Imm i) en t = BVal_Unknown)``,

SIMP_TAC std_ss [bil_eval_load_def]);


val bil_eval_load_Unknown_REWRS4 = prove (
  ``!a en t i aty vty mmap.
      (t <> vty) ==>
      (bil_eval_load (BVal_Mem aty vty mmap) (BVal_Imm i) BEnd_NoEndian t = BVal_Unknown)``,

SIMP_TAC std_ss [bil_eval_load_def] >>
REPEAT STRIP_TAC >>
COND_CASES_TAC >> SIMP_TAC std_ss [] >>
ASM_SIMP_TAC std_ss [bil_load_from_mem_NO_ENDIAN]);

val bil_eval_load_Unknown_REWRS5 = prove (
  ``!a en t i aty vty mmap en.
      (bil_number_of_mem_splits vty t = NONE) ==>
      (bil_eval_load (BVal_Mem aty vty mmap) (BVal_Imm i) en t = BVal_Unknown)``,

SIMP_TAC std_ss [bil_eval_load_def] >>
REPEAT STRIP_TAC >>
COND_CASES_TAC >> SIMP_TAC std_ss [] >>
ASM_SIMP_TAC std_ss [bil_load_from_mem_def]);


val bil_eval_load_Unknown_REWRS = save_thm ("bil_eval_load_Unknown_REWRS",
  REWRITE_RULE [GSYM CONJ_ASSOC] (
  LIST_CONJ [bil_eval_load_Unknown_REWRS1, bil_eval_load_Unknown_REWRS2,
             bil_eval_load_Unknown_REWRS3, bil_eval_load_Unknown_REWRS4,
             bil_eval_load_Unknown_REWRS5]));


val bil_eval_load_SINGLE_REWR = store_thm ("bil_eval_load_SINGLE_REWR",
  ``!a en t i aty vty mmap en.
      (bil_eval_load (BVal_Mem aty vty mmap) (BVal_Imm i) en vty) =
      ((if (type_of_bil_imm i = aty) then (BVal_Imm (n2bs (mmap (b2n i)) vty))
       else BVal_Unknown))``,

SIMP_TAC arith_ss [bil_eval_load_def, bil_load_from_mem_SINGLE]);


val bil_eval_load_BASIC_REWR = store_thm ("bil_eval_load_BASIC_REWR",
  ``!a en t i aty vty ty mmap en.
      (bil_eval_load (BVal_Mem aty vty mmap) (BVal_Imm i) en ty) =
      (if type_of_bil_imm i = aty then
        case bil_load_from_mem vty ty mmap en (b2n i) of
          NONE => BVal_Unknown
        | SOME i => BVal_Imm i
       else BVal_Unknown)``,
SIMP_TAC arith_ss [bil_eval_load_def]);


val bil_eval_load_FULL_REWRS = save_thm ("bil_eval_load_FULL_REWRS",
let
  val thm_prune0 = prove (``(!ta a.
      (type_of_bil_imm a <> ta) ==>
      (bil_eval_load (BVal_Mem ta tv mmap) (BVal_Imm a) en tr = BVal_Unknown)) /\
      (!tr tv.
      (tr <> tv) ==> (bil_number_of_mem_splits tv tr <> NONE) ==>
      (bil_eval_load (BVal_Mem ta tv mmap) (BVal_Imm i) BEnd_NoEndian tr = BVal_Unknown)) /\
      (!tr tv.
      (bil_number_of_mem_splits tv tr = NONE) ==>
      (bil_eval_load (BVal_Mem ta tv mmap) (BVal_Imm i) en tr = BVal_Unknown))``,
   SIMP_TAC std_ss [bil_eval_load_Unknown_REWRS])

  val thm_prune1 = SIMP_RULE (std_ss ++ bil_imm_ss ++ DatatypeSimps.expand_type_quants_ss [``:bil_immtype_t``, ``:bil_imm_t``]) [bil_number_of_mem_splits_REWRS, type_of_bil_imm_def] thm_prune0

  val thm_prune2 = SIMP_RULE std_ss [FORALL_AND_THM, GSYM CONJ_ASSOC] (GEN_ALL thm_prune1)


  val thm0 = bil_eval_load_BASIC_REWR

  val thm1 = SIMP_RULE (list_ss ++ bil_imm_ss ++ DatatypeSimps.expand_type_quants_ss [``:bil_immtype_t``, ``:bil_imm_t``, ``:bil_endian_t``]) [ type_of_bil_imm_def, size_of_bil_immtype_def, bil_number_of_mem_splits_REWRS, bil_load_from_mem_REWRS, thm_prune2]
     thm0

  val thm2 = Ho_Rewrite.REWRITE_RULE [fold_bil_endian_THM] thm1

  val thm3 = SIMP_RULE (list_ss) [
     FORALL_AND_THM, b2n_MOD_2EXP, type_of_bil_imm_def, size_of_bil_immtype_def]
     thm2

  val thm4 = REWRITE_RULE [b2n_def, GSYM CONJ_ASSOC] (CONJ thm3 thm_prune2)
in thm4
end);



val bil_eval_store_Unknown_REWRS1 = prove (
  ``(!mem en v. bil_eval_store mem BVal_Unknown en v = BVal_Unknown) /\
    (!mem en v aty vty mmap. bil_eval_store mem (BVal_Mem aty vty mmap) en v = BVal_Unknown)``,

SIMP_TAC std_ss [bil_eval_store_def] >>
REPEAT CONJ_TAC >>
Cases_on `mem` >> SIMP_TAC std_ss [bil_eval_store_def]);

val bil_eval_store_Unknown_REWRS2 = prove (
  ``(!a en v. bil_eval_store BVal_Unknown a en v = BVal_Unknown) /\
    (!a en v i. bil_eval_store (BVal_Imm i) a en v = BVal_Unknown)``,

SIMP_TAC std_ss [bil_eval_store_def]);


val bil_eval_store_Unknown_REWRS3 = prove (
  ``(!a en mem. bil_eval_store mem a en BVal_Unknown = BVal_Unknown) /\
    (!a en mem ta tv mmap. bil_eval_store mem a en (BVal_Mem ta tv mmap) = BVal_Unknown)``,

REPEAT CONJ_TAC >>
Cases_on `mem` >> Cases_on `a` >> SIMP_TAC std_ss [bil_eval_store_def]);


val bil_eval_store_Unknown_REWRS4 = prove (
  ``!en v i aty vty mmap.
      (type_of_bil_imm i <> aty) ==>
      (bil_eval_store (BVal_Mem aty vty mmap) (BVal_Imm i) en v = BVal_Unknown)``,
Cases_on `v` >>
SIMP_TAC std_ss [bil_eval_store_def]);


val bil_eval_store_Unknown_REWRS5 = prove (
  ``!a en v aty vty mmap.
      (type_of_bil_imm v <> vty) ==>
      (bil_eval_store (BVal_Mem aty vty mmap) a BEnd_NoEndian (BVal_Imm v) = BVal_Unknown)``,

Cases_on `a` >> SIMP_TAC std_ss [bil_eval_store_def] >>
REPEAT STRIP_TAC >>
COND_CASES_TAC >> SIMP_TAC std_ss [] >>
ASM_SIMP_TAC std_ss [bil_store_in_mem_NO_ENDIAN]);


val bil_eval_store_Unknown_REWRS6 = prove (
  ``!a en v aty vty mmap en.
      (bil_number_of_mem_splits vty (type_of_bil_imm v) = NONE) ==>
      (bil_eval_store (BVal_Mem aty vty mmap) a en (BVal_Imm v) = BVal_Unknown)``,

Cases_on `a` >> SIMP_TAC std_ss [bil_eval_store_def, LET_DEF] >>
REPEAT STRIP_TAC >>
COND_CASES_TAC >> SIMP_TAC std_ss [] >>
ASM_SIMP_TAC std_ss [bil_store_in_mem_def, LET_DEF]);


val bil_eval_store_Unknown_REWRS = save_thm ("bil_eval_store_Unknown_REWRS",
  SIMP_RULE std_ss [GSYM CONJ_ASSOC] (
  LIST_CONJ [bil_eval_store_Unknown_REWRS1, bil_eval_store_Unknown_REWRS2,
             bil_eval_store_Unknown_REWRS3, bil_eval_store_Unknown_REWRS4,
             bil_eval_store_Unknown_REWRS5, bil_eval_store_Unknown_REWRS6]));

val bil_eval_store_SINGLE_REWR = store_thm ("bil_eval_store_SINGLE_REWR",
  ``!a en t i aty v vty mmap en.
      ((type_of_bil_imm i = aty) /\ (type_of_bil_imm v = vty)) ==>
      (bil_eval_store (BVal_Mem aty vty mmap) (BVal_Imm i) en (BVal_Imm v) =
      (BVal_Mem aty vty ((b2n i =+ b2n v) mmap)))``,

SIMP_TAC arith_ss [bil_eval_store_def, bil_store_in_mem_SINGLE]);



val bil_eval_store_BASIC_REWR = store_thm ("bil_eval_store_BASIC_REWR",
  ``!a en t i aty v vty mmap en.
      (bil_eval_store (BVal_Mem aty vty mmap) (BVal_Imm i) en (BVal_Imm v) =
      (if type_of_bil_imm i = aty then
         case bil_store_in_mem vty v mmap en (b2n i) of
           NONE => BVal_Unknown
         | SOME mmap' => BVal_Mem aty vty mmap'
       else BVal_Unknown))``,

SIMP_TAC arith_ss [bil_eval_store_def]);


val bil_eval_store_FULL_REWRS = save_thm ("bil_eval_store_FULL_REWRS",
let
  val thm_prune0 = prove (``(!ta a.
      (type_of_bil_imm a <> ta) ==>
      (bil_eval_store (BVal_Mem ta tv mmap) (BVal_Imm a) en v = BVal_Unknown)) /\
      (!i tv.
      (type_of_bil_imm i <> tv) ==> (bil_number_of_mem_splits tv (type_of_bil_imm i) <> NONE) ==>
      (bil_eval_store (BVal_Mem ta tv mmap) a BEnd_NoEndian (BVal_Imm i) = BVal_Unknown)) /\
      (!i tv.
      (bil_number_of_mem_splits tv (type_of_bil_imm i) = NONE) ==>
      (bil_eval_store (BVal_Mem ta tv mmap) a en (BVal_Imm i) = BVal_Unknown))``,
   SIMP_TAC std_ss [bil_eval_store_Unknown_REWRS])

  val thm_prune1 = SIMP_RULE (std_ss ++ bil_imm_ss ++ DatatypeSimps.expand_type_quants_ss [``:bil_immtype_t``, ``:bil_imm_t``]) [bil_number_of_mem_splits_REWRS, type_of_bil_imm_def] thm_prune0

  val thm_prune2 = SIMP_RULE std_ss [FORALL_AND_THM, GSYM CONJ_ASSOC] (GEN_ALL thm_prune1)


  val thm0 = SIMP_RULE (std_ss) [bil_eval_store_Unknown_REWRS, FORALL_AND_THM] bil_eval_store_BASIC_REWR

  val thm1 = SIMP_RULE (list_ss++ bil_imm_ss ++ DatatypeSimps.expand_type_quants_ss [``:bil_immtype_t``, ``:bil_imm_t``, ``:bil_endian_t``]) [ type_of_bil_imm_def, size_of_bil_immtype_def, bil_number_of_mem_splits_REWRS, bil_store_in_mem_REWRS, thm_prune2]
     thm0

  val thm2 = Ho_Rewrite.REWRITE_RULE [fold_bil_endian_THM] thm1

  val thm3 = SIMP_RULE (list_ss) [
     FORALL_AND_THM, type_of_bil_imm_def, size_of_bil_immtype_def]
     thm2

  val thm4 = REWRITE_RULE [b2n_def, GSYM CONJ_ASSOC] (CONJ thm3 thm_prune2)
in thm4
end);


(* ------------------------------------------------------------------------- *)
(*  Boolean Expressions                                                      *)
(* ------------------------------------------------------------------------- *)

val bil_dest_bool_val_def = Define `
  (bil_dest_bool_val (BVal_Imm (Imm1 w)) = SOME (w = 1w)) /\
  (bil_dest_bool_val _ = NONE)`

val bil_dest_bool_val_EQ_NONE = store_thm ("bil_dest_bool_val_EQ_NONE",
  ``!v. (bil_dest_bool_val v = NONE) <=> ~(bil_val_is_Bool v)``,
Cases >> SIMP_TAC std_ss [bil_val_checker_REWRS, bil_dest_bool_val_def] >>
Cases_on `b` >> SIMP_TAC (std_ss++bil_imm_ss) [bil_val_checker_REWRS, bil_dest_bool_val_def,
  type_of_bil_imm_def]);



val _ = export_theory();
