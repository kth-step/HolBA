open HolKernel Parse boolLib bossLib;
open bir_envTheory

(* Some simple syntax for temporary variables indentified by their name. *)

val _ = new_theory "bir_temp_vars";


val bir_temp_var_name_def = Define `bir_temp_var_name vn = STRCAT "tmp_" vn`;
val bir_is_temp_var_name_def = Define `bir_is_temp_var_name vn = (TAKE 4 vn = "tmp_")`

val bir_temp_var_def = Define `bir_temp_var use_temp (BVar vn ty) =
  BVar (if use_temp then (bir_temp_var_name vn) else vn) ty`;

val bir_temp_var_name_11 = store_thm ("bir_temp_var_name_11",
  ``!vn1 vn2. (bir_temp_var_name vn1 = bir_temp_var_name vn2) <=> (vn1 = vn2)``,
SIMP_TAC list_ss [bir_temp_var_name_def]);


val bir_temp_var_name_irreflexive = store_thm ("bir_temp_var_name_irreflexive",
  ``!vn. bir_temp_var_name vn <> vn``,
REPEAT STRIP_TAC >>
`STRLEN (bir_temp_var_name vn) = STRLEN vn` by ASM_REWRITE_TAC[] >>
FULL_SIMP_TAC std_ss [stringTheory.STRLEN_CAT, bir_temp_var_name_def,
  stringTheory.STRLEN_THM]);


val bir_is_temp_var_name_ALT_DEF = store_thm ("bir_is_temp_var_name_ALT_DEF",
  ``!vn. bir_is_temp_var_name vn <=> (?vn'. vn = bir_temp_var_name vn')``,

SIMP_TAC std_ss [bir_is_temp_var_name_def, bir_temp_var_name_def] >>
GEN_TAC >> EQ_TAC >> REPEAT STRIP_TAC >> ASM_SIMP_TAC list_ss [] >>
REPEAT (
  Cases_on `vn` >> FULL_SIMP_TAC list_ss [] >>
  rename1 `TAKE _ vn = _`
));


val bir_is_temp_var_name_REWR = store_thm ("bir_is_temp_var_name_REWR",
  ``!vn. bir_is_temp_var_name (bir_temp_var_name vn)``,
METIS_TAC[bir_is_temp_var_name_ALT_DEF]);


val bir_temp_var_REWRS = store_thm ("bir_temp_var_REWRS",
  ``(!v. bir_temp_var F v = v) /\
    (!v ut. bir_var_type (bir_temp_var ut v) = bir_var_type v) /\
    (!v ut. bir_var_name (bir_temp_var ut v) =
         (if ut then (bir_temp_var_name (bir_var_name v)) else bir_var_name v))``,

REPEAT CONJ_TAC >> Cases >> (
  SIMP_TAC std_ss [bir_temp_var_def, bir_var_type_def, bir_var_name_def]
));


val _ = export_theory();
