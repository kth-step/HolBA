(* ========================================================================= *)
(* FILE          : bil_mem_expScript.sml                                     *)
(* DESCRIPTION   : A model of bil variable invironments                      *)
(* AUTHOR        : (c) Thomas Tuerk <tuerk@kth.se> based on previous work    *)
(*                 by Roberto Metere, KTH - Royal Institute of Technology    *)
(* DATE          : 2017                                                      *)
(* ========================================================================= *)

open HolKernel Parse boolLib bossLib;
open wordsTheory bitstringTheory;
open finite_mapTheory;
open bil_auxiliaryTheory bil_immTheory bil_valuesTheory;

val _ = new_theory "bil_env";

val _ = Datatype `bil_var_t = Var string bil_type_t`;

val bil_var_name_def = Define `bil_var_name (Var n _) = n`;
val bil_var_type_def = Define `bil_var_type (Var _ ty) = ty`;

val _ = Datatype `bil_var_environment_t =
    IrregularEnv
  | RegularEnv (string |-> (bil_type_t # (bil_val_t option)))`;


(* Empty environment *)
val empty_env_def = Define `empty_env = RegularEnv FEMPTY`

val is_env_regular_def = Define `
  (is_env_regular IrregularEnv = F) /\
  (is_env_regular (RegularEnv _) = T)`;

val is_valid_env_def = Define `(is_valid_env IrregularEnv = F) /\
  (is_valid_env (RegularEnv m) <=> FEVERY (\ (_, (ty, vo)).
     (case vo of NONE => T | SOME v => (ty = type_of_bil_val v))) m)`

val is_valid_env_empty = store_thm ("is_valid_env_empty",
  ``is_valid_env empty_env``,
SIMP_TAC std_ss [is_valid_env_def, empty_env_def, finite_mapTheory.FEVERY_FEMPTY]);

val is_env_regular_REWRS = store_thm ("is_env_regular_REWRS",
``!env. is_env_regular env <=> (env <> IrregularEnv)``,
Cases >> SIMP_TAC (srw_ss()) [is_env_regular_def])

val bil_env_lookup_def = Define `
  (bil_env_lookup varname IrregularEnv = NONE) /\
  (bil_env_lookup varname (RegularEnv env) = FLOOKUP env varname)`

val bil_env_update_def = Define `
  (bil_env_update varname vo ty IrregularEnv = IrregularEnv) /\
  (bil_env_update varname vo ty (RegularEnv env) = 
    if (?v. (vo = SOME v) /\ (ty <> type_of_bil_val v)) then IrregularEnv else
    (RegularEnv (env |+ (varname, (ty, vo)))))`;


val bil_env_lookup_type_def = Define `
  bil_env_lookup_type var_name env = OPTION_MAP FST (bil_env_lookup var_name env)`;

val bil_env_check_type_def = Define `
  bil_env_check_type var env = 
    (bil_env_lookup_type (bil_var_name var) env = SOME (bil_var_type var))`


val bil_env_read_def = Define `bil_env_read v env =
  case (bil_env_lookup (bil_var_name v) env) of
     NONE => Unknown
   | SOME (_, NONE) => Unknown
   | SOME (ty, SOME r) => if (ty = bil_var_type v) then r else Unknown`;


val bil_env_write_def = Define `bil_env_write v va env =
  if (bil_env_check_type v env) then bil_env_update (bil_var_name v) (SOME va) (bil_var_type v) env else IrregularEnv`;


val bil_env_write_Irregular = store_thm ("bil_env_write_Irregular",
  ``!v va. (bil_env_write v va IrregularEnv) = IrregularEnv``,
SIMP_TAC std_ss [bil_env_write_def, bil_env_update_def]);

val bil_env_write_Irregular_WrongVal = store_thm ("bil_env_write_Irregular_WrongVal",
  ``!v va env. (type_of_bil_val va <> bil_var_type v) ==>
               (bil_env_write v va env = IrregularEnv)``,

REPEAT GEN_TAC >>
SIMP_TAC std_ss [bil_env_write_def, bil_env_check_type_def] >>
COND_CASES_TAC >> REWRITE_TAC[] >>
Cases_on `env` >> SIMP_TAC std_ss [bil_env_update_def])


val bil_env_var_is_bound_def = Define `
  (bil_env_var_is_bound var IrregularEnv = F) /\
  (bil_env_var_is_bound var (RegularEnv env) = (var IN FDOM env))` 


val bin_env_var_is_bound_ALT_DEF = store_thm ("bin_env_var_is_bound_ALT_DEF",
  ``!var env. bil_env_var_is_bound var env <=> IS_SOME (bil_env_lookup_type var env)``,

Cases_on `env` >> (
  SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss) [bil_env_var_is_bound_def, bil_env_var_is_bound_def,
    bil_env_lookup_type_def, bil_env_lookup_def, FLOOKUP_DEF]
));

val _ = export_theory();
