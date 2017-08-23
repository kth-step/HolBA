open HolKernel Parse boolLib bossLib;
open bir_program_blocksTheory;
open stringTheory finite_mapTheory pred_setTheory
open bir_envTheory listTheory
open bir_programTheory
open bir_auxiliaryTheory
open HolBACoreSimps;


(* This theory defines functionality for blocks that update multiple
   variables "in parallel".

   A single update specification states that a certain variable in the
   environment should be updated to contain the value of a certain
   expression. If multiple variables should be updated "in parallel",
   the problem arises that variables used in later expression have
   already been updated. update-blocks use temporary variables to
   store the old value and perform a seemingly "parallel"
   update. However, the value of potentially used temp vars is
   changed.
*)



val _ = new_theory "bir_update_block";


(****************************)
(* Temporary variable names *)
(****************************)

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



(****************************)
(* Update descriptions      *)
(****************************)

val _ = Datatype `bir_updateB_desc_t = BUpdateDescB bir_var_t bir_exp_t bir_val_t bool`;

val bir_updateB_desc_t_11 = DB.fetch "-" "bir_updateB_desc_t_11";

val bir_updateB_desc_var_def =
  Define `bir_updateB_desc_var (BUpdateDescB var _ _ _) = var`;

val bir_updateB_desc_temp_var_def =
  Define `bir_updateB_desc_temp_var (BUpdateDescB var _ _ use_temp) =
          bir_temp_var use_temp var`;

val bir_updateB_desc_exp_def =
  Define `bir_updateB_desc_exp (BUpdateDescB _ e _ _) = e`;

val bir_updateB_desc_value_def =
  Define `bir_updateB_desc_value (BUpdateDescB _ _ v _) = v`;

val bir_updateB_desc_use_temp_def =
  Define `bir_updateB_desc_use_temp (BUpdateDescB _ _ _ ut) = ut`;


val bir_updateB_desc_ACCESSORS = save_thm ("bir_updateB_desc_ACCESSORS",
  LIST_CONJ [bir_updateB_desc_var_def, bir_updateB_desc_temp_var_def,
             bir_updateB_desc_exp_def, bir_updateB_desc_value_def,
             bir_updateB_desc_use_temp_def]);



val bir_updateB_desc_OK_def = Define `
  bir_updateB_desc_OK env (BUpdateDescB var e v use_temp) <=> (
     (* Types fit *)
     (type_of_bir_val v = SOME (bir_var_type var)) /\

     (* The varname is not a temp one *)
     (~(bir_is_temp_var_name (bir_var_name var))) /\

     (* Variable and if used the temp var are declared *)
     bir_env_var_is_declared env var /\
     bir_env_var_is_declared env (bir_temp_var use_temp var) /\

     (* The expression really evaluates to the given value *)
     (bir_eval_exp e env = v)
  )`


val bir_update_blockB_desc_OK_def = Define `
  bir_update_blockB_desc_OK env updates <=> (

  (* All descs are well-formed *)
  EVERY (bir_updateB_desc_OK env) updates /\

  (* A var is only updated once *)
  (ALL_DISTINCT (MAP (\up. bir_var_name (bir_updateB_desc_var up)) updates)) /\

  (* Previous assigments do not interfer. *)
  (!i j var. (i < LENGTH updates) /\ (j < i) /\
             var IN (bir_vars_of_exp (bir_updateB_desc_exp (EL i updates))) ==>
             (bir_var_name var <>
                 bir_var_name (bir_updateB_desc_temp_var (EL j updates)))))`;



val bir_update_blockB_desc_OK_NULL = store_thm("bir_update_blockB_desc_OK_NULL", ``
  !env. bir_update_blockB_desc_OK env []``,
SIMP_TAC list_ss [bir_update_blockB_desc_OK_def]);


val bir_update_blockB_desc_OK_SNOC = store_thm("bir_update_blockB_desc_OK_SNOC", ``
  !env updates up.
  bir_update_blockB_desc_OK env (SNOC up updates) <=>

  (bir_update_blockB_desc_OK env updates /\
  (EVERY (\up'. ~(bir_var_name (bir_updateB_desc_var up') = bir_var_name (bir_updateB_desc_var up))) updates) /\

  (let used_var_name_set = IMAGE bir_var_name (bir_vars_of_exp (bir_updateB_desc_exp up)) in
  (EVERY (\up'. ~(bir_var_name (bir_updateB_desc_temp_var up') IN used_var_name_set)) updates)) /\
  (bir_updateB_desc_OK env up)
)``,

SIMP_TAC (list_ss++boolSimps.EQUIV_EXTRACT_ss) [bir_update_blockB_desc_OK_def,
  EVERY_SNOC, MAP_SNOC, prim_recTheory.LESS_THM, ALL_DISTINCT_SNOC, MEM_MAP,
  RIGHT_AND_OVER_OR, DISJ_IMP_THM, FORALL_AND_THM, EL_LENGTH_SNOC,
  EL_SNOC, LET_THM, IN_IMAGE, EVERY_MEM, MEM_EL, GSYM LEFT_FORALL_IMP_THM,
  GSYM RIGHT_FORALL_OR_THM] >>
METIS_TAC[EL_SNOC]);


val bir_update_blockB_desc_OK_CONS = store_thm("bir_update_blockB_desc_OK_CONS", ``
  !env updates up.
  bir_update_blockB_desc_OK env (up :: updates) <=>

  (bir_update_blockB_desc_OK env updates /\
  (EVERY (\up'. ~(bir_var_name (bir_updateB_desc_var up') = bir_var_name (bir_updateB_desc_var up))) updates) /\
  (bir_updateB_desc_OK env up) /\
  (EVERY (\up'. ~(bir_var_name (bir_updateB_desc_temp_var up) IN
      IMAGE bir_var_name (bir_vars_of_exp (bir_updateB_desc_exp up')))) updates)
)``,

SIMP_TAC (list_ss++boolSimps.EQUIV_EXTRACT_ss) [bir_update_blockB_desc_OK_def,
  FORALL_AND_THM, EVERY_MEM, MEM_MAP, indexedListsTheory.LT_SUC,
  RIGHT_AND_OVER_OR, DISJ_IMP_THM, GSYM LEFT_EXISTS_AND_THM, GSYM LEFT_FORALL_IMP_THM,
  LEFT_AND_OVER_OR, GSYM RIGHT_EXISTS_AND_THM, IN_IMAGE] >>
REPEAT STRIP_TAC >>
METIS_TAC[MEM_EL]);



val bir_update_blockB_desc_OK_VARNAME_UNIQUE = store_thm ("bir_update_blockB_desc_OK_VARNAME_UNIQUE",
  ``!env updates up1 up2.
       bir_update_blockB_desc_OK env updates ==>
       MEM up1 updates ==>
       MEM up2 updates ==>
       (bir_var_name (bir_updateB_desc_var up1) = bir_var_name (bir_updateB_desc_var up2)) ==>

       (up1 = up2)``,

REPEAT GEN_TAC >> REPEAT DISCH_TAC >>
`?i1. i1 < LENGTH updates /\ (EL i1 updates = up1)` by
  METIS_TAC[MEM_EL] >>
`?i2. i2 < LENGTH updates /\ (EL i2 updates = up2)` by
  METIS_TAC[MEM_EL] >>

MP_TAC (ISPECL [``MAP (\up. bir_var_name (bir_updateB_desc_var up)) updates``, ``i1:num``, ``i2:num``] ALL_DISTINCT_EL_IMP) >>
FULL_SIMP_TAC list_ss [EL_MAP, bir_update_blockB_desc_OK_def] >>
STRIP_TAC >>
FULL_SIMP_TAC std_ss []);



val bir_update_blockB_desc_TEMP_VAR_NAMES_DIFFERENT = store_thm ("bir_update_blockB_desc_TEMP_VAR_NAMES_DIFFERENT",
``!var use_temp updates env.

bir_update_blockB_desc_OK env updates /\
EVERY
  (\up.
     bir_var_name (bir_updateB_desc_var up) <>
     bir_var_name var) updates /\
~(bir_is_temp_var_name (bir_var_name var)) ==>
EVERY
  (\up.
     bir_var_name (bir_temp_var use_temp var) <>
     bir_var_name (bir_updateB_desc_temp_var up)) updates``,

SIMP_TAC std_ss [EVERY_MEM, bir_update_blockB_desc_OK_def] >>
REPEAT GEN_TAC >> STRIP_TAC >>
REPEAT GEN_TAC >> STRIP_TAC >>
`bir_updateB_desc_OK env up /\
 (bir_var_name var <> bir_var_name (bir_updateB_desc_var up))` by METIS_TAC[] >>
Cases_on `up` >>
FULL_SIMP_TAC std_ss [bir_updateB_desc_ACCESSORS, bir_temp_var_REWRS,
  bir_updateB_desc_OK_def] >>
ASM_SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss) [bir_temp_var_name_11] >>
METIS_TAC[bir_is_temp_var_name_ALT_DEF]);




val bir_update_blockB_desc_OK_compute_def = Define `
   bir_update_blockB_desc_OK_compute env (updated_vars : string set) (used_exp_vars : string set) updates =
   (bir_update_blockB_desc_OK env updates /\
    EVERY (\up.
       (bir_var_name (bir_updateB_desc_var up) IN updated_vars) /\
       (IMAGE bir_var_name (bir_vars_of_exp (bir_updateB_desc_exp up)) SUBSET used_exp_vars))
      updates)`

val bir_update_blockB_desc_OK_compute_FINAL = store_thm ("bir_update_blockB_desc_OK_compute_FINAL",
  ``bir_update_blockB_desc_OK_compute env uvs evs updates ==>
    bir_update_blockB_desc_OK env updates``, SIMP_TAC std_ss [bir_update_blockB_desc_OK_compute_def])

val bir_update_blockB_desc_OK_compute_INIT = store_thm ("bir_update_blockB_desc_OK_compute_INIT",
  ``!env. bir_update_blockB_desc_OK_compute env {} {} []``,
SIMP_TAC list_ss [bir_update_blockB_desc_OK_compute_def, bir_update_blockB_desc_OK_NULL]);

val bir_update_blockB_desc_OK_compute_CONS = store_thm ("bir_update_blockB_desc_OK_compute_CONS",
  ``bir_update_blockB_desc_OK_compute env uvs evs updates ==>
    bir_updateB_desc_OK env (BUpdateDescB var e v use_temp) ==>
    ~((bir_var_name var) IN uvs) /\
    ~((bir_var_name (bir_temp_var use_temp var)) IN evs) ==>
    bir_update_blockB_desc_OK_compute env ((bir_var_name var) INSERT uvs) (IMAGE bir_var_name (bir_vars_of_exp e) UNION evs) ((BUpdateDescB var e v use_temp)::updates)``,

SIMP_TAC list_ss [bir_update_blockB_desc_OK_compute_def, bir_update_blockB_desc_OK_CONS,
  bir_updateB_desc_ACCESSORS, IN_INSERT, SUBSET_UNION, IN_IMAGE, SUBSET_DEF,
  GSYM EVERY_CONJ] >>

SIMP_TAC (std_ss ++ boolSimps.CONJ_ss) [GSYM LEFT_FORALL_IMP_THM, EVERY_MEM,
  bir_temp_var_REWRS] >>
METIS_TAC[]);



(*****************)
(* Update blocks *)
(*****************)

val bir_update_blockB_STEP1_def = Define `
  bir_update_blockB_STEP1 (BUpdateDescB var e v use_temp) =
  BStmt_Assign (bir_temp_var use_temp var) e`

val bir_update_blockB_STEP2_def = Define `
  (bir_update_blockB_STEP2 (BUpdateDescB var e v T) =
     (BStmt_Assign var (BExp_Den (bir_temp_var T var))))

  (* We don't care for case where no temp vars are used *)
`

val bir_update_blockB_def = Define `bir_update_blockB updates =
  (MAP bir_update_blockB_STEP1 updates) ++
  (MAP bir_update_blockB_STEP2 (FILTER bir_updateB_desc_use_temp updates))`


(* We will show theorems for the first and the second part of the block
   separately and then combine them *)

val bir_update_blockB_SEM1 = prove (``!st c l updates.

  (* the initial state is not terminated and the updates are fine in this
     states environment *)
  bir_update_blockB_desc_OK st.bst_environ updates /\
  ~(bir_state_is_terminated st) ==> (?st'.

  (* Then the execution of the first part of the block terminates without
     running into an error or halting *)
  (bir_exec_stmtsB (MAP bir_update_blockB_STEP1 updates) (l, c, st) =
     (REVERSE l, c + LENGTH updates, st')) /\
  ~(bir_state_is_terminated st') /\

  (* In the resulting state, either the variables in temp themselves or
     their temp version having been updated to contain now the desired value *)
  (EVERY (\up.
        (bir_env_lookup (bir_var_name (bir_updateB_desc_temp_var up)) st'.bst_environ =
          SOME (bir_var_type (bir_updateB_desc_var up), SOME (bir_updateB_desc_value up)))) updates) /\

  (* All other vars have still the same value *)
  (!vn. (EVERY (\up. vn <> bir_var_name (bir_updateB_desc_temp_var up)) updates) ==>
        (bir_env_lookup vn st'.bst_environ = bir_env_lookup vn st.bst_environ)))``,


NTAC 3 GEN_TAC >>
listLib.SNOC_INDUCT_TAC >- (
  SIMP_TAC list_ss [bir_exec_stmtsB_REWRS]
) >>

Cases >>
rename1 `SNOC (BUpdateDescB var e v use_temp) updates` >>
SIMP_TAC std_ss [bir_update_blockB_desc_OK_SNOC] >>
REPEAT STRIP_TAC >>
FULL_SIMP_TAC list_ss [SNOC_APPEND, bir_exec_stmtsB_APPEND, LET_THM, IN_IMAGE,
  bir_updateB_desc_ACCESSORS, bir_updateB_desc_OK_def] >>
ASM_SIMP_TAC arith_ss [bir_exec_stmtsB_REWRS, bir_update_blockB_STEP1_def,
  bir_exec_stmtB_def, LET_THM, OPT_CONS_REWRS, DISJ_IMP_THM, FORALL_AND_THM,
  bir_updateB_desc_ACCESSORS] >>


Cases_on `st.bst_environ` >> rename1 `BEnv env` >>
Cases_on `st'.bst_environ` >> rename1 `st'.bst_environ = BEnv env'` >>

`EVERY
  (\up.
     bir_var_name (bir_temp_var use_temp var) <>
     bir_var_name (bir_updateB_desc_temp_var up)) updates` by (
  MATCH_MP_TAC bir_update_blockB_desc_TEMP_VAR_NAMES_DIFFERENT >>
  Q.EXISTS_TAC `BEnv env` >>
  ASM_SIMP_TAC std_ss []
) >>

`?env''. env'' = (env' |+
                    (if use_temp then
                         bir_temp_var_name (bir_var_name var)
                       else bir_var_name var, bir_var_type var,
                       SOME v))` by METIS_TAC[] >>


`bir_exec_stmt_assign (bir_temp_var use_temp var) e st' =
 (st' with bst_environ := BEnv env'')` by (

  `bir_env_lookup (bir_var_name (bir_temp_var use_temp var)) (BEnv env') =
   bir_env_lookup (bir_var_name (bir_temp_var use_temp var)) (BEnv env)` by (
     Q.PAT_X_ASSUM `!vn. _` MATCH_MP_TAC >>
     ASM_REWRITE_TAC[]
  ) >>


  `bir_env_check_type (bir_temp_var use_temp var) (BEnv env') <=>
   bir_env_var_is_declared (BEnv env) (bir_temp_var use_temp var)` by (
    METIS_TAC[bir_env_var_is_declared_def, bir_env_lookup_type_def,
      bir_env_check_type_def]
  ) >>

  `bir_eval_exp e (BEnv env') = bir_eval_exp e (BEnv env)` by (
     MATCH_MP_TAC bir_typing_expTheory.bir_vars_of_exp_THM >>
     REPEAT STRIP_TAC >>
     rename1 `var_other IN _` >>

     `bir_env_lookup (bir_var_name var_other) (BEnv env') =
      bir_env_lookup (bir_var_name var_other) (BEnv env)` by (
        Q.PAT_X_ASSUM `!vn. _` MATCH_MP_TAC >>
        FULL_SIMP_TAC std_ss [bir_update_blockB_desc_OK_def, EVERY_MEM] >>
        METIS_TAC[]
     ) >>
     ASM_SIMP_TAC std_ss [bir_env_read_def]
  ) >>


  ASM_SIMP_TAC std_ss [bir_exec_stmt_assign_def,
    bir_env_write_def, bir_temp_var_REWRS,
    bir_env_update_def, LET_THM]
) >>

FULL_SIMP_TAC (std_ss++holBACore_ss) [DISJ_IMP_THM, FORALL_AND_THM,
  bir_temp_var_REWRS, bir_env_lookup_UPDATE, bir_env_read_UPDATE,
  bir_state_is_terminated_def, EVERY_MEM]);





val bir_update_blockB_SEM2 = prove (``!st c l updates.

(* Now we only update the vars previously stored in a temp value. *)
let updatesT = FILTER bir_updateB_desc_use_temp updates in

(* We start in a non-terminated state *)
~(bir_state_is_terminated st) /\

(* All updates are well-formed and the to the temp var has happened before. *)
(EVERY (\up.
   ~(bir_is_temp_var_name (bir_var_name (bir_updateB_desc_var up))) /\
   (type_of_bir_val (bir_updateB_desc_value up) = SOME (bir_var_type (bir_updateB_desc_var up))) /\
   bir_env_var_is_declared st.bst_environ (bir_updateB_desc_var up) /\
   (bir_env_lookup (bir_var_name (bir_updateB_desc_temp_var up)) st.bst_environ =
      SOME (bir_var_type (bir_updateB_desc_var up), SOME (bir_updateB_desc_value up)))) updatesT) /\

(* We don't update anything twice *)
(ALL_DISTINCT (MAP (\up. bir_var_name (bir_updateB_desc_var up)) updates)) ==> (?st'.

(* Then we terminate successfully ... *)
(bir_exec_stmtsB (MAP bir_update_blockB_STEP2 updatesT) (l, c, st) = (REVERSE l, c + LENGTH updatesT, st')) /\
 ~(bir_state_is_terminated st') /\

(* Every update has been performed *)
EVERY (\up.
   (bir_env_lookup (bir_var_name (bir_updateB_desc_var up)) st'.bst_environ =
      SOME (bir_var_type (bir_updateB_desc_var up), SOME (bir_updateB_desc_value up)))) updatesT /\

(* And all other vars remain unchanged *)
(!vn. (EVERY (\up. vn <> bir_var_name (bir_updateB_desc_var up)) updatesT) ==>
      (bir_env_lookup vn st'.bst_environ = bir_env_lookup vn st.bst_environ)))``,


NTAC 3 GEN_TAC >>
listLib.SNOC_INDUCT_TAC >- (
  SIMP_TAC list_ss [bir_exec_stmtsB_REWRS, LET_THM]
) >>

Cases >>
rename1 `SNOC (BUpdateDescB var e v use_temp) updates` >>
Tactical.REVERSE (Cases_on `use_temp`) >> (
  FULL_SIMP_TAC list_ss [rich_listTheory.FILTER_SNOC, EVERY_SNOC, MAP_SNOC, ALL_DISTINCT_SNOC,
  DISJ_IMP_THM, FORALL_AND_THM, LET_THM, bir_updateB_desc_ACCESSORS,
  bir_updateB_desc_OK_def]
) >>
REPEAT STRIP_TAC >>
FULL_SIMP_TAC list_ss [SNOC_APPEND, bir_exec_stmtsB_APPEND, LET_THM] >>
ASM_SIMP_TAC arith_ss [bir_exec_stmtsB_REWRS, bir_update_blockB_STEP2_def,
  bir_exec_stmtB_def, LET_THM, OPT_CONS_REWRS, DISJ_IMP_THM, FORALL_AND_THM] >>

Cases_on `st.bst_environ` >> rename1 `BEnv env` >>
Cases_on `st'.bst_environ` >> rename1 `st'.bst_environ = BEnv env'` >>


`bir_env_lookup (bir_temp_var_name (bir_var_name var)) (BEnv env') =
 bir_env_lookup (bir_temp_var_name (bir_var_name var)) (BEnv env)` by (
  Q.PAT_X_ASSUM `!vn. _` MATCH_MP_TAC >>
  FULL_SIMP_TAC list_ss [EVERY_MEM] >>
  METIS_TAC[bir_is_temp_var_name_ALT_DEF]
) >>

`!up.
  MEM up (FILTER bir_updateB_desc_use_temp updates) ==>
  bir_var_name var <> bir_var_name (bir_updateB_desc_var up)` by (
  FULL_SIMP_TAC std_ss [MEM_MAP, MEM_FILTER] >>
  METIS_TAC[]
) >>


`bir_env_lookup (bir_var_name var) (BEnv env') =
 bir_env_lookup (bir_var_name var) (BEnv env)` by (
  Q.PAT_X_ASSUM `!vn. _` MATCH_MP_TAC >>
  FULL_SIMP_TAC std_ss [MEM_MAP, EVERY_MEM] >>
  METIS_TAC[]
) >>

`bir_exec_stmt_assign var (BExp_Den (bir_temp_var T var)) st' =
 (st' with bst_environ := BEnv (env' |+ (bir_var_name var,bir_var_type var,SOME v)))` by (

  FULL_SIMP_TAC std_ss [bir_exec_stmt_assign_def, bir_expTheory.bir_eval_exp_def,
    bir_env_read_def, bir_temp_var_REWRS, pairTheory.pair_case_thm,
    LET_THM, bir_env_write_def, bir_env_check_type_def,
    bir_env_var_is_declared_def, bir_env_lookup_type_def,
    bir_env_update_def]
) >>

FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_state_is_terminated_def,
  bir_env_lookup_UPDATE, EVERY_MEM]);




(* Now combine it! This is what we are really interested in. *)
val bir_update_blockB_SEM = store_thm ("bir_update_blockB_SEM", ``!st c l updates.

(* We start with valid updates in a non-terminated state. *)
bir_update_blockB_desc_OK st.bst_environ updates /\
~(bir_state_is_terminated st) ==>

(* Then we terminate in a state ... *)
(?st'. (bir_exec_stmtsB (bir_update_blockB updates) (l, c, st) = (REVERSE l, c + LENGTH (bir_update_blockB updates), st')) /\
  ~(bir_state_is_terminated st') /\

  (* Such that all updates have been performed correctly. *)
  (EVERY (\up. (bir_env_lookup (bir_var_name (bir_updateB_desc_var up)) st'.bst_environ =
                   SOME (bir_var_type (bir_updateB_desc_var up), SOME (bir_updateB_desc_value up))) /\
               (bir_env_lookup (bir_var_name (bir_updateB_desc_temp_var up)) st'.bst_environ =
                   SOME (bir_var_type (bir_updateB_desc_var up), SOME (bir_updateB_desc_value up))))
    updates) /\

  (* And nothing else changed *)
  (!vn. (EVERY (\up. (vn <> bir_var_name (bir_updateB_desc_var up)) /\
                     (vn <> bir_var_name (bir_updateB_desc_temp_var up))) updates) ==>
        (bir_env_lookup vn st'.bst_environ = bir_env_lookup vn st.bst_environ)))``,

REPEAT STRIP_TAC >>
MP_TAC (Q.SPECL [`st`, `c`, `l`, `updates`] bir_update_blockB_SEM1) >>
ASM_SIMP_TAC std_ss [] >> STRIP_TAC >>
ASM_SIMP_TAC list_ss [bir_update_blockB_def, bir_exec_stmtsB_APPEND, LET_THM] >>

MP_TAC (Q.SPECL [`st'`, `c+LENGTH (updates:bir_updateB_desc_t list)`,
  `l`, `updates`] bir_update_blockB_SEM2) >>
MP_TAC (Q.SPECL [`st.bst_environ`, `updates`] bir_update_blockB_desc_OK_VARNAME_UNIQUE) >>
ASM_SIMP_TAC std_ss [LET_THM] >> STRIP_TAC >>
MATCH_MP_TAC (prove (``(A /\ (B ==> C)) ==> ((A ==> B) ==> C)``, PROVE_TAC[])) >>
STRIP_TAC >- (
  FULL_SIMP_TAC std_ss [bir_update_blockB_desc_OK_def, bir_temp_var_REWRS, EVERY_MEM,
    MEM_FILTER] >>
  GEN_TAC >> STRIP_TAC >>
  `bir_updateB_desc_OK st.bst_environ up` by METIS_TAC[] >>
  Cases_on `up` >> rename1 `BUpdateDescB var e v use_temp` >>
  FULL_SIMP_TAC std_ss [bir_updateB_desc_OK_def, bir_updateB_desc_ACCESSORS] >>

  `bir_env_lookup (bir_var_name var) st'.bst_environ =
   bir_env_lookup (bir_var_name var) st.bst_environ` suffices_by (
     FULL_SIMP_TAC std_ss [bir_env_var_is_declared_def, bir_env_lookup_type_def]
  ) >>
  Q.PAT_X_ASSUM `!up. _` MATCH_MP_TAC >>
  Cases >> rename1 `BUpdateDescB var' e' v' use_temp'` >>
  SIMP_TAC std_ss [bir_updateB_desc_ACCESSORS, bir_temp_var_REWRS] >>
  Cases_on `use_temp'` >> REWRITE_TAC[] >- (
    METIS_TAC[bir_is_temp_var_name_ALT_DEF]
  ) >>
  METIS_TAC [bir_updateB_desc_var_def, bir_updateB_desc_t_11]
) >>

STRIP_TAC >>
FULL_SIMP_TAC list_ss [EVERY_MEM, MEM_FILTER] >>
Cases >> rename1 `BUpdateDescB var e v use_temp` >>
STRIP_TAC >> FULL_SIMP_TAC std_ss [bir_updateB_desc_ACCESSORS] >>
`bir_env_lookup (bir_var_name (bir_temp_var use_temp var)) st''.bst_environ =
 bir_env_lookup (bir_var_name (bir_temp_var use_temp var)) st'.bst_environ` by (

  Q.PAT_X_ASSUM `!vn. _` MATCH_MP_TAC >>
  Cases >> rename1 `BUpdateDescB var' e' v' use_temp'` >>
  SIMP_TAC std_ss [bir_updateB_desc_ACCESSORS, bir_temp_var_REWRS, MEM_FILTER] >>
  STRIP_TAC >>
  Cases_on `use_temp` >| [
    METIS_TAC [bir_update_blockB_desc_OK_def, bir_updateB_desc_OK_def, EVERY_MEM, bir_is_temp_var_name_ALT_DEF],
    METIS_TAC[bir_updateB_desc_ACCESSORS, bir_updateB_desc_t_11]
  ]
) >>
METIS_TAC[bir_updateB_desc_ACCESSORS, bir_temp_var_REWRS]);


val _ = export_theory();
