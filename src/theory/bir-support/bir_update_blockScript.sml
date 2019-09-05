open HolKernel Parse boolLib bossLib;
open bir_program_blocksTheory;
open stringTheory finite_mapTheory pred_setTheory
open bir_envTheory listTheory
open bir_programTheory bir_valuesTheory
open bir_typing_expTheory
open bir_auxiliaryTheory bir_expTheory
open bir_bool_expTheory bir_program_env_orderTheory
open bir_temp_varsTheory bir_program_varsTheory
open bir_program_terminationTheory
open bir_typing_progTheory
open bir_program_valid_stateTheory
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
(* Update descriptions      *)
(****************************)

val _ = Datatype `bir_updateB_desc_t = BUpdateDescB bir_var_t bir_exp_t (bir_val_t option) bool`;

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

val bir_vars_of_updateB_desc_def = Define `bir_vars_of_updateB_desc d =
  ((bir_updateB_desc_temp_var d) INSERT
   (bir_updateB_desc_var d) INSERT
   (bir_vars_of_exp (bir_updateB_desc_exp d)))`;

val bir_updateB_desc_ACCESSORS = save_thm ("bir_updateB_desc_ACCESSORS",
  LIST_CONJ [bir_updateB_desc_var_def, bir_updateB_desc_temp_var_def,
             bir_updateB_desc_exp_def, bir_updateB_desc_value_def,
             bir_updateB_desc_use_temp_def]);



val bir_updateB_desc_OK_def = Define `
  bir_updateB_desc_OK env (BUpdateDescB var e v_opt use_temp) <=> (
     (* Types fit *)
     (?v. (v_opt = SOME v) /\
          (type_of_bir_val v = (bir_var_type var))
     ) /\

     (* The varname is not a temp one *)
     (~(bir_is_temp_var_name (bir_var_name var))) /\

     (* Variable and if used the temp var are declared *)
     bir_env_var_is_declared env var /\
     bir_env_var_is_declared env (bir_temp_var use_temp var) /\

     (* The expression really evaluates to the given value *)
     (bir_eval_exp e env = v_opt)
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

val bir_updateB_desc_OK_env_change = store_thm ("bir_updateB_desc_OK_env_change",
``!update env env'.
     bir_env_EQ_FOR_VARS (bir_vars_of_updateB_desc update) env' env ==>
     bir_updateB_desc_OK env update ==>
     bir_updateB_desc_OK env' update``,

Cases >>
rename1 `BUpdateDescB var e v use_temp` >>
SIMP_TAC std_ss [bir_updateB_desc_OK_def,
  bir_env_oldTheory.bir_env_var_is_declared_def, bir_env_lookup_type_def,
  IN_INSERT, DISJ_IMP_THM, FORALL_AND_THM, bir_env_EQ_FOR_VARS_def,
  bir_updateB_desc_ACCESSORS, bir_vars_of_updateB_desc_def] >>
REPEAT STRIP_TAC >>
METIS_TAC[bir_vars_of_exp_THM, bir_env_read_EQ_lookup_IMPL]);


val bir_update_blockB_desc_OK_env_change = store_thm ("bir_update_blockB_desc_OK_env_change",
``!updates env env'.
     ((!update.
          MEM update updates ==>
          bir_env_EQ_FOR_VARS (bir_vars_of_updateB_desc update) env' env) /\

     bir_update_blockB_desc_OK env updates) ==>
     bir_update_blockB_desc_OK env' updates``,

SIMP_TAC std_ss [bir_update_blockB_desc_OK_def, EVERY_MEM,
  IMP_CONJ_THM] >>
REPEAT STRIP_TAC >>
METIS_TAC[bir_updateB_desc_OK_env_change]);



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
          (bir_updateB_desc_value up))) updates) /\

  (* All other vars have still the same value *)
  (!vn. (EVERY (\up. vn <> bir_var_name (bir_updateB_desc_temp_var up)) updates) ==>
        (bir_env_lookup vn st'.bst_environ = bir_env_lookup vn st.bst_environ)))``,


cheat);





val bir_update_blockB_SEM2 = prove (``!st c l updates.

(* Now we only update the vars previously stored in a temp value. *)
let updatesT = FILTER bir_updateB_desc_use_temp updates in

(* We start in a non-terminated state *)
~(bir_state_is_terminated st) /\

(* All updates are well-formed and the to the temp var has happened before. *)
(EVERY (\up.
  (?v.
   ((bir_updateB_desc_value up) = SOME v) /\
   ~(bir_is_temp_var_name (bir_var_name (bir_updateB_desc_var up))) /\
   (type_of_bir_val v = (bir_var_type (bir_updateB_desc_var up))) /\
   bir_env_var_is_declared st.bst_environ (bir_updateB_desc_var up) /\
   (bir_env_lookup (bir_var_name (bir_updateB_desc_temp_var up)) st.bst_environ =
      SOME v))) updatesT) /\

(* We don't update anything twice *)
(ALL_DISTINCT (MAP (\up. bir_var_name (bir_updateB_desc_var up)) updates)) ==> (?st'.

(* Then we terminate successfully ... *)
(bir_exec_stmtsB (MAP bir_update_blockB_STEP2 updatesT) (l, c, st) = (REVERSE l, c + LENGTH updatesT, st')) /\
 ~(bir_state_is_terminated st') /\

(* Every update has been performed *)
EVERY (\up.
   (bir_env_lookup (bir_var_name (bir_updateB_desc_var up)) st'.bst_environ =
      (bir_updateB_desc_value up))) updatesT /\

(* And all other vars remain unchanged *)
(!vn. (EVERY (\up. vn <> bir_var_name (bir_updateB_desc_var up)) updatesT) ==>
      (bir_env_lookup vn st'.bst_environ = bir_env_lookup vn st.bst_environ)))``,


cheat);




(* Now combine it! This is what we are really interested in. *)
val bir_update_blockB_SEM = store_thm ("bir_update_blockB_SEM", ``!st c (l:'a list) updates.

(* We start with valid updates in a non-terminated state. *)
bir_update_blockB_desc_OK st.bst_environ updates /\
~(bir_state_is_terminated st) ==>

(* Then we terminate in a state ... *)
(?st'. (bir_exec_stmtsB (bir_update_blockB updates) (l, c, st) = (REVERSE l, c + LENGTH ((bir_update_blockB updates):'a bir_stmt_basic_t list), st')) /\
  ~(bir_state_is_terminated st') /\

  (* Such that all updates have been performed correctly. *)
  (EVERY (\up. (bir_env_lookup (bir_var_name (bir_updateB_desc_var up)) st'.bst_environ =
                   (bir_updateB_desc_value up)) /\
               (bir_env_lookup (bir_var_name (bir_updateB_desc_temp_var up)) st'.bst_environ =
                   (bir_updateB_desc_value up)))
    updates) /\

  (* And nothing else changed *)
  (!vn. (EVERY (\up. (vn <> bir_var_name (bir_updateB_desc_var up)) /\
                     (vn <> bir_var_name (bir_updateB_desc_temp_var up))) updates) ==>
        (bir_env_lookup vn st'.bst_environ = bir_env_lookup vn st.bst_environ)))``,

cheat);



(****************************)
(* Update End descriptions  *)
(****************************)

(* We need to define what should happen at the end of the block. Either we halt
   or update the the PC somehow. For now, we just consider simple cases, i.e. the
   conditional jump with 2 computed targets is ommited. It can be expressed using
   a simple computed jump anyhow. *)
val _ = Datatype `bir_updateE_desc_t =
   BUpdateDescE_Jmp  bir_label_t
     (* simple, unconditional jump *)
 | BUpdateDescE_CJmp (bir_var_t option) bir_exp_t bool bir_label_t bir_label_t
     (* simple, conditional jump, temp variable might be used to store value of condition *)
 | BUpdateDescE_XJmp (bir_var_t option) bir_exp_t bir_imm_t
     (* something complicated, temp variable might be used to store computed label *)
 | BUpdateDescE_Halt (bir_var_t option) bir_exp_t bir_imm_t
     (* halting *)`;


(* We also need to define the expected behaviour, if run in a certain environment *)
val _ = Datatype `bir_updateE_val_t =
   BUpdateValE_Jmp  bir_label_t (* we jump to some label *)
 | BUpdateValE_Halt bir_imm_t   (* we halt with some value *)`;


val bir_updateE_SEM_def = Define `
   (bir_updateE_SEM (BUpdateDescE_Jmp l) = BUpdateValE_Jmp l) /\
   (bir_updateE_SEM (BUpdateDescE_CJmp _ _ b l1 l2) =
      BUpdateValE_Jmp (if b then l1 else l2)) /\
   (bir_updateE_SEM (BUpdateDescE_XJmp _ _ i) =
      BUpdateValE_Jmp (BL_Address i)) /\
   (bir_updateE_SEM (BUpdateDescE_Halt _ _ v) =
      BUpdateValE_Halt v)`


val bir_state_pc_is_at_label_def = Define `
  bir_state_pc_is_at_label p l_new st =
    (if MEM l_new (bir_labels_of_program p) then
        ((st.bst_pc = bir_block_pc l_new) /\
         (st.bst_status = BST_Running))
     else
        (st.bst_status = BST_JumpOutside l_new))`


val BUpdateValE_SEM_def = Define `
  (BUpdateValE_SEM st p (BUpdateValE_Halt v) =
     (st.bst_status = BST_Halted (BVal_Imm v))) /\
  (BUpdateValE_SEM st p (BUpdateValE_Jmp l_new) =
    (bir_state_pc_is_at_label p l_new st))`

val BUpdateValE_EXEC_def = Define `
  (BUpdateValE_EXEC p (BUpdateValE_Halt v) =
    bir_exec_stmt_halt (BExp_Const v)) /\
  (BUpdateValE_EXEC p (BUpdateValE_Jmp l_new) =
    bir_exec_stmt_jmp_to_label p l_new)`;


val bir_updateE_desc_var_def = Define `
  (bir_updateE_desc_var (BUpdateDescE_Jmp l) = NONE) /\
  (bir_updateE_desc_var (BUpdateDescE_CJmp vo _ _ _ _) = vo) /\
  (bir_updateE_desc_var (BUpdateDescE_XJmp vo _ _) = vo) /\
  (bir_updateE_desc_var (BUpdateDescE_Halt vo _ _) = vo)`;


val bir_updateE_desc_exp_def = Define `
  (bir_updateE_desc_exp (BUpdateDescE_Jmp l) = NONE) /\
  (bir_updateE_desc_exp (BUpdateDescE_CJmp _ c _ _ _) = SOME c) /\
  (bir_updateE_desc_exp (BUpdateDescE_XJmp _ e _) = (SOME e)) /\
  (bir_updateE_desc_exp (BUpdateDescE_Halt _ e _) = SOME e)`;


val bir_updateE_desc_value_def = Define `
  (bir_updateE_desc_value (BUpdateDescE_Jmp _) = NONE) /\
  (bir_updateE_desc_value (BUpdateDescE_CJmp _ _ b _ _) = SOME (bool2b b)) /\
  (bir_updateE_desc_value (BUpdateDescE_XJmp _ _ v) = (SOME v)) /\
  (bir_updateE_desc_value (BUpdateDescE_Halt _ _ v) = SOME v)`;


val bir_updateE_desc_final_exp_def = Define `
  bir_updateE_desc_final_exp d =
    (case (bir_updateE_desc_var d) of
       SOME v => SOME (BExp_Den v)
     | NONE => (case (bir_updateE_desc_exp d) of
       | SOME e => SOME e
       | NONE => NONE))`;

val bir_updateE_desc_final_exp_vars_def = Define `bir_updateE_desc_final_exp_vars d =
  case bir_updateE_desc_final_exp d of
      SOME e => bir_vars_of_exp e
    | NONE => {}`


val bir_updateE_desc_ACCESSORS_IS_SOME = store_thm ("bir_updateE_desc_ACCESSORS_IS_SOME",
  ``(!d. (IS_SOME (bir_updateE_desc_value d) <=> IS_SOME (bir_updateE_desc_exp d))) /\
    (!d. (IS_SOME (bir_updateE_desc_var d) ==> IS_SOME (bir_updateE_desc_exp d))) /\
    (!d. (IS_SOME (bir_updateE_desc_final_exp d) <=> (IS_SOME (bir_updateE_desc_exp d))))``,

SIMP_TAC (std_ss ++ DatatypeSimps.expand_type_quants_ss[``:bir_updateE_desc_t``, ``:'a option``]) [
  bir_updateE_desc_var_def,
  bir_updateE_desc_exp_def,
  bir_updateE_desc_value_def,
  bir_updateE_desc_final_exp_def
]);


val bir_updateE_desc_remove_var_def = Define `
  (bir_updateE_desc_remove_var (BUpdateDescE_Jmp l) = (BUpdateDescE_Jmp l)) /\
  (bir_updateE_desc_remove_var (BUpdateDescE_CJmp vo e b l1 l2) =
     (BUpdateDescE_CJmp NONE e b l1 l2)) /\
  (bir_updateE_desc_remove_var (BUpdateDescE_XJmp vo e i) = (BUpdateDescE_XJmp NONE e i)) /\
  (bir_updateE_desc_remove_var (BUpdateDescE_Halt vo e i) =
     (BUpdateDescE_Halt NONE e i))`;

val bir_updateE_desc_remove_var_REWRS = store_thm ("bir_updateE_desc_remove_var_REWRS",
  ``(!d. bir_updateE_desc_var (bir_updateE_desc_remove_var d) = NONE) /\
    (!d. bir_updateE_desc_exp (bir_updateE_desc_remove_var d) = bir_updateE_desc_exp d) /\
    (!d. bir_updateE_desc_value (bir_updateE_desc_remove_var d) = bir_updateE_desc_value d) /\
    (!d. bir_updateE_desc_final_exp (bir_updateE_desc_remove_var d) = bir_updateE_desc_exp d) /\
    (!d. bir_updateE_SEM (bir_updateE_desc_remove_var d) = bir_updateE_SEM d)``,

REPEAT CONJ_TAC >> Cases >> (
  SIMP_TAC std_ss [bir_updateE_desc_var_def, bir_updateE_desc_exp_def,
                   bir_updateE_desc_value_def, bir_updateE_desc_final_exp_def,
                   bir_updateE_desc_remove_var_def, bir_updateE_SEM_def]
));


val bir_updateE_desc_OK_def = Define `
  bir_updateE_desc_OK env d <=> (
     (!e v. ((bir_updateE_desc_exp d = SOME e) /\ (bir_updateE_desc_value d = SOME v)) ==>
            (type_of_bir_exp e = SOME (BType_Imm (type_of_bir_imm v))) /\
            (bir_eval_exp e env = SOME (BVal_Imm v))) /\

     (!e var. ((bir_updateE_desc_var d = SOME var) /\ (bir_updateE_desc_exp d = SOME e)) ==>
              (type_of_bir_exp e = SOME (bir_var_type var)) /\
              bir_env_var_is_declared env var)
  )`;

val bir_updateE_desc_OK_remove_var = store_thm ("bir_updateE_desc_OK_remove_var",
 ``!d env. bir_updateE_desc_OK env d ==> bir_updateE_desc_OK env (bir_updateE_desc_remove_var d)``,
Cases >> (
  SIMP_TAC std_ss [bir_updateE_desc_OK_def, bir_updateE_desc_remove_var_REWRS]
));


val bir_update_block_desc_OK_def = Define `
  bir_update_block_desc_OK env eup updates <=> (

  bir_update_blockB_desc_OK env updates /\
  bir_updateE_desc_OK env eup /\

  (!v up v'. (bir_updateE_desc_var eup = SOME v) ==>
             (MEM up updates) ==>
             (v' IN (bir_vars_of_updateB_desc up)) ==>
             ((bir_var_name v <> bir_var_name v'))) /\

  (!v e up v'. (bir_updateE_desc_var eup = NONE) ==>
               (bir_updateE_desc_exp eup = SOME e) ==>
               (v IN bir_vars_of_exp e) ==>
               MEM up updates ==>
               (v' IN {bir_updateB_desc_temp_var up; bir_updateB_desc_var up}) ==>
               ((bir_var_name v <> bir_var_name v'))))`;


val bir_update_blockE_INIT_def = Define `
  (bir_update_blockE_INIT d =
   case (bir_updateE_desc_var d, bir_updateE_desc_exp d) of
     | (SOME v, SOME e) => [BStmt_Assign v e]
     | (_, _) => [])`;


val bir_update_blockE_FINAL_def = Define `
  (bir_update_blockE_FINAL (BUpdateDescE_Jmp l) = BStmt_Jmp (BLE_Label l)) /\
  (bir_update_blockE_FINAL (BUpdateDescE_CJmp vo e _ l1 l2) = BStmt_CJmp
    (option_CASE vo e (\v. BExp_Den v)) (BLE_Label l1) (BLE_Label l2)) /\
  (bir_update_blockE_FINAL (BUpdateDescE_XJmp vo e i) = BStmt_Jmp (BLE_Exp
    (option_CASE vo e (\v. BExp_Den v)))) /\
  (bir_update_blockE_FINAL (BUpdateDescE_Halt vo e _) = BStmt_Halt (option_CASE vo e (\v. BExp_Den v)))`


val bir_update_blockE_FINAL_THM = store_thm ("bir_update_blockE_FINAL_THM",
``!d p st.
    (!e v. ((bir_updateE_desc_final_exp d) = SOME e) ==>
           ((bir_updateE_desc_value d) = SOME v) ==>
           (bir_eval_exp e st.bst_environ = SOME (BVal_Imm v))) ==>

(bir_exec_stmtE p (bir_update_blockE_FINAL d) st =
 BUpdateValE_EXEC p (bir_updateE_SEM d) st)``,

SIMP_TAC (std_ss ++ DatatypeSimps.expand_type_quants_ss[``:bir_updateE_desc_t``, ``:'a option``]) [
  bir_updateE_desc_final_exp_def, bir_updateE_desc_var_def,
  bir_updateE_desc_value_def, bir_updateE_desc_exp_def,
  bir_update_blockE_FINAL_def, bir_exec_stmtE_def,
  bir_updateE_SEM_def, BUpdateValE_EXEC_def,
  bir_exec_stmt_halt_def, bir_eval_exp_def,
  bir_exec_stmt_cjmp_def, bir_dest_bool_val_bool2b,
  bir_exec_stmt_jmp_def, bir_eval_label_exp_def, LET_DEF] >>
SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss++holBACore_ss) []);


val bir_update_block_def = Define `bir_update_block l eup updates =
  (<|
    bb_label          := l;
    bb_statements     := bir_update_blockE_INIT eup ++ bir_update_blockB updates;
    bb_last_statement := bir_update_blockE_FINAL eup|>)`;



val bir_update_blockE_INIT_SEM = store_thm ("bir_update_blockE_INIT_SEM", ``
 !st eup (l:'a list) c.
    bir_updateE_desc_OK st.bst_environ eup /\
    ~(bir_state_is_terminated st) ==>
    (?st'. (bir_exec_stmtsB (bir_update_blockE_INIT eup) (l,c,st) =
           (REVERSE l, c + LENGTH ((bir_update_blockE_INIT eup) : ('a bir_stmt_basic_t) list), st')) /\

          ~(bir_state_is_terminated st') /\
          (st'.bst_pc = st.bst_pc) /\
          (!var v. (bir_updateE_desc_var eup = SOME var) ==>
                   (bir_updateE_desc_value eup = SOME v) ==>
                   ((bir_env_lookup (bir_var_name var) st'.bst_environ =
                      SOME (BVal_Imm v)))) /\

          (!vn. (!var. (bir_updateE_desc_var eup = SOME var) ==> (bir_var_name var <> vn)) ==>
               (bir_env_lookup vn st'.bst_environ = bir_env_lookup vn st.bst_environ)))``,

REPEAT STRIP_TAC >>
SIMP_TAC std_ss [bir_update_blockE_INIT_def] >>
Cases_on `bir_updateE_desc_var eup` >- (
  (* No var, it is a skip *)
  ASM_SIMP_TAC list_ss [pairTheory.pair_case_thm, bir_exec_stmtsB_REWRS]
) >>
rename1 `_ = SOME var` >>
`(?e. bir_updateE_desc_exp eup = SOME e) /\
 (?v. bir_updateE_desc_value eup = SOME v)` by METIS_TAC[
   bir_updateE_desc_ACCESSORS_IS_SOME,
   optionTheory.IS_SOME_EXISTS] >>
ASM_SIMP_TAC list_ss [pairTheory.pair_case_thm, bir_exec_stmtsB_REWRS,
  bir_exec_stmtB_def, LET_THM, OPT_CONS_REWRS] >>
FULL_SIMP_TAC std_ss [bir_updateE_desc_OK_def] >>
Cases_on `st.bst_environ` >>
rename1 `BEnv env` >>
FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_exec_stmt_assign_def,
  bir_env_write_def, GSYM bir_env_oldTheory.bir_env_var_is_declared_ALT_DEF,
  bir_env_update_def, type_of_bir_val_def, LET_THM,
  bir_env_lookup_UPDATE, bir_state_is_terminated_def] >>
cheat);





val bir_update_block_SEM = store_thm ("bir_update_block_SEM", ``!st l eup (p : 'a bir_program_t) updates (bl:'a bir_block_t).

(* We start with valid updates in a non-terminated state. *)
bir_update_block_desc_OK st.bst_environ eup updates /\
(bl = (bir_update_block l eup updates)) ==>
~(bir_state_is_terminated st) ==>

(* Then we terminate in a state ... *)
(?st'. (bir_exec_block p bl st = (([]:'a list), bir_block_size bl, st')) /\

  (* Such that we are either
      - running and jumped to the intended label
      - stopped because the intended label does not exist
      - halted with the intended exit code
  *)
  (BUpdateValE_SEM st' p (bir_updateE_SEM eup)) /\

  (* All updates have been performed correctly. *)
  (EVERY (\up. (bir_env_lookup (bir_var_name (bir_updateB_desc_var up)) st'.bst_environ =
                   (bir_updateB_desc_value up)) /\
               (bir_env_lookup (bir_var_name (bir_updateB_desc_temp_var up)) st'.bst_environ =
                   (bir_updateB_desc_value up)))
    updates) /\
  (!var v. (bir_updateE_desc_var eup = SOME var) ==>
           (bir_updateE_desc_value eup = SOME v) ==>
           ((bir_env_lookup (bir_var_name var) st'.bst_environ =
            SOME (BVal_Imm v)))) /\

  (* And nothing else changed *)
  (!vn. (EVERY (\up. (vn <> bir_var_name (bir_updateB_desc_var up)) /\
                     (vn <> bir_var_name (bir_updateB_desc_temp_var up))) updates) ==>
        (!var. (bir_updateE_desc_var eup = SOME var) ==> (bir_var_name var <> vn)) ==>
        (bir_env_lookup vn st'.bst_environ = bir_env_lookup vn st.bst_environ)))``,


cheat);



(********************)
(* Assertion Blocks *)
(********************)


val _ = Datatype `bir_assert_desc_t = BAssertDesc bir_exp_t bool`;

val bir_assert_desc_OK_def = Define `
  bir_assert_desc_OK env (BAssertDesc e b) <=> (
     (* The expression really evaluates to the given value *)
     (bir_eval_exp e env = SOME (BVal_Imm (bool2b b)))
  )`

val bir_assert_desc_exp_def = Define `bir_assert_desc_exp (BAssertDesc e b) = e`;
val bir_assert_desc_value_def = Define `bir_assert_desc_value (BAssertDesc e b) = b`;


val bir_assert_block_def = Define `
  bir_assert_block al = MAP (\a. BStmt_Assert (bir_assert_desc_exp a)) al`;


val bir_assert_block_SEM = store_thm ("bir_assert_block_SEM", ``!st al l.
  EVERY (bir_assert_desc_OK st.bst_environ) al ==>
  ~(bir_state_is_terminated st) ==>

  (!c.
  (bir_exec_stmtsB (bir_assert_block al) (l, c, st) =
  (case INDEX_FIND 0 (\a. ~(bir_assert_desc_value a)) al of
     | NONE        => (REVERSE l, c + LENGTH al, st)
     | SOME (n, _) => (REVERSE l, c + SUC n, (st with bst_status := BST_AssertionViolated)))))``,


REPEAT GEN_TAC >> REPEAT DISCH_TAC >>
Induct_on `al` >- (
  SIMP_TAC list_ss [INDEX_FIND_def, bir_assert_block_def,
    bir_exec_stmtsB_REWRS]
) >>
REPEAT STRIP_TAC >>
rename1 `a::al` >>
FULL_SIMP_TAC list_ss [bir_assert_block_def,
  bir_exec_stmtsB_REWRS, bir_exec_stmtB_def,
  LET_THM, OPT_CONS_REWRS] >>
`bir_exec_stmt_assert (bir_assert_desc_exp a) st =
  (if bir_assert_desc_value a then st else (st with bst_status := BST_AssertionViolated))` by (
  Cases_on `a` >>
  FULL_SIMP_TAC std_ss [bir_assert_desc_OK_def,
    bir_assert_desc_value_def, bir_assert_desc_exp_def,
    bir_exec_stmt_assert_def, bir_dest_bool_val_bool2b]
) >>
Tactical.REVERSE (Cases_on `bir_assert_desc_value a`) >- (
  `bir_state_is_terminated (st with bst_status := BST_AssertionViolated)` by
     SIMP_TAC (std_ss++bir_TYPES_ss) [bir_state_is_terminated_def, bir_state_set_typeerror_def] >>
  FULL_SIMP_TAC list_ss [INDEX_FIND_def, pairTheory.pair_case_thm,
    bir_exec_stmtsB_REWRS]
) >>
FULL_SIMP_TAC std_ss [INDEX_FIND_def, Q.SPEC `1` INDEX_FIND_INDEX_CHANGE] >>
CASE_TAC >> SIMP_TAC (arith_ss++pairSimps.gen_beta_ss) [pairTheory.pair_CASE_def]);



val bir_assert_block_SEM_NOT_FAIL = store_thm ("bir_assert_block_SEM_NOT_FAIL", ``
  !st al (l:'a list) c l' c' st'.
  EVERY (bir_assert_desc_OK st.bst_environ) al ==>
  ~(bir_state_is_terminated st) ==>
  (bir_exec_stmtsB (bir_assert_block al) (l, c, st) = (l', c', st')) ==>
  ~(st'.bst_status = BST_AssertionViolated) ==>

  ((l' = REVERSE l) /\
   (c' = c + LENGTH al) /\
   (st' = st) /\
   (EVERY (\a. bir_assert_desc_value a) al))``,

SIMP_TAC std_ss [bir_assert_block_SEM] >>
REPEAT GEN_TAC >>
CASE_TAC >> (
  FULL_SIMP_TAC list_ss [INDEX_FIND_EQ_NONE, combinTheory.o_DEF,
    pairTheory.pair_CASE_def]
) >>
REPEAT DISCH_TAC >>
FULL_SIMP_TAC std_ss [] >>
REPEAT BasicProvers.VAR_EQ_TAC >>
FULL_SIMP_TAC (std_ss++bir_TYPES_ss) []);


val bir_assert_block_SEM_NOT_FAIL_BLOCK = store_thm ("bir_assert_block_SEM_NOT_FAIL_BLOCK", ``
  !al bl (p : 'a bir_program_t) (l:'a list) c st st'.
  EVERY (bir_assert_desc_OK st.bst_environ) al ==>
  ~(bir_state_is_terminated st) ==>
  (bir_exec_block p (bl with bb_statements := (bir_assert_block al) ++ bl.bb_statements) st = (l, c, st')) ==>
  ~(st'.bst_status = BST_AssertionViolated) ==>

  ((LENGTH al < c) /\
  (bir_exec_block p bl st = (l, c - LENGTH al,
     if (bir_state_is_terminated st') then
        (st' with bst_pc := (st'.bst_pc with bpc_index := st'.bst_pc.bpc_index - LENGTH al))
     else st')) /\
  (EVERY (\a. bir_assert_desc_value a) al))``,

SIMP_TAC (std_ss++bir_TYPES_ss) [bir_exec_block_def,
  bir_exec_stmtsB_APPEND] >>
REPEAT GEN_TAC >>
`?l' c' st''. bir_exec_stmtsB (bir_assert_block al) (([]:'a list),0,st) = (l', c', st'')` by
  METIS_TAC[pairTheory.PAIR] >>
`?l'' c'' st'''.  bir_exec_stmtsB bl.bb_statements ([],0,st) = (l'', c'', st''')` by
  METIS_TAC[pairTheory.PAIR] >>
ASM_SIMP_TAC std_ss [] >>
ONCE_ASM_REWRITE_TAC[bir_exec_stmtsB_RESET_ACCUMULATOR_COUNTER] >>
Cases_on `st''.bst_status = BST_AssertionViolated` >- (
  `bir_state_is_terminated st''` by (
    FULL_SIMP_TAC (std_ss++bir_TYPES_ss) [bir_state_is_terminated_def]
  ) >>
  ASM_SIMP_TAC list_ss [bir_exec_stmtsB_REWRS, LET_THM] >>
  REPEAT DISCH_TAC >> FULL_SIMP_TAC std_ss [] >> REPEAT BasicProvers.VAR_EQ_TAC >>
  FULL_SIMP_TAC (std_ss++bir_TYPES_ss) []
) >>
NTAC 2 DISCH_TAC >>
MP_TAC (Q.SPECL [`st`, `al`, `[]:'a list`, `0`] bir_assert_block_SEM_NOT_FAIL) >>
ASM_SIMP_TAC list_ss [LET_THM] >>
STRIP_TAC >> REPEAT (BasicProvers.VAR_EQ_TAC) >>
Tactical.REVERSE (Cases_on `bir_state_is_terminated st'''`) >- (
   ASM_SIMP_TAC arith_ss [] >>
   STRIP_TAC >> STRIP_TAC >>
   Cases_on `bir_state_is_terminated
           (bir_exec_stmtE p bl.bb_last_statement st''')` >> (
     FULL_SIMP_TAC std_ss [] >>
     REPEAT BasicProvers.VAR_EQ_TAC >>
     FULL_SIMP_TAC (std_ss++bir_TYPES_ss) [bir_state_is_terminated_def] >>
     ASM_SIMP_TAC (arith_ss++bir_TYPES_ss) [bir_state_t_component_equality,
       bir_programcounter_t_component_equality]
   )
) >>
ASM_SIMP_TAC std_ss [] >>
STRIP_TAC >> STRIP_TAC >> REPEAT BasicProvers.VAR_EQ_TAC >>
FULL_SIMP_TAC (arith_ss++bir_TYPES_ss) [bir_state_is_terminated_def,
  bir_state_t_component_equality, bir_programcounter_t_component_equality] >>
Cases_on `c''` >- (
  `(st''' = st)` by METIS_TAC[bir_exec_stmtsB_COUNTER_EQ] >>
  METIS_TAC[]
) >>
SIMP_TAC arith_ss []);



(*****************************)
(* Combine update and assert *)
(*****************************)


val bir_update_assert_block_def = Define `bir_update_assert_block l al eup updates =
  (<|
    bb_label          := l;
    bb_statements     := bir_assert_block al ++ bir_update_blockE_INIT eup ++ bir_update_blockB updates;
    bb_last_statement := bir_update_blockE_FINAL eup|>)`;


val bir_update_assert_block_ALT_def = store_thm ("bir_update_assert_block_ALT_def",
  ``((bir_update_assert_block l al eup updates):'a bir_block_t) =
    (bir_update_block l eup updates):'a bir_block_t with bb_statements := (bir_assert_block al ++ (bir_update_block l eup updates).bb_statements)``,
SIMP_TAC (list_ss++bir_TYPES_ss) [bir_update_assert_block_def, bir_update_block_def, bir_block_t_component_equality]);


val bir_update_assert_block_SEM = store_thm ("bir_update_assert_block_SEM", ``!st l eup (p : 'a bir_program_t) updates bl al lo n' st'.

(* We start with valid updates and asserts in a non-terminated state. *)
EVERY (bir_assert_desc_OK st.bst_environ) al ==>
bir_update_block_desc_OK st.bst_environ eup updates ==>
(bl = (bir_update_assert_block l al eup updates)) ==>
~(bir_state_is_terminated st) ==>
(bir_exec_block p bl st = (lo:'a list, n', st')) ==>
~(st'.bst_status = BST_AssertionViolated) ==> (

(* Then we terminate in a state ... *)
  ((lo = []) /\ (n' = bir_block_size bl)) /\
  (EVERY (\a. bir_assert_desc_value a) al) /\

  (* Such that we are either
      - running and jumped to the intended label
      - stopped because the intended label does not exist
      - halted with the intended exit code
  *)
  (BUpdateValE_SEM st' p (bir_updateE_SEM eup)) /\

  (* All updates have been performed correctly. *)
  (EVERY (\up. (bir_env_lookup (bir_var_name (bir_updateB_desc_var up)) st'.bst_environ =
                   (bir_updateB_desc_value up)) /\
               (bir_env_lookup (bir_var_name (bir_updateB_desc_temp_var up)) st'.bst_environ =
                   (bir_updateB_desc_value up)))
    updates) /\
  (!var v. (bir_updateE_desc_var eup = SOME var) ==>
           (bir_updateE_desc_value eup = SOME v) ==>
           ((bir_env_lookup (bir_var_name var) st'.bst_environ =
            SOME (BVal_Imm v)))) /\

  (* And nothing else changed *)
  (!vn. (EVERY (\up. (vn <> bir_var_name (bir_updateB_desc_var up)) /\
                     (vn <> bir_var_name (bir_updateB_desc_temp_var up))) updates) ==>
        (!var. (bir_updateE_desc_var eup = SOME var) ==> (bir_var_name var <> vn)) ==>
        (bir_env_lookup vn st'.bst_environ = bir_env_lookup vn st.bst_environ)))``,


REPEAT GEN_TAC >> REPEAT DISCH_TAC >>
REPEAT BasicProvers.VAR_EQ_TAC >>
Q.ABBREV_TAC `bl' = bir_update_block l eup updates` >>
MP_TAC (Q.SPECL [`al`, `bl'`, `p`, `lo`, `n'`, `st`] bir_assert_block_SEM_NOT_FAIL_BLOCK) >>
FULL_SIMP_TAC std_ss [bir_update_assert_block_ALT_def] >>
STRIP_TAC >>

MP_TAC (Q.SPECL [`st`, `l`, `eup`, `p:'a bir_program_t`, `updates`] bir_update_block_SEM) >>
ASM_SIMP_TAC std_ss [] >>
STRIP_TAC >>
FULL_SIMP_TAC std_ss [] >>
Q.ABBREV_TAC `st'' = (if bir_state_is_terminated st' then
                  st' with bst_pc :=
                    st'.bst_pc with
                    bpc_index := st'.bst_pc.bpc_index − LENGTH al
                else st')` >>
`(st''.bst_environ = st'.bst_environ)` by (
   Q.UNABBREV_TAC `st''` >>
   Cases_on `bir_state_is_terminated st'` >> ASM_SIMP_TAC (std_ss++bir_TYPES_ss) []
) >>
FULL_SIMP_TAC (list_ss++bir_TYPES_ss) [bir_block_size_def, bir_assert_block_def] >>
Q.UNABBREV_TAC `st''` >>
Tactical.REVERSE(Cases_on `bir_state_is_terminated st'`) >> FULL_SIMP_TAC std_ss [] >>

Cases_on `bir_updateE_SEM eup` >> FULL_SIMP_TAC (std_ss++bir_TYPES_ss) [BUpdateValE_SEM_def] >>
FULL_SIMP_TAC (std_ss++bir_TYPES_ss) [bir_state_pc_is_at_label_def, bir_state_is_terminated_def]);


(****************)
(* Changed_vars *)
(****************)


val bir_changed_vars_of_update_block = store_thm ("bir_changed_vars_of_update_block",
``bir_changed_vars_of_block (bir_update_block l eup dl) =

  (case bir_updateE_desc_var eup of SOME v => {v} | _ => {}) UNION
  (set (MAP bir_updateB_desc_var dl)) UNION
  (set (MAP bir_updateB_desc_temp_var (FILTER bir_updateB_desc_use_temp dl)))``,

SIMP_TAC (list_ss++bir_TYPES_ss) [bir_changed_vars_of_block_def, bir_update_block_def,
  GSYM LIST_TO_SET_MAP, bir_update_blockE_INIT_def, bir_update_blockB_def,
  BIGUNION_UNION, GSYM UNION_ASSOC] >>
MATCH_MP_TAC (prove (``(S1 = S1') /\ (S2 = S2') ==> (S1 UNION S2 = S1' UNION S2')``,
    PROVE_TAC[])) >>

REPEAT STRIP_TAC >- (
  Cases_on `bir_updateE_desc_var eup` >- (
    SIMP_TAC list_ss [bir_updateE_desc_var_def, bir_updateE_desc_exp_def,
      pairTheory.pair_CASE_def, BIGUNION_EMPTY]
  ) >>
  `IS_SOME (bir_updateE_desc_exp eup)` by METIS_TAC[bir_updateE_desc_ACCESSORS_IS_SOME,
     optionTheory.IS_SOME_EXISTS] >>
  FULL_SIMP_TAC list_ss [optionTheory.IS_SOME_EXISTS, pairTheory.pair_CASE_def,
    bir_changed_vars_of_stmtB_def, BIGUNION_INSERT, BIGUNION_EMPTY, UNION_EMPTY]
) >>
Induct_on `dl` >- (
  SIMP_TAC list_ss [BIGUNION_EMPTY, UNION_EMPTY]
) >>
Cases >>
SIMP_TAC (list_ss++boolSimps.LIFT_COND_ss) [bir_changed_vars_of_stmtB_def,
  bir_update_blockB_STEP1_def, BIGUNION_INSERT,
  bir_update_blockB_STEP2_def, bir_updateB_desc_var_def,
   bir_updateB_desc_temp_var_def, bir_updateB_desc_use_temp_def] >>
FULL_SIMP_TAC std_ss [EXTENSION] >>
FULL_SIMP_TAC (std_ss++boolSimps.EQUIV_EXTRACT_ss) [IN_UNION, IN_INSERT, NOT_IN_EMPTY, bir_temp_var_REWRS]);


val bir_changed_vars_of_update_assert_block_AUX = prove (
``bir_changed_vars_of_block (((bir_update_assert_block l al eup dl)):'a bir_block_t) =
  bir_changed_vars_of_block ((bir_update_block l eup dl):'a bir_block_t)``,

SIMP_TAC (list_ss++bir_TYPES_ss) [bir_changed_vars_of_block_def, bir_update_block_def,
  bir_update_assert_block_def, IMAGE_UNION, BIGUNION_UNION] >>
SIMP_TAC (std_ss++boolSimps.EQUIV_EXTRACT_ss) [EXTENSION, IN_UNION] >>
SIMP_TAC list_ss [bir_assert_block_def, GSYM listTheory.LIST_TO_SET_MAP,
  MAP_MAP_o, combinTheory.o_DEF, bir_changed_vars_of_stmtB_def] >>
SIMP_TAC std_ss [listTheory.LIST_TO_SET_MAP, IN_BIGUNION_IMAGE, NOT_IN_EMPTY]);


val bir_changed_vars_of_update_assert_block = store_thm("bir_changed_vars_of_update_assert_block",
``bir_changed_vars_of_block (((bir_update_assert_block l al eup dl)):'a bir_block_t) =
  (case bir_updateE_desc_var eup of SOME v => {v} | _ => {}) UNION
  (set (MAP bir_updateB_desc_var dl)) UNION
  (set (MAP bir_updateB_desc_temp_var (FILTER bir_updateB_desc_use_temp dl)))``,

SIMP_TAC std_ss [bir_changed_vars_of_update_assert_block_AUX,
  bir_changed_vars_of_update_block]);


val _ = export_theory();
