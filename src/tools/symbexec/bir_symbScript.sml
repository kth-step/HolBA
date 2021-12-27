open HolKernel Parse boolLib bossLib;

open symb_interpretTheory;
open symb_recordTheory;
open symb_record_soundTheory;

open bir_valuesTheory;
open bir_expTheory;
open bir_envTheory;
open bir_programTheory;
open bir_typing_expTheory;

open bir_bool_expTheory;
open bir_exp_substitutionsTheory;
open bir_typing_expTheory;

open bir_symb_supportTheory;

open finite_mapTheory;
open pred_setTheory;
open listTheory;
open combinTheory;
open optionTheory;

open HolBACoreSimps;
open symb_typesLib;

open pred_setSimps;
open listSimps;

val _ = new_theory "bir_symb";

(*
DEFINITIONS: INSTANTIATION FOR BIR/SBIR
=======================================================
*)
(*
- 'a_label    = bir_programcounter_t
- 'b_var      = string
- 'c_val      = bir_val_t
- 'd_extra    = bir_status_t

- 'e_symbol   = bir_var_t
- 'f_symbexpr = bir_exp_t
- 'g_type     = bir_type_t
*)
(*
"bir_concst_t = (bir_programcounter_t, string, bir_val_t, bir_status_t) symb_concst_t"
"bir_symbst_t = (bir_programcounter_t, string, bir_exp_t, bir_status_t) symb_symbst_t"
*)


(* functions to convert between conrete states *)
(* TODO: have to add observation in symbolic execution, could have this for another instance also?! no, probably not useful to split this *)
val birs_symb_to_concst_def = Define `
    birs_symb_to_concst s =
      (SymbConcSt
        s.bst_pc
        (\bvn. bir_env_lookup bvn s.bst_environ)
        s.bst_status)
`;

val birs_symb_from_concst_def = Define `
    birs_symb_from_concst (SymbConcSt lbl env status) =
      <|
        bst_pc       := lbl;
        bst_environ  := BEnv env;
        bst_status   := status
      |>
`;


val bir_env_lookup_I_thm = store_thm(
   "bir_env_lookup_I_thm", ``
!env. (\bvn. bir_env_lookup bvn (BEnv env)) = env
``,
  FULL_SIMP_TAC (std_ss++holBACore_ss)
    [bir_env_lookup_def] >>
  METIS_TAC []
);

val bir_env_lookup_BEnv_thm = store_thm(
   "bir_env_lookup_BEnv_thm", ``
!env. BEnv (\bvn. bir_env_lookup bvn env) = env
``,
  Cases_on `env` >>
  FULL_SIMP_TAC (std_ss++holBACore_ss)
    [bir_env_lookup_I_thm]
);

val bir_env_lookup_BIJ_thm = store_thm(
   "bir_env_lookup_BIJ_thm", ``
!env1 env2.
  ((\bvn. bir_env_lookup bvn env1) = (\bvn. bir_env_lookup bvn env2)) ==>
  (env1 = env2)
``,
  Cases_on `env1` >> Cases_on `env2` >>
  FULL_SIMP_TAC (std_ss++holBACore_ss)
      [bir_env_lookup_I_thm]
);

val birs_symb_from_to_concst_thm = store_thm(
   "birs_symb_from_to_concst_thm", ``
!s. birs_symb_to_concst (birs_symb_from_concst s) = s
``,
  GEN_TAC >>
  Cases_on `s` >>
  FULL_SIMP_TAC (std_ss++symb_TYPES_ss++holBACore_ss)
    [birs_symb_to_concst_def, birs_symb_from_concst_def, bir_env_lookup_def] >>

  METIS_TAC []
);

val birs_symb_to_from_concst_thm = store_thm(
   "birs_symb_to_from_concst_thm", ``
!s. birs_symb_from_concst (birs_symb_to_concst s) = s
``,
  GEN_TAC >>
  Cases_on `s` >>

  FULL_SIMP_TAC (std_ss++symb_TYPES_ss++holBACore_ss)
    [birs_symb_to_concst_def, birs_symb_from_concst_def, bir_env_lookup_BEnv_thm] >>

  Q.ABBREV_TAC `s = <|bst_pc := b; bst_environ := b0; bst_status := b1|>` >>
  `s.bst_pc = b /\
   s.bst_environ = b0 /\
   s.bst_status = b1` by (
    Q.UNABBREV_TAC `s` >>
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >>

  Cases_on `s` >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) []
);

val birs_symb_to_concst_EXISTS_thm = store_thm(
   "birs_symb_to_concst_EXISTS_thm", ``
!s. ?st. birs_symb_to_concst st = s
``,
  METIS_TAC [birs_symb_from_to_concst_thm]
);

val birs_symb_from_concst_EXISTS_thm = store_thm(
   "birs_symb_from_concst_EXISTS_thm", ``
!s. ?st. birs_symb_from_concst st = s
``,
  METIS_TAC [birs_symb_to_from_concst_thm]
);

val birs_symb_to_concst_BIJ_thm = store_thm(
   "birs_symb_to_concst_BIJ_thm", ``
!s1 s2.
  (birs_symb_to_concst s1 = birs_symb_to_concst s2) ==>
  (s1 = s2)
``,
  REPEAT GEN_TAC >>
  Cases_on `s1` >> Cases_on `s2` >>

  FULL_SIMP_TAC (std_ss++symb_TYPES_ss++holBACore_ss)
    [birs_symb_to_concst_def, bir_env_lookup_BIJ_thm]
);

(* sr_step_conc is in principle "bir_exec_step" *)


(* sr_step_symb, must define "birs_exec_step" first *)

(* first some general functions to deal with symbolic expressions (symbolic evaluation and interpretation) *)
val birs_eval_exp_subst_var_def = Define `
    birs_eval_exp_subst_var x senv =
      option_CASE (senv (bir_var_name x)) (BExp_Den x) (I)
(*
      case senv (bir_var_name x) of
       | SOME x_ex => x_ex
       | NONE => BExp_Den x
*)
`;
val birs_eval_exp_subst_def = Define `
   (birs_eval_exp_subst (BExp_Const n) senv = (BExp_Const n)) /\
   (birs_eval_exp_subst (BExp_MemConst aty vty mmap) senv = (BExp_MemConst aty vty mmap)) /\
   (birs_eval_exp_subst (BExp_Den v) senv = birs_eval_exp_subst_var v senv) /\
   (birs_eval_exp_subst (BExp_Cast ct e ty) senv =
      BExp_Cast ct
        (birs_eval_exp_subst e senv) ty) /\
   (birs_eval_exp_subst (BExp_UnaryExp et e) senv =
      BExp_UnaryExp et
        (birs_eval_exp_subst e senv)) /\
   (birs_eval_exp_subst (BExp_BinExp et e1 e2) senv =
      BExp_BinExp et
        (birs_eval_exp_subst e1 senv)
        (birs_eval_exp_subst e2 senv)) /\
   (birs_eval_exp_subst (BExp_BinPred pt e1 e2) senv =
      BExp_BinPred pt
        (birs_eval_exp_subst e1 senv)
        (birs_eval_exp_subst e2 senv)) /\
   (birs_eval_exp_subst (BExp_MemEq me1 me2) senv =
      BExp_MemEq
        (birs_eval_exp_subst me1 senv)
        (birs_eval_exp_subst me2 senv)) /\
   (birs_eval_exp_subst (BExp_IfThenElse c et ef) senv =
      BExp_IfThenElse
        (birs_eval_exp_subst c senv)
        (birs_eval_exp_subst et senv)
        (birs_eval_exp_subst ef senv)) /\
   (birs_eval_exp_subst (BExp_Load mem_e a_e en ty) senv =
      BExp_Load
        (birs_eval_exp_subst mem_e senv)
        (birs_eval_exp_subst a_e senv)
        en
        ty) /\
   (birs_eval_exp_subst (BExp_Store mem_e a_e en v_e) senv =
      BExp_Store
        (birs_eval_exp_subst mem_e senv)
        (birs_eval_exp_subst a_e senv)
        en
        (birs_eval_exp_subst v_e senv))
`;
val birs_eval_exp_subst_ALT_def = Define `
    birs_eval_exp_subst_ALT e senv =
      bir_exp_subst
        (FUN_FMAP
          (\x. birs_eval_exp_subst_var x senv)
          (bir_vars_of_exp e))
        e
`;

(* TODO: this should go to bir_symb_support *)
val bir_exp_subst_FUN_FMAP_bir_vars_of_exp_thm = store_thm(
   "bir_exp_subst_FUN_FMAP_bir_vars_of_exp_thm", ``
!e X Y.
  (FINITE Y) ==>
  (bir_exp_subst
    (FUN_FMAP X (bir_vars_of_exp e UNION Y))
    e
   =
   bir_exp_subst
    (FUN_FMAP X (bir_vars_of_exp e))
    e)
``,
  Induct_on `e` >> (
    SIMP_TAC (std_ss)
      ([birs_eval_exp_subst_def, birs_eval_exp_subst_ALT_def, bir_exp_subst_def]@
       [bir_vars_of_exp_def, bir_exp_subst_var_def, FLOOKUP_FUN_FMAP,
        IN_SING, FINITE_SING, IN_UNION, FINITE_UNION])
  ) >> (
    REPEAT STRIP_TAC >>
    `FINITE (bir_vars_of_exp e' ∪ Y) /\
     FINITE (bir_vars_of_exp e ∪ Y) /\
     FINITE (bir_vars_of_exp e) /\
     FINITE (bir_vars_of_exp e') /\

     FINITE (bir_vars_of_exp e' ∪ bir_vars_of_exp e'' ∪ Y) /\
     FINITE (bir_vars_of_exp e' ∪ bir_vars_of_exp e'') /\
     FINITE (bir_vars_of_exp e ∪ bir_vars_of_exp e'' ∪ Y) /\
     FINITE (bir_vars_of_exp e ∪ bir_vars_of_exp e'') /\
     FINITE (bir_vars_of_exp e ∪ bir_vars_of_exp e' ∪ Y) /\
     FINITE (bir_vars_of_exp e ∪ bir_vars_of_exp e')` by (
      METIS_TAC
        [bir_vars_of_exp_FINITE, FINITE_UNION]
    ) >>
    METIS_TAC
      [birs_eval_exp_subst_ALT_def, UNION_COMM,
       UNION_ASSOC, bir_vars_of_exp_FINITE]
  )
);

val birs_eval_exp_subst_ALT_thm = store_thm(
   "birs_eval_exp_subst_ALT_thm", ``
!e senv.
  birs_eval_exp_subst e senv = birs_eval_exp_subst_ALT e senv
``,
  Induct_on `e` >> (
    SIMP_TAC (std_ss)
      ([birs_eval_exp_subst_def, birs_eval_exp_subst_ALT_def, bir_exp_subst_def]@
       [bir_vars_of_exp_def, bir_exp_subst_var_def, FLOOKUP_FUN_FMAP,
        IN_SING, FINITE_SING])
  ) >> (
    ASM_SIMP_TAC (std_ss) [birs_eval_exp_subst_def, birs_eval_exp_subst_ALT_def, bir_exp_subst_def, bir_vars_of_exp_def] >>
    `FINITE (bir_vars_of_exp e ∪ bir_vars_of_exp e') /\
     FINITE (bir_vars_of_exp e' ∪ bir_vars_of_exp e'') /\
     FINITE (bir_vars_of_exp e ∪ bir_vars_of_exp e'')` by (
      METIS_TAC
        [bir_vars_of_exp_FINITE, FINITE_UNION]
    ) >>
    METIS_TAC
      [birs_eval_exp_subst_ALT_def, bir_exp_subst_FUN_FMAP_bir_vars_of_exp_thm, UNION_COMM,
       UNION_ASSOC, bir_vars_of_exp_FINITE]
  )
);

val APPEND_distinct_def = Define `
    APPEND_distinct l1 l2 =
      FOLDR (\x l. if MEM x l then l else x::l) l2 l1
`;
val APPEND_distinct_thm = store_thm(
   "APPEND_distinct_thm", ``
!x l1 l2.
  (MEM x (APPEND_distinct l1 l2))
  <=>
  (MEM x l1 \/ MEM x l2)
  
``,
  Induct_on `l1` >- (
    SIMP_TAC (std_ss++LIST_ss) [APPEND_distinct_def]
  ) >>

  REWRITE_TAC [APPEND_distinct_def] >>
  REPEAT GEN_TAC >>

  SIMP_TAC (std_ss++LIST_ss) [] >>
  Cases_on `MEM h (FOLDR (\x l. if MEM x l then l else x::l) l2 l1)` >> (
    METIS_TAC [APPEND_distinct_def, MEM]
  )
);

val bir_vars_of_exp_LIST_def = Define `
  (bir_vars_of_exp_LIST (BExp_Const _) =
     []) /\
  (bir_vars_of_exp_LIST (BExp_MemConst _ _ _) =
     []) /\
  (bir_vars_of_exp_LIST (BExp_Den v) =
     [v]) /\
  (bir_vars_of_exp_LIST (BExp_Cast _ e _) =
     bir_vars_of_exp_LIST e) /\
  (bir_vars_of_exp_LIST (BExp_UnaryExp _ e) =
     bir_vars_of_exp_LIST e) /\
  (bir_vars_of_exp_LIST (BExp_BinExp _ e1 e2) =
     (APPEND_distinct
       (bir_vars_of_exp_LIST e1)
       (bir_vars_of_exp_LIST e2))) /\
  (bir_vars_of_exp_LIST (BExp_BinPred _ e1 e2) =
     (APPEND_distinct
       (bir_vars_of_exp_LIST e1)
       (bir_vars_of_exp_LIST e2))) /\
  (bir_vars_of_exp_LIST (BExp_MemEq e1 e2) =
     (APPEND_distinct
       (bir_vars_of_exp_LIST e1)
       (bir_vars_of_exp_LIST e2))) /\
  (bir_vars_of_exp_LIST (BExp_IfThenElse ec e1 e2) =
     (APPEND_distinct
       (APPEND_distinct
         (bir_vars_of_exp_LIST ec)
         (bir_vars_of_exp_LIST e1))
       (bir_vars_of_exp_LIST e2))) /\
  (bir_vars_of_exp_LIST (BExp_Load me ae _ _) =
     (APPEND_distinct
       (bir_vars_of_exp_LIST me)
       (bir_vars_of_exp_LIST ae))) /\
  (bir_vars_of_exp_LIST (BExp_Store me ae _ ve) =
     (APPEND_distinct
       (APPEND_distinct
         (bir_vars_of_exp_LIST me)
         (bir_vars_of_exp_LIST ae))
       (bir_vars_of_exp_LIST ve)))
`;

val bir_vars_of_exp_LIST_thm = store_thm(
   "bir_vars_of_exp_LIST_thm", ``
!e x.
  MEM x (bir_vars_of_exp_LIST e) <=> x IN (bir_vars_of_exp e)
``,
  Induct_on `e` >> (
    FULL_SIMP_TAC (std_ss++LIST_ss++PRED_SET_ss)
      [bir_vars_of_exp_def, bir_vars_of_exp_LIST_def, APPEND_distinct_thm]
  )
);

val birs_envty_of_senv_def = Define `
    birs_envty_of_senv senv =
  BEnvTy ((\x. OPTION_BIND x type_of_bir_exp) o senv)
`;
val birs_senv_typecheck_def = Define `
    birs_senv_typecheck e senv =
      EVERY (\v. ((\x. OPTION_BIND x type_of_bir_exp) o senv) (bir_var_name v) = SOME (bir_var_type v)) (bir_vars_of_exp_LIST e)
`;

val birs_senv_typecheck_thm = store_thm(
   "birs_senv_typecheck_thm", ``
!e senv.
  birs_senv_typecheck e senv <=> bir_envty_includes_vs (birs_envty_of_senv senv) (bir_vars_of_exp e)
``,
  REWRITE_TAC
    [birs_senv_typecheck_def, bir_envty_includes_vs_def,
     birs_envty_of_senv_def, bir_envty_includes_v_def, EVERY_MEM, bir_vars_of_exp_LIST_thm] >>
  METIS_TAC []
);

val birs_senv_typecheck_IMP_birs_eval_exp_subst_type_thm = store_thm(
   "birs_senv_typecheck_IMP_birs_eval_exp_subst_type_thm", ``
!e senv.
  (birs_senv_typecheck e senv) ==>
  (type_of_bir_exp (birs_eval_exp_subst e senv) = type_of_bir_exp e)
``,
  SIMP_TAC std_ss [birs_eval_exp_subst_ALT_thm, birs_eval_exp_subst_ALT_def] >>

  REPEAT STRIP_TAC >>
  `FEVERY
     (\(v,e). type_of_bir_exp e = SOME (bir_var_type v))
     (FUN_FMAP (\x. birs_eval_exp_subst_var x senv) (bir_vars_of_exp e))` by (
    SIMP_TAC std_ss [FEVERY_DEF, FUN_FMAP_DEF, bir_vars_of_exp_FINITE] >>

    REPEAT STRIP_TAC >>
    FULL_SIMP_TAC std_ss [birs_senv_typecheck_thm, bir_envty_includes_vs_def, birs_envty_of_senv_def, bir_envty_includes_v_def, birs_eval_exp_subst_var_def] >>
    METIS_TAC [option_CLAUSES, I_THM]
  ) >>

  METIS_TAC [bir_exp_subst_TYPE_EQ]
);

val birs_eval_exp_def = Define `
    birs_eval_exp e senv =
      let e_ty_o = type_of_bir_exp e; in
      if
        birs_senv_typecheck e senv /\
        IS_SOME e_ty_o
      then
        let e' = birs_eval_exp_subst e senv; in
        SOME (e', THE e_ty_o)
      else
        NONE
`;

val birs_eval_exp_subst_var_ALT_def = Define `
    birs_eval_exp_subst_var_ALT x senv =
      OPTION_BIND
        (senv (bir_var_name x))
        (\x_ex. if type_of_bir_exp (x_ex) = SOME (bir_var_type x) then
                  SOME x_ex
                else NONE) 
`;
val birs_eval_cast_def = Define `
  (birs_eval_cast ct (SOME e) ty =
     if ~(option_CASE (type_of_bir_exp e) F bir_type_is_Imm) then NONE else
     SOME (BExp_Cast ct e ty)) /\
  (birs_eval_cast _ _ _ = NONE)`;

val birs_eval_unary_exp_def = Define `
  (birs_eval_unary_exp et (SOME e) =
     if ~(option_CASE (type_of_bir_exp e) F bir_type_is_Imm) then NONE else
     SOME (BExp_UnaryExp et e)) /\
  (birs_eval_unary_exp _ _ = NONE)`;

val birs_eval_bin_exp_def = Define `
  (birs_eval_bin_exp et (SOME e1) (SOME e2) =
     if ~(option_CASE (type_of_bir_exp e1) F bir_type_is_Imm) \/ (type_of_bir_exp e1 <> type_of_bir_exp e2) then NONE else
     SOME (BExp_BinExp et e1 e2)) /\
  (birs_eval_bin_exp _ _ _ = NONE)`;

val birs_eval_bin_pred_def = Define `
  (birs_eval_bin_pred pt (SOME e1) (SOME e2) =
     if ~(option_CASE (type_of_bir_exp e1) F bir_type_is_Imm) \/ (type_of_bir_exp e1 <> type_of_bir_exp e2) then NONE else
     SOME (BExp_BinPred pt e1 e2)) /\
  (birs_eval_bin_pred _ _ _ = NONE)`;

val birs_eval_memeq_def = Define `
  (birs_eval_memeq (SOME e1) (SOME e2) =
     if ~(option_CASE (type_of_bir_exp e1) F bir_type_is_Mem) \/ (type_of_bir_exp e1 <> type_of_bir_exp e2) then NONE else
     SOME (BExp_MemEq e1 e2)) /\
  (birs_eval_memeq _ _ = NONE)`;

val birs_eval_ifthenelse_def = Define `
  (birs_eval_ifthenelse (SOME ec) (SOME et) (SOME ef) =
     if ~(option_CASE (type_of_bir_exp ec) F (bir_type_is_Imm_s Bit1)) \/ IS_NONE (type_of_bir_exp et) \/ (type_of_bir_exp et <> type_of_bir_exp ef) then NONE else
       SOME (BExp_IfThenElse ec et ef)) /\
  (birs_eval_ifthenelse _ _ _ = NONE)`;

val birs_eval_load_def = Define `
  (birs_eval_load (SOME em) (SOME ea) en sz =
     case type_of_bir_exp em of
      | SOME (BType_Mem aty vty) =>
         (case type_of_bir_exp ea of
          | SOME (BType_Imm avty) =>
             if aty <> avty \/ (en = BEnd_NoEndian /\ vty <> sz) \/ (en <> BEnd_NoEndian /\ IS_NONE (bir_number_of_mem_splits vty sz aty)) then NONE else
             SOME (BExp_Load em ea en sz)
          | _ => NONE)
      | _ => NONE) /\
  (birs_eval_load _ _ _ _ = NONE)`;

val birs_eval_store_def = Define `
  (birs_eval_store (SOME em) (SOME ea) en (SOME ev) =
     case type_of_bir_exp em of
      | SOME (BType_Mem aty vty) =>
         (case type_of_bir_exp ea of
          | SOME (BType_Imm avty) =>
             (case type_of_bir_exp ev of
              | SOME (BType_Imm sz) =>
                 if aty <> avty \/ (en = BEnd_NoEndian /\ vty <> sz) \/ (en <> BEnd_NoEndian /\ IS_NONE (bir_number_of_mem_splits vty sz aty)) then NONE else
                 SOME (BExp_Store em ea en ev)
              | _ => NONE)
          | _ => NONE)
      | _ => NONE) /\
  (birs_eval_store _ _ _ _ = NONE)`;

val birs_eval_exp_ALT2_def = Define `
   (birs_eval_exp_ALT2 (BExp_Const n) senv = SOME (BExp_Const n)) /\
   (birs_eval_exp_ALT2 (BExp_MemConst aty vty mmap) senv = SOME (BExp_MemConst aty vty mmap)) /\
   (birs_eval_exp_ALT2 (BExp_Den v) senv = birs_eval_exp_subst_var_ALT v senv) /\
   (birs_eval_exp_ALT2 (BExp_Cast ct e ty) senv =
      birs_eval_cast ct
        (birs_eval_exp_ALT2 e senv) ty) /\
   (birs_eval_exp_ALT2 (BExp_UnaryExp et e) senv =
      birs_eval_unary_exp et
        (birs_eval_exp_ALT2 e senv)) /\
   (birs_eval_exp_ALT2 (BExp_BinExp et e1 e2) senv =
      birs_eval_bin_exp et
        (birs_eval_exp_ALT2 e1 senv)
        (birs_eval_exp_ALT2 e2 senv)) /\
   (birs_eval_exp_ALT2 (BExp_BinPred pt e1 e2) senv =
      birs_eval_bin_pred pt
        (birs_eval_exp_ALT2 e1 senv)
        (birs_eval_exp_ALT2 e2 senv)) /\
   (birs_eval_exp_ALT2 (BExp_MemEq me1 me2) senv =
      birs_eval_memeq
        (birs_eval_exp_ALT2 me1 senv)
        (birs_eval_exp_ALT2 me2 senv)) /\
   (birs_eval_exp_ALT2 (BExp_IfThenElse c et ef) senv =
      birs_eval_ifthenelse
        (birs_eval_exp_ALT2 c senv)
        (birs_eval_exp_ALT2 et senv)
        (birs_eval_exp_ALT2 ef senv)) /\
   (birs_eval_exp_ALT2 (BExp_Load mem_e a_e en ty) senv =
      birs_eval_load
        (birs_eval_exp_ALT2 mem_e senv)
        (birs_eval_exp_ALT2 a_e senv)
        en
        ty) /\
   (birs_eval_exp_ALT2 (BExp_Store mem_e a_e en v_e) senv =
      birs_eval_store
        (birs_eval_exp_ALT2 mem_e senv)
        (birs_eval_exp_ALT2 a_e senv)
        en
        (birs_eval_exp_ALT2 v_e senv))
`;

val birs_eval_exp_ALT2_typeok_thm = store_thm(
   "birs_eval_exp_ALT2_typeok_thm", ``
!e senv ty sv.
  (bir_envty_includes_vs (birs_envty_of_senv senv) (bir_vars_of_exp e)) ==>
  (type_of_bir_exp e = SOME ty) ==>
  (birs_eval_exp_ALT2 e senv = SOME sv) ==>
  (type_of_bir_exp sv = SOME ty)
``,
  Induct_on `e` >- (
    SIMP_TAC std_ss [birs_eval_exp_ALT2_def, type_of_bir_exp_def, bir_vars_of_exp_def, bir_envty_includes_vs_def, NOT_IN_EMPTY]
  ) >- (
    SIMP_TAC std_ss [birs_eval_exp_ALT2_def, type_of_bir_exp_def, bir_vars_of_exp_def, bir_envty_includes_vs_def, NOT_IN_EMPTY]
  ) >- (
    SIMP_TAC std_ss [birs_eval_exp_ALT2_def, type_of_bir_exp_def, bir_vars_of_exp_def, bir_envty_includes_vs_def, NOT_IN_EMPTY] >>
    SIMP_TAC std_ss [birs_eval_exp_ALT2_def, type_of_bir_exp_def, bir_vars_of_exp_def, bir_envty_includes_vs_def, NOT_IN_EMPTY, IN_SING, bir_envty_includes_v_def, birs_envty_of_senv_def] >>
    REPEAT STRIP_TAC >>
    FULL_SIMP_TAC std_ss [birs_eval_exp_subst_var_ALT_def]
  ) >> (
    TRY (
      REPEAT STRIP_TAC >>
      FULL_SIMP_TAC std_ss [bir_vars_of_exp_def, type_of_bir_exp_def, birs_eval_exp_ALT2_def] >>
      REPEAT (PAT_X_ASSUM ``!senv A B. bir_envty_includes_vs (birs_envty_of_senv senv) C ==> D`` (ASSUME_TAC o Q.SPEC `senv`)) >>

      Cases_on `birs_eval_exp_ALT2 e senv` >> (
        FULL_SIMP_TAC std_ss [birs_eval_cast_def, birs_eval_unary_exp_def]
      ) >>

      rename1 `birs_eval_exp_ALT2 e senv = SOME sv_e` >>
      Cases_on `type_of_bir_exp e` >> (
        FULL_SIMP_TAC std_ss [option_CLAUSES]
      ) >>

      PAT_X_ASSUM ``A = sv:bir_exp_t`` (ASSUME_TAC o GSYM) >>
      FULL_SIMP_TAC std_ss [type_of_bir_exp_def] >>
      FAIL_TAC "not finished here"
    )
  ) >> (
    TRY (
      REPEAT STRIP_TAC >>
      FULL_SIMP_TAC std_ss [bir_vars_of_exp_def, type_of_bir_exp_def, birs_eval_exp_ALT2_def, bir_envty_includes_vs_UNION] >>
      REPEAT (PAT_X_ASSUM ``!senv A B. bir_envty_includes_vs (birs_envty_of_senv senv) C ==> D`` (ASSUME_TAC o Q.SPEC `senv`)) >>

      Cases_on `birs_eval_exp_ALT2 e' senv` >> Cases_on `birs_eval_exp_ALT2 e senv` >> (
        FULL_SIMP_TAC std_ss [birs_eval_bin_exp_def, birs_eval_bin_pred_def]
      ) >> (

        rename1 `birs_eval_exp_ALT2 e senv = SOME sv_e` >>
        rename1 `birs_eval_exp_ALT2 e' senv = SOME sv_e'` >>
        Cases_on `type_of_bir_exp e'` >> Cases_on `type_of_bir_exp e` >> (
          FULL_SIMP_TAC std_ss [option_CLAUSES, pairTheory.pair_CASE_def]
        ) >>

        PAT_X_ASSUM ``A = sv:bir_exp_t`` (ASSUME_TAC o GSYM) >>
        FULL_SIMP_TAC std_ss [type_of_bir_exp_def, pairTheory.pair_CASE_def]
      ) >>
      FAIL_TAC "not finished here"
    )
  ) >- (
    REPEAT STRIP_TAC >>
    FULL_SIMP_TAC std_ss [bir_vars_of_exp_def, type_of_bir_exp_def, birs_eval_exp_ALT2_def, bir_envty_includes_vs_UNION] >>
    REPEAT (PAT_X_ASSUM ``!senv A B. bir_envty_includes_vs (birs_envty_of_senv senv) C ==> D`` (ASSUME_TAC o Q.SPEC `senv`)) >>

    Cases_on `birs_eval_exp_ALT2 e' senv` >> Cases_on `birs_eval_exp_ALT2 e senv` >> (
      FULL_SIMP_TAC std_ss [birs_eval_memeq_def]
    ) >>

    rename1 `birs_eval_exp_ALT2 e senv = SOME sv_e` >>
    rename1 `birs_eval_exp_ALT2 e' senv = SOME sv_e'` >>
    Cases_on `type_of_bir_exp e'` >> Cases_on `type_of_bir_exp e` >> (
      FULL_SIMP_TAC std_ss [option_CLAUSES, pairTheory.pair_CASE_def]
    ) >> (
      Cases_on `x` >> (
        FULL_SIMP_TAC (std_ss++holBACore_ss) [option_CLAUSES, pairTheory.pair_CASE_def]
      )
    ) >> (
      Cases_on `x'` >> (
        FULL_SIMP_TAC (std_ss++holBACore_ss) [option_CLAUSES, pairTheory.pair_CASE_def]
      )
    ) >>

    PAT_X_ASSUM ``A = sv:bir_exp_t`` (ASSUME_TAC o GSYM) >>
    FULL_SIMP_TAC (std_ss++holBACore_ss) [type_of_bir_exp_def, pairTheory.pair_CASE_def]
  ) >- (
    REPEAT STRIP_TAC >>
    FULL_SIMP_TAC std_ss [bir_vars_of_exp_def, type_of_bir_exp_def, birs_eval_exp_ALT2_def, bir_envty_includes_vs_UNION] >>
    REPEAT (PAT_X_ASSUM ``!senv A B. bir_envty_includes_vs (birs_envty_of_senv senv) C ==> D`` (ASSUME_TAC o Q.SPEC `senv`)) >>

    Cases_on `birs_eval_exp_ALT2 e'' senv` >> Cases_on `birs_eval_exp_ALT2 e' senv` >> Cases_on `birs_eval_exp_ALT2 e senv` >> (
      FULL_SIMP_TAC std_ss [birs_eval_ifthenelse_def]
    ) >>

    rename1 `birs_eval_exp_ALT2 e senv = SOME sv_e` >>
    rename1 `birs_eval_exp_ALT2 e' senv = SOME sv_e'` >>
    rename1 `birs_eval_exp_ALT2 e'' senv = SOME sv_e''` >>
    Cases_on `type_of_bir_exp e''` >> Cases_on `type_of_bir_exp e'` >> Cases_on `type_of_bir_exp e` >> (
      FULL_SIMP_TAC std_ss [option_CLAUSES, pairTheory.pair_CASE_def]
    ) >>

    PAT_X_ASSUM ``A = sv:bir_exp_t`` (ASSUME_TAC o GSYM) >>
    FULL_SIMP_TAC (std_ss++holBACore_ss) [type_of_bir_exp_def, pairTheory.pair_CASE_def]
  ) >- (
    REPEAT STRIP_TAC >>
    FULL_SIMP_TAC std_ss [bir_vars_of_exp_def, type_of_bir_exp_def, birs_eval_exp_ALT2_def, bir_envty_includes_vs_UNION] >>
    REPEAT (PAT_X_ASSUM ``!senv A B. bir_envty_includes_vs (birs_envty_of_senv senv) C ==> D`` (ASSUME_TAC o Q.SPEC `senv`)) >>

    Cases_on `birs_eval_exp_ALT2 e' senv` >> Cases_on `birs_eval_exp_ALT2 e senv` >> (
      FULL_SIMP_TAC std_ss [birs_eval_load_def]
    ) >>

    rename1 `birs_eval_exp_ALT2 e senv = SOME sv_e` >>
    rename1 `birs_eval_exp_ALT2 e' senv = SOME sv_e'` >>
    Cases_on `type_of_bir_exp e'` >> Cases_on `type_of_bir_exp e` >> (
      FULL_SIMP_TAC std_ss [option_CLAUSES, pairTheory.pair_CASE_def]
    ) >> (
      Cases_on `x` >> (
        FULL_SIMP_TAC (std_ss++holBACore_ss) [option_CLAUSES, pairTheory.pair_CASE_def]
      )
    ) >> (
      Cases_on `x'` >> (
        FULL_SIMP_TAC (std_ss++holBACore_ss) [option_CLAUSES, pairTheory.pair_CASE_def]
      )
    ) >>

    REV_FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
    FULL_SIMP_TAC (std_ss++holBACore_ss) [type_of_bir_exp_def, pairTheory.pair_CASE_def] >>

    PAT_X_ASSUM ``A = sv:bir_exp_t`` (ASSUME_TAC o GSYM) >>
    FULL_SIMP_TAC (std_ss++holBACore_ss) [type_of_bir_exp_def, pairTheory.pair_CASE_def]
  ) >> (
    REPEAT STRIP_TAC >>
    FULL_SIMP_TAC std_ss [bir_vars_of_exp_def, type_of_bir_exp_def, birs_eval_exp_ALT2_def, bir_envty_includes_vs_UNION] >>
    REPEAT (PAT_X_ASSUM ``!senv A B. bir_envty_includes_vs (birs_envty_of_senv senv) C ==> D`` (ASSUME_TAC o Q.SPEC `senv`)) >>

    Cases_on `birs_eval_exp_ALT2 e'' senv` >> Cases_on `birs_eval_exp_ALT2 e' senv` >> Cases_on `birs_eval_exp_ALT2 e senv` >> (
      FULL_SIMP_TAC std_ss [birs_eval_store_def]
    ) >>

    rename1 `birs_eval_exp_ALT2 e senv = SOME sv_e` >>
    rename1 `birs_eval_exp_ALT2 e' senv = SOME sv_e'` >>
    rename1 `birs_eval_exp_ALT2 e'' senv = SOME sv_e''` >>
    Cases_on `type_of_bir_exp e''` >> Cases_on `type_of_bir_exp e'` >> Cases_on `type_of_bir_exp e` >> (
      FULL_SIMP_TAC std_ss [option_CLAUSES, pairTheory.pair_CASE_def]
    ) >> (
      Cases_on `x` >> (
        FULL_SIMP_TAC (std_ss++holBACore_ss) [option_CLAUSES, pairTheory.pair_CASE_def]
      )
    ) >> (
      Cases_on `x'` >> (
        FULL_SIMP_TAC (std_ss++holBACore_ss) [option_CLAUSES, pairTheory.pair_CASE_def]
      )
    ) >> (
      Cases_on `x''` >> (
        FULL_SIMP_TAC (std_ss++holBACore_ss) [option_CLAUSES, pairTheory.pair_CASE_def]
      )
    ) >>

    Cases_on `ty` >> (
      FULL_SIMP_TAC (std_ss++holBACore_ss) [option_CLAUSES, pairTheory.pair_CASE_def]
    ) >>

    REV_FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
    FULL_SIMP_TAC (std_ss++holBACore_ss) [type_of_bir_exp_def, pairTheory.pair_CASE_def] >>

    PAT_X_ASSUM ``A = sv:bir_exp_t`` (ASSUME_TAC o GSYM) >>
    FULL_SIMP_TAC (std_ss++holBACore_ss) [type_of_bir_exp_def, pairTheory.pair_CASE_def]
  )
);

val birs_eval_exp_ALT2_typeerr_thm = store_thm(
   "birs_eval_exp_ALT2_typeerr_thm", ``
!e senv.
  ((~(bir_envty_includes_vs (birs_envty_of_senv senv) (bir_vars_of_exp e))) \/
   (type_of_bir_exp e = NONE)) ==>
  (birs_eval_exp_ALT2 e senv = NONE)
``,
  Induct_on `e` >- (
    SIMP_TAC std_ss [birs_eval_exp_ALT2_def, type_of_bir_exp_def, bir_vars_of_exp_def, bir_envty_includes_vs_def, NOT_IN_EMPTY]
  ) >- (
    SIMP_TAC std_ss [birs_eval_exp_ALT2_def, type_of_bir_exp_def, bir_vars_of_exp_def, bir_envty_includes_vs_def, NOT_IN_EMPTY]
  ) >- (
    SIMP_TAC std_ss [birs_eval_exp_ALT2_def, type_of_bir_exp_def, bir_vars_of_exp_def, bir_envty_includes_vs_def, NOT_IN_EMPTY] >>
    SIMP_TAC std_ss [birs_eval_exp_ALT2_def, type_of_bir_exp_def, bir_vars_of_exp_def, bir_envty_includes_vs_def, NOT_IN_EMPTY, IN_SING, bir_envty_includes_v_def, birs_envty_of_senv_def] >>
    REPEAT STRIP_TAC >>
    FULL_SIMP_TAC std_ss [birs_eval_exp_subst_var_ALT_def] >>

    Cases_on `senv (bir_var_name b)` >> (
      FULL_SIMP_TAC std_ss [option_CLAUSES]
    )
  ) >> (
    TRY (
      (* 2x *)
      REPEAT GEN_TAC >>
      REPEAT (PAT_X_ASSUM ``!A.B`` (ASSUME_TAC o SIMP_RULE std_ss [boolTheory.DISJ_IMP_THM] o Q.SPEC `senv`)) >>

      REPEAT STRIP_TAC >> (
        FULL_SIMP_TAC std_ss [bir_vars_of_exp_def, type_of_bir_exp_def, birs_eval_exp_ALT2_def] >>
        REV_FULL_SIMP_TAC std_ss [] >>
        REWRITE_TAC [birs_eval_cast_def, birs_eval_unary_exp_def]
      ) >>

      Cases_on `type_of_bir_exp e` >> (
        FULL_SIMP_TAC std_ss [option_CLAUSES] >>
        REWRITE_TAC [birs_eval_cast_def, birs_eval_unary_exp_def]
      ) >>

      Cases_on `birs_eval_exp_ALT2 e senv` >> (
        FULL_SIMP_TAC std_ss [birs_eval_cast_def, birs_eval_unary_exp_def] >>
        REWRITE_TAC []
      ) >>

      IMP_RES_TAC birs_eval_exp_ALT2_typeok_thm >>
      FULL_SIMP_TAC std_ss [] >>
      FAIL_TAC "not done yet"
    )
  ) >> (
    TRY (
      (* 2x *)
      REPEAT GEN_TAC >>
      REPEAT (PAT_X_ASSUM ``!A.B`` (ASSUME_TAC o SIMP_RULE std_ss [boolTheory.DISJ_IMP_THM] o Q.SPEC `senv`)) >>

      REPEAT STRIP_TAC >> (
        FULL_SIMP_TAC std_ss [bir_vars_of_exp_def, type_of_bir_exp_def, birs_eval_exp_ALT2_def, bir_envty_includes_vs_UNION] >>
        REV_FULL_SIMP_TAC std_ss [] >>
        FULL_SIMP_TAC std_ss [birs_eval_bin_pred_def, birs_eval_bin_exp_def]
      ) >> (
        Cases_on `type_of_bir_exp e'` >> Cases_on `type_of_bir_exp e` >> Cases_on `birs_eval_exp_ALT2 e senv` >> (
          FULL_SIMP_TAC std_ss [option_CLAUSES] >>
          REWRITE_TAC [birs_eval_bin_pred_def, birs_eval_bin_exp_def]
        ) >>

        Cases_on `birs_eval_exp_ALT2 e' senv` >> (
          FULL_SIMP_TAC std_ss [birs_eval_bin_pred_def, birs_eval_bin_exp_def] >>
          REWRITE_TAC []
        ) >>

        IMP_RES_TAC birs_eval_exp_ALT2_typeok_thm >>
        Cases_on `x = x'` >> (
          FULL_SIMP_TAC (std_ss++holBACore_ss) [option_CLAUSES, pairTheory.pair_CASE_def]
        )
      ) >>
      FAIL_TAC "not done yet"
    )
  ) >- (
    (* 1x MemEq *)
    REPEAT GEN_TAC >>
    REPEAT (PAT_X_ASSUM ``!A.B`` (ASSUME_TAC o SIMP_RULE std_ss [boolTheory.DISJ_IMP_THM] o Q.SPEC `senv`)) >>

    REPEAT STRIP_TAC >> (
      FULL_SIMP_TAC std_ss [bir_vars_of_exp_def, type_of_bir_exp_def, birs_eval_exp_ALT2_def, bir_envty_includes_vs_UNION] >>
      REV_FULL_SIMP_TAC std_ss [] >>
      FULL_SIMP_TAC std_ss [birs_eval_memeq_def]
    ) >> (
      Cases_on `type_of_bir_exp e'` >> Cases_on `type_of_bir_exp e` >> Cases_on `birs_eval_exp_ALT2 e senv` >> (
        FULL_SIMP_TAC std_ss [option_CLAUSES] >>
        REWRITE_TAC [birs_eval_memeq_def]
      ) >>

      Cases_on `birs_eval_exp_ALT2 e' senv` >> (
        FULL_SIMP_TAC std_ss [birs_eval_memeq_def] >>
        REWRITE_TAC []
      ) >>

      IMP_RES_TAC birs_eval_exp_ALT2_typeok_thm >>
      Cases_on `x` >> Cases_on `x'` >> (
        FULL_SIMP_TAC (std_ss++holBACore_ss) [option_CLAUSES, pairTheory.pair_CASE_def]
      )
    )
  ) >- (
    (* 1x ifthenelse *)
    REPEAT GEN_TAC >>
    REPEAT (PAT_X_ASSUM ``!A.B`` (ASSUME_TAC o SIMP_RULE std_ss [boolTheory.DISJ_IMP_THM] o Q.SPEC `senv`)) >>

    REPEAT STRIP_TAC >> (
      FULL_SIMP_TAC std_ss [bir_vars_of_exp_def, type_of_bir_exp_def, birs_eval_exp_ALT2_def, bir_envty_includes_vs_UNION] >>
      REV_FULL_SIMP_TAC std_ss [] >>
      FULL_SIMP_TAC std_ss [birs_eval_ifthenelse_def]
    ) >> (
      Cases_on `type_of_bir_exp e''` >> Cases_on `type_of_bir_exp e'` >> Cases_on `type_of_bir_exp e` >> Cases_on `birs_eval_exp_ALT2 e senv` >> (
        FULL_SIMP_TAC std_ss [option_CLAUSES] >>
        REWRITE_TAC [birs_eval_ifthenelse_def]
      ) >>

      Cases_on `birs_eval_exp_ALT2 e' senv` >> (
        FULL_SIMP_TAC std_ss [birs_eval_ifthenelse_def] >>
        REWRITE_TAC []
      ) >>

      Cases_on `birs_eval_exp_ALT2 e'' senv` >> (
        FULL_SIMP_TAC std_ss [birs_eval_ifthenelse_def] >>
        REWRITE_TAC []
      ) >>

      IMP_RES_TAC birs_eval_exp_ALT2_typeok_thm >>
      Cases_on `x` >> Cases_on `x'` >> Cases_on `x''` >> Cases_on `b = b'` >> Cases_on `b0 = b0'` >> (
        FULL_SIMP_TAC (std_ss++holBACore_ss) [option_CLAUSES, pairTheory.pair_CASE_def, BType_Bool_def]
      )
    )
  ) >- (
    (* 1x memload *)
    REPEAT GEN_TAC >>
    REPEAT (PAT_X_ASSUM ``!A.B`` (ASSUME_TAC o SIMP_RULE std_ss [boolTheory.DISJ_IMP_THM] o Q.SPEC `senv`)) >>

    REPEAT STRIP_TAC >> (
      FULL_SIMP_TAC std_ss [bir_vars_of_exp_def, type_of_bir_exp_def, birs_eval_exp_ALT2_def, bir_envty_includes_vs_UNION] >>
      REV_FULL_SIMP_TAC std_ss [] >>
      FULL_SIMP_TAC std_ss [birs_eval_load_def]
    ) >> (
      Cases_on `type_of_bir_exp e'` >> Cases_on `type_of_bir_exp e` >> Cases_on `birs_eval_exp_ALT2 e senv` >> (
        FULL_SIMP_TAC std_ss [option_CLAUSES] >>
        REWRITE_TAC [birs_eval_load_def]
      ) >>

      Cases_on `birs_eval_exp_ALT2 e' senv` >> (
        FULL_SIMP_TAC std_ss [birs_eval_load_def] >>
        REWRITE_TAC []
      ) >>

      IMP_RES_TAC birs_eval_exp_ALT2_typeok_thm >>
      Cases_on `x` >> Cases_on `x'` >> Cases_on `b' = b` >> Cases_on `b2 = BEnd_NoEndian` >> (
        FULL_SIMP_TAC (std_ss++holBACore_ss) [option_CLAUSES, pairTheory.pair_CASE_def, BType_Bool_def]
      )
    )
  ) >> (
    (* 1x memstore *)
    REPEAT GEN_TAC >>
    REPEAT (PAT_X_ASSUM ``!A.B`` (ASSUME_TAC o SIMP_RULE std_ss [boolTheory.DISJ_IMP_THM] o Q.SPEC `senv`)) >>

    REPEAT STRIP_TAC >> (
      FULL_SIMP_TAC std_ss [bir_vars_of_exp_def, type_of_bir_exp_def, birs_eval_exp_ALT2_def, bir_envty_includes_vs_UNION] >>
      REV_FULL_SIMP_TAC std_ss [] >>
      FULL_SIMP_TAC std_ss [birs_eval_store_def]
    ) >> (
      Cases_on `type_of_bir_exp e''` >> Cases_on `type_of_bir_exp e'` >> Cases_on `type_of_bir_exp e` >> Cases_on `birs_eval_exp_ALT2 e senv` >> Cases_on `birs_eval_exp_ALT2 e' senv` >> (
        FULL_SIMP_TAC std_ss [option_CLAUSES] >>
        REWRITE_TAC [birs_eval_store_def]
      ) >>

      Cases_on `birs_eval_exp_ALT2 e'' senv` >> (
        FULL_SIMP_TAC std_ss [birs_eval_store_def] >>
        REWRITE_TAC []
      ) >>

      IMP_RES_TAC birs_eval_exp_ALT2_typeok_thm >>
      Cases_on `x` >> Cases_on `x'` >> Cases_on `x''` >> Cases_on `b'' = b'` >> Cases_on `b0 = b0'` >> Cases_on `b2 = BEnd_NoEndian` >> (
        FULL_SIMP_TAC (std_ss++holBACore_ss) [option_CLAUSES, pairTheory.pair_CASE_def, BType_Bool_def]
      )
    )
  )
);


val birs_eval_exp_ALT2_thm = store_thm(
   "birs_eval_exp_ALT2_thm", ``
!e senv.
  (bir_envty_includes_vs (birs_envty_of_senv senv) (bir_vars_of_exp e)) ==>
  (IS_SOME (type_of_bir_exp e)) ==>
  (SOME (birs_eval_exp_subst e senv) = birs_eval_exp_ALT2 e senv)
``,
  Induct_on `e` >- (
    FULL_SIMP_TAC (std_ss)
      ([birs_eval_exp_subst_def, birs_eval_exp_ALT2_def, LET_DEF, birs_senv_typecheck_thm]@
       [type_of_bir_exp_def, bir_vars_of_exp_def, bir_envty_includes_vs_def, NOT_IN_EMPTY])
  ) >- (
    FULL_SIMP_TAC (std_ss)
      ([birs_eval_exp_subst_def, birs_eval_exp_ALT2_def, LET_DEF, birs_senv_typecheck_thm]@
       [type_of_bir_exp_def, bir_vars_of_exp_def, bir_envty_includes_vs_def, NOT_IN_EMPTY])
  ) >- (
    FULL_SIMP_TAC (std_ss)
      ([birs_eval_exp_subst_def, birs_eval_exp_ALT2_def, LET_DEF, birs_senv_typecheck_thm]@
       [type_of_bir_exp_def, bir_vars_of_exp_def, bir_envty_includes_vs_def, NOT_IN_EMPTY]) >>
    SIMP_TAC (std_ss)
      [birs_eval_exp_subst_var_ALT_def, IN_SING, bir_envty_includes_v_def, birs_eval_exp_subst_var_def, birs_envty_of_senv_def] >>
    REPEAT STRIP_TAC >> (
      FULL_SIMP_TAC (std_ss) [option_CLAUSES]
    )
  ) >> (
    TRY (
      REPEAT STRIP_TAC >>
      REPEAT (PAT_X_ASSUM ``!A.B`` (ASSUME_TAC o Q.SPEC `senv`)) >>

      FULL_SIMP_TAC (std_ss)
        ([birs_eval_exp_subst_def, birs_eval_exp_ALT2_def]@
         [IS_SOME_EXISTS, type_of_bir_exp_EQ_SOME_REWRS, bir_vars_of_exp_def]) >>

      Cases_on `birs_eval_exp_ALT2 e senv` >> (
        FULL_SIMP_TAC (std_ss) [birs_eval_cast_def, birs_eval_unary_exp_def]
      ) >>
      REV_FULL_SIMP_TAC (std_ss) [] >>

      IMP_RES_TAC birs_eval_exp_ALT2_typeok_thm >>
      FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
      FAIL_TAC "not there yet"
    )
  ) >> (
    TRY (
      REPEAT STRIP_TAC >>
      REPEAT (PAT_X_ASSUM ``!A.B`` (ASSUME_TAC o Q.SPEC `senv`)) >>

      FULL_SIMP_TAC (std_ss)
        ([birs_eval_exp_subst_def, birs_eval_exp_ALT2_def]@
         [IS_SOME_EXISTS, type_of_bir_exp_EQ_SOME_REWRS, bir_vars_of_exp_def, bir_envty_includes_vs_UNION]) >>

      Cases_on `birs_eval_exp_ALT2 e' senv` >> Cases_on `birs_eval_exp_ALT2 e senv` >> (
        FULL_SIMP_TAC (std_ss) [birs_eval_bin_exp_def, birs_eval_bin_pred_def, birs_eval_memeq_def]
      ) >>
      REV_FULL_SIMP_TAC (std_ss) [] >>

      IMP_RES_TAC birs_eval_exp_ALT2_typeok_thm >>
      FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
      FAIL_TAC "not there yet"
    )
  ) >> (
    TRY (
      REPEAT STRIP_TAC >>
      REPEAT (PAT_X_ASSUM ``!A.B`` (ASSUME_TAC o Q.SPEC `senv`)) >>

      FULL_SIMP_TAC (std_ss)
        ([birs_eval_exp_subst_def, birs_eval_exp_ALT2_def]@
         [IS_SOME_EXISTS, type_of_bir_exp_EQ_SOME_REWRS, bir_vars_of_exp_def, bir_envty_includes_vs_UNION]) >>

      Cases_on `birs_eval_exp_ALT2 e'' senv` >> Cases_on `birs_eval_exp_ALT2 e' senv` >> Cases_on `birs_eval_exp_ALT2 e senv` >> (
        FULL_SIMP_TAC (std_ss) [birs_eval_ifthenelse_def]
      ) >>
      REV_FULL_SIMP_TAC (std_ss) [] >>

      IMP_RES_TAC birs_eval_exp_ALT2_typeok_thm >>
      FULL_SIMP_TAC (std_ss++holBACore_ss) [BType_Bool_def] >>
      FAIL_TAC "not there yet"
    )
  ) >- (
    (* load *)
    REPEAT STRIP_TAC >>
    REPEAT (PAT_X_ASSUM ``!A.B`` (ASSUME_TAC o Q.SPEC `senv`)) >>

    FULL_SIMP_TAC (std_ss)
      ([birs_eval_exp_subst_def, birs_eval_exp_ALT2_def]@
       [IS_SOME_EXISTS, type_of_bir_exp_EQ_SOME_REWRS, bir_vars_of_exp_def, bir_envty_includes_vs_UNION]) >>

    Cases_on `birs_eval_exp_ALT2 e' senv` >> Cases_on `birs_eval_exp_ALT2 e senv` >> (
      FULL_SIMP_TAC (std_ss) [birs_eval_load_def]
    ) >>
    REV_FULL_SIMP_TAC (std_ss) [] >>

    IMP_RES_TAC birs_eval_exp_ALT2_typeok_thm >>
    Cases_on `b2 = BEnd_NoEndian` >>  (
      FULL_SIMP_TAC (std_ss++holBACore_ss) []
    ) >>
    FAIL_TAC "not there yet"
  ) >> (
    (* store *)
    REPEAT STRIP_TAC >>
    REPEAT (PAT_X_ASSUM ``!A.B`` (ASSUME_TAC o Q.SPEC `senv`)) >>

    FULL_SIMP_TAC (std_ss)
      ([birs_eval_exp_subst_def, birs_eval_exp_ALT2_def]@
       [IS_SOME_EXISTS, type_of_bir_exp_EQ_SOME_REWRS, bir_vars_of_exp_def, bir_envty_includes_vs_UNION]) >>

    Cases_on `birs_eval_exp_ALT2 e'' senv` >> Cases_on `birs_eval_exp_ALT2 e' senv` >> Cases_on `birs_eval_exp_ALT2 e senv` >> (
      FULL_SIMP_TAC (std_ss) [birs_eval_store_def]
    ) >>
    REV_FULL_SIMP_TAC (std_ss) [] >>

    IMP_RES_TAC birs_eval_exp_ALT2_typeok_thm >>
    Cases_on `b2 = BEnd_NoEndian` >>  (
      FULL_SIMP_TAC (std_ss++holBACore_ss) []
    ) >>
    FAIL_TAC "not there yet"
  )
);

val birs_eval_exp_ALT_def = Define `
    birs_eval_exp_ALT e senv =
      OPTION_MAP (\se. (se, THE (type_of_bir_exp se))) (birs_eval_exp_ALT2 e senv)
`;

val birs_eval_exp_ALT_thm = store_thm(
   "birs_eval_exp_ALT_thm", ``
!e senv.
  birs_eval_exp e senv = birs_eval_exp_ALT e senv
``,
  FULL_SIMP_TAC (std_ss)
      [birs_eval_exp_def, birs_eval_exp_ALT_def, LET_DEF, birs_senv_typecheck_thm] >>
  REPEAT STRIP_TAC >>

  Cases_on `bir_envty_includes_vs (birs_envty_of_senv senv)
            (bir_vars_of_exp e) /\ IS_SOME (type_of_bir_exp e)` >> (
      FULL_SIMP_TAC (std_ss) [IS_SOME_EXISTS, option_CLAUSES, birs_eval_exp_ALT2_thm, birs_senv_typecheck_IMP_birs_eval_exp_subst_type_thm, birs_senv_typecheck_thm]
  ) >> (
    METIS_TAC [birs_eval_exp_ALT2_typeerr_thm]
  )
);
(* TODO: rename the other theorem to birs_interpr_fun_ALT_thm *)


val birs_eval_exp_NONE_EQ_bir_exp_env_type_thm = store_thm(
   "birs_eval_exp_NONE_EQ_bir_exp_env_type_thm", ``
!senv e.
  ((type_of_bir_exp e = NONE) \/
   (~bir_envty_includes_vs (birs_envty_of_senv senv) (bir_vars_of_exp e)))
  <=>
  (birs_eval_exp e senv = NONE)
``,
  SIMP_TAC std_ss [birs_eval_exp_def, LET_DEF, birs_senv_typecheck_thm] >>
  METIS_TAC []
);

val birs_eval_exp_SOME_EQ_bir_exp_env_type_thm = store_thm(
   "birs_eval_exp_SOME_EQ_bir_exp_env_type_thm", ``
!senv e ty.
  (type_of_bir_exp e = SOME ty) /\
  (bir_envty_includes_vs (birs_envty_of_senv senv) (bir_vars_of_exp e))
  <=>
  (?sv. birs_eval_exp e senv = SOME (sv, ty))
``,
  SIMP_TAC std_ss [birs_eval_exp_def, LET_DEF, birs_senv_typecheck_thm] >>
  METIS_TAC [option_CLAUSES]
);

val birs_eval_exp_IMP_type_thm = store_thm(
   "birs_eval_exp_IMP_type_thm", ``
!e senv sv ty.
  (birs_eval_exp e senv = SOME (sv, ty)) ==>
  (type_of_bir_exp sv = SOME ty)
``,
  SIMP_TAC std_ss
    [birs_eval_exp_def, LET_DEF, option_CLAUSES,
     birs_senv_typecheck_IMP_birs_eval_exp_subst_type_thm]
);

(* TODO: define predicate for symbols of birs store? *)
val bir_vars_of_exp_IMP_symbs_SUBSET_senv_thm = store_thm(
   "bir_vars_of_exp_IMP_symbs_SUBSET_senv_thm", ``
!e senv sv ty.
  (birs_eval_exp e senv = SOME (sv,ty)) ==>
  (bir_vars_of_exp sv SUBSET (BIGUNION {bir_vars_of_exp e | (?vn. senv vn = SOME e)}))
``,
  REWRITE_TAC [birs_eval_exp_ALT_thm, birs_eval_exp_ALT_def] >>
  Induct_on `e` >> (
    SIMP_TAC std_ss [birs_eval_exp_ALT_def, birs_eval_exp_ALT2_def, bir_vars_of_exp_def, EMPTY_SUBSET]
  ) >- (
    SIMP_TAC std_ss [birs_eval_exp_subst_var_ALT_def] >>
    SIMP_TAC (std_ss++PRED_SET_ss) [SUBSET_DEF] >>
    REPEAT STRIP_TAC >>
    METIS_TAC []
  ) >> (
    TRY (
      REPEAT STRIP_TAC >>
      Cases_on `birs_eval_exp_ALT2 e senv` >> (
        FULL_SIMP_TAC std_ss [birs_eval_cast_def, birs_eval_unary_exp_def]
      ) >>

      Cases_on `type_of_bir_exp x` >> (
        FULL_SIMP_TAC std_ss []
      ) >>
      FULL_SIMP_TAC std_ss [bir_vars_of_exp_def] >>

      PAT_X_ASSUM ``A = sv:bir_exp_t`` (ASSUME_TAC o GSYM) >>
      FULL_SIMP_TAC std_ss [bir_vars_of_exp_def, pairTheory.pair_CASE_def] >>
      FAIL_TAC "oh no"
    ) >>

    TRY (
      REPEAT STRIP_TAC >>
      Cases_on `birs_eval_exp_ALT2 e senv` >> Cases_on `birs_eval_exp_ALT2 e' senv` >> (
        FULL_SIMP_TAC std_ss [birs_eval_bin_exp_def, birs_eval_bin_pred_def]
      ) >>

      rename1 `birs_eval_exp_ALT2 e senv = SOME sv_e` >>
      rename1 `birs_eval_exp_ALT2 e' senv = SOME sv_e'` >>
      Cases_on `type_of_bir_exp sv_e` >> Cases_on `type_of_bir_exp sv_e'` >> (
        FULL_SIMP_TAC std_ss []
      ) >>
      FULL_SIMP_TAC std_ss [bir_vars_of_exp_def] >>

      PAT_X_ASSUM ``A = sv:bir_exp_t`` (ASSUME_TAC o GSYM) >>
      FULL_SIMP_TAC std_ss [bir_vars_of_exp_def, pairTheory.pair_CASE_def, UNION_SUBSET] >>
      FAIL_TAC "oh no"
    ) >>

    TRY (
      REPEAT STRIP_TAC >>
      Cases_on `birs_eval_exp_ALT2 e senv` >> Cases_on `birs_eval_exp_ALT2 e' senv` >> (
        FULL_SIMP_TAC std_ss [birs_eval_memeq_def]
      ) >>

      rename1 `birs_eval_exp_ALT2 e senv = SOME sv_e` >>
      rename1 `birs_eval_exp_ALT2 e' senv = SOME sv_e'` >>
      Cases_on `type_of_bir_exp sv_e` >> Cases_on `type_of_bir_exp sv_e'` >> (
        FULL_SIMP_TAC std_ss []
      ) >>
      FULL_SIMP_TAC std_ss [bir_vars_of_exp_def] >>

      PAT_X_ASSUM ``A = sv:bir_exp_t`` (ASSUME_TAC o GSYM) >>
      FULL_SIMP_TAC std_ss [bir_vars_of_exp_def, pairTheory.pair_CASE_def, UNION_SUBSET] >>
      FAIL_TAC "oh no"
    )
  ) >> (
    cheat
  )
);



val bir_val_to_constexp_def = Define `
   (bir_val_to_constexp (BVal_Imm i) = BExp_Const i) /\
   (bir_val_to_constexp (BVal_Mem aty vty mmap) = BExp_MemConst aty vty mmap)
`;
val birs_interpret_subst_fmap_get_def = Define `
    birs_interpret_subst_fmap_get i x =
      if x IN symb_interpr_dom i then
        bir_val_to_constexp (THE (symb_interpr_get i x))
      else
        BExp_Den x
`;
val birs_interpret_subst_fmap_def = Define `
    birs_interpret_subst_fmap i e =
      FUN_FMAP (birs_interpret_subst_fmap_get i) (bir_vars_of_exp e)
`;
val birs_interpret_subst_def = Define `
    birs_interpret_subst i e =
      bir_exp_subst
        (birs_interpret_subst_fmap i e)
        e
`;
val birs_interpret_fun_def = Define `
    birs_interpret_fun i e =
      bir_eval_exp
       (birs_interpret_subst i e)
       bir_env_empty
`;

val birs_interpret_get_var_def = Define `
    birs_interpret_get_var i x =
      if x IN symb_interpr_dom i then
        symb_interpr_get i x
      else
        NONE
`;
val birs_interpret_fun_ALT_def = Define `
   (birs_interpret_fun_ALT i (BExp_Const n) = SOME (BVal_Imm n)) /\
   (birs_interpret_fun_ALT i (BExp_MemConst aty vty mmap) = SOME (BVal_Mem aty vty mmap)) /\
   (birs_interpret_fun_ALT i (BExp_Den v) = birs_interpret_get_var i v) /\
   (birs_interpret_fun_ALT i (BExp_Cast ct e ty) =
      bir_eval_cast ct (birs_interpret_fun_ALT i e) ty) /\
   (birs_interpret_fun_ALT i (BExp_UnaryExp et e) =
      bir_eval_unary_exp et (birs_interpret_fun_ALT i e)) /\
   (birs_interpret_fun_ALT i (BExp_BinExp et e1 e2) =
      bir_eval_bin_exp et
        (birs_interpret_fun_ALT i e1)
        (birs_interpret_fun_ALT i e2)) /\
   (birs_interpret_fun_ALT i (BExp_BinPred pt e1 e2) =
      bir_eval_bin_pred pt
        (birs_interpret_fun_ALT i e1)
        (birs_interpret_fun_ALT i e2)) /\
   (birs_interpret_fun_ALT i (BExp_MemEq me1 me2) =
      bir_eval_memeq
        (birs_interpret_fun_ALT i me1)
        (birs_interpret_fun_ALT i me2)) /\
   (birs_interpret_fun_ALT i (BExp_IfThenElse c et ef) =
      bir_eval_ifthenelse
        (birs_interpret_fun_ALT i c)
        (birs_interpret_fun_ALT i et)
        (birs_interpret_fun_ALT i ef)) /\
   (birs_interpret_fun_ALT i (BExp_Load mem_e a_e en ty) =
      bir_eval_load
        (birs_interpret_fun_ALT i mem_e)
        (birs_interpret_fun_ALT i a_e)
        en
        ty) /\
   (birs_interpret_fun_ALT i (BExp_Store mem_e a_e en v_e) =
      bir_eval_store
        (birs_interpret_fun_ALT i mem_e)
        (birs_interpret_fun_ALT i a_e)
        en
        (birs_interpret_fun_ALT i v_e))
`;

val birs_interpret_fun_thm = store_thm(
   "birs_interpret_fun_thm", ``
!i e.
  birs_interpret_fun i e = birs_interpret_fun_ALT i e
``,
  REPEAT STRIP_TAC >>
  Induct_on `e` >- (
    (* BExp_Const *)
    FULL_SIMP_TAC (std_ss++holBACore_ss) [birs_interpret_fun_def, birs_interpret_fun_ALT_def, birs_interpret_subst_def, bir_exp_subst_def]
  ) >- (
    (* BExp_MemConst *)
    FULL_SIMP_TAC (std_ss++holBACore_ss) [birs_interpret_fun_def, birs_interpret_fun_ALT_def, birs_interpret_subst_def, bir_exp_subst_def]
  ) >- (
    (* BExp_Den *)
    FULL_SIMP_TAC (std_ss++holBACore_ss) [birs_interpret_fun_def, birs_interpret_fun_ALT_def, birs_interpret_subst_def, bir_exp_subst_def] >>
    FULL_SIMP_TAC (std_ss++holBACore_ss) [birs_interpret_subst_fmap_def, bir_exp_subst_var_def, FLOOKUP_FUN_FMAP, FINITE_SING, IN_SING, birs_interpret_subst_fmap_get_def] >>
    FULL_SIMP_TAC (std_ss++holBACore_ss) [birs_interpret_get_var_def] >>
    REPEAT STRIP_TAC >>
    Cases_on `b IN symb_interpr_dom i` >- (
      Cases_on `symb_interpr_get i b` >- (
        FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
        METIS_TAC [symb_interpr_dom_IMP_get_CASES_thm, option_CLAUSES]
      ) >>
      Cases_on `x` >> (
        FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_val_to_constexp_def, bir_eval_exp_def]
      )
    ) >>
    FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_env_read_def, bir_env_empty_def, bir_env_map_empty_def, bir_env_check_type_def, bir_env_lookup_def]
  )(* >- (
    SIMP_TAC (std_ss++holBACore_ss) [birs_interpret_fun_def, birs_interpret_fun_ALT_def, birs_interpret_subst_def, bir_exp_subst_def, birs_interpret_subst_fmap_def] >>
    METIS_TAC [birs_interpret_fun_def, birs_interpret_subst_def, birs_interpret_subst_fmap_def]
  )*) >> (
    (* BExp_* *)
    SIMP_TAC (std_ss++holBACore_ss) [birs_interpret_fun_def, birs_interpret_fun_ALT_def, birs_interpret_subst_def, bir_exp_subst_def, birs_interpret_subst_fmap_def] >>
    `FINITE (bir_vars_of_exp e ) /\
     FINITE (bir_vars_of_exp e') /\
     FINITE (bir_vars_of_exp e' UNION bir_vars_of_exp e'') /\
     FINITE (bir_vars_of_exp e  UNION bir_vars_of_exp e' ) /\
     FINITE (bir_vars_of_exp e  UNION bir_vars_of_exp e'')` by (
      METIS_TAC [bir_vars_of_exp_FINITE, FINITE_UNION, UNION_COMM, UNION_ASSOC]
    ) >>
    METIS_TAC
      [birs_interpret_fun_def, birs_interpret_subst_def, birs_interpret_subst_fmap_def,
       bir_exp_subst_FUN_FMAP_bir_vars_of_exp_UNION_thm, UNION_COMM, UNION_ASSOC]
  )
);


(* now a symbolic state *)
val _ = Datatype `birs_state_t = <|
  bsst_pc       : bir_programcounter_t;
  bsst_environ  : string -> bir_exp_t option;
  bsst_status   : bir_status_t;
  bsst_pcond    : bir_exp_t
|>`;

val birs_symb_to_symbst_def = Define `
    birs_symb_to_symbst s =
      (SymbSymbSt
        s.bsst_pc
        s.bsst_environ
        s.bsst_pcond
        s.bsst_status)
`;

val birs_symb_from_symbst_def = Define `
    birs_symb_from_symbst (SymbSymbSt lbl env pcond status) =
      <|
        bsst_pc       := lbl;
        bsst_environ  := env;
        bsst_pcond    := pcond;
        bsst_status   := status
      |>
`;

val birs_state_ss = rewrites (type_rws ``:birs_state_t``);

val birs_symb_from_to_symbst_thm = store_thm(
   "birs_symb_from_to_symbst_thm", ``
!s. birs_symb_to_symbst (birs_symb_from_symbst s) = s
``,
  GEN_TAC >>
  Cases_on `s` >>
  FULL_SIMP_TAC (std_ss++symb_TYPES_ss++birs_state_ss)
    [birs_symb_to_symbst_def, birs_symb_from_symbst_def] >>

  METIS_TAC []
);

val birs_symb_to_from_symbst_thm = store_thm(
   "birs_symb_to_from_symbst_thm", ``
!s. birs_symb_from_symbst (birs_symb_to_symbst s) = s
``,
  GEN_TAC >>
  Cases_on `s` >>

  FULL_SIMP_TAC (std_ss++symb_TYPES_ss++birs_state_ss)
    [birs_symb_to_symbst_def, birs_symb_from_symbst_def] >>

  Q.ABBREV_TAC `s = <|bsst_pc := b; bsst_environ := f; bsst_status := b0; bsst_pcond := b1|>` >>
  `s.bsst_pc = b /\
   s.bsst_environ = f /\
   s.bsst_status = b0 /\
   s.bsst_pcond = b1` by (
    Q.UNABBREV_TAC `s` >>
    FULL_SIMP_TAC (std_ss++birs_state_ss) []
  ) >>

  Cases_on `s` >>
  FULL_SIMP_TAC (std_ss++birs_state_ss) []
);

val birs_symb_to_symbst_EXISTS_thm = store_thm(
   "birs_symb_to_symbst_EXISTS_thm", ``
!s. ?st. birs_symb_to_symbst st = s
``,
  METIS_TAC [birs_symb_from_to_symbst_thm]
);

val birs_symb_to_symbst_SET_EXISTS_thm = store_thm(
   "birs_symb_to_symbst_SET_EXISTS_thm", ``
!Pi. ?Pi_t. IMAGE birs_symb_to_symbst Pi_t = Pi
``,
  REPEAT STRIP_TAC >>

  Q.EXISTS_TAC `IMAGE birs_symb_from_symbst Pi` >>

  SIMP_TAC (std_ss++PRED_SET_ss)
    [IMAGE_IMAGE, birs_symb_from_to_symbst_thm, o_DEF]
);

val birs_symb_from_symbst_EXISTS_thm = store_thm(
   "birs_symb_from_symbst_EXISTS_thm", ``
!s. ?st. birs_symb_from_symbst st = s
``,
  METIS_TAC [birs_symb_to_from_symbst_thm]
);

val birs_symb_to_symbst_BIJ_thm = store_thm(
   "birs_symb_to_symbst_BIJ_thm", ``
!s1 s2.
  (birs_symb_to_symbst s1 = birs_symb_to_symbst s2) ==>
  (s1 = s2)
``,
  REPEAT GEN_TAC >>
  Cases_on `s1` >> Cases_on `s2` >>

  FULL_SIMP_TAC (std_ss++symb_TYPES_ss++birs_state_ss)
    [birs_symb_to_symbst_def]
);

val birs_state_is_terminated_def = Define `
    birs_state_is_terminated st =
      (st.bsst_status <> BST_Running)
`;
val birs_state_set_typeerror_def = Define `
    birs_state_set_typeerror st =
      (st with bsst_status := BST_TypeError)`;
val birs_state_set_failed_def = Define `
    birs_state_set_failed st =
      (st with bsst_status := BST_Failed)
`;


(* now the definition of a symbolic execution step *)


(* ... *)

val birs_exec_stmt_assign_def = Define `
    birs_exec_stmt_assign v ex (st : birs_state_t) =
      case birs_eval_exp ex st.bsst_environ of
     | SOME (vaex, vaty) =>
         if vaty = bir_var_type v /\ (OPTION_BIND (st.bsst_environ (bir_var_name v)) type_of_bir_exp = SOME vaty) then
           {st with bsst_environ := ((bir_var_name v =+ (SOME vaex)) st.bsst_environ)}
         else
           {birs_state_set_typeerror st}
     | NONE => {birs_state_set_typeerror st}
`;

val birs_exec_stmt_assert_def = Define `
    birs_exec_stmt_assert ex (st : birs_state_t) =
      case birs_eval_exp ex st.bsst_environ of
     | SOME (vaex, BType_Imm Bit1) =>
        {st with bsst_pcond := BExp_BinExp BIExp_And st.bsst_pcond vaex;
         (st with bsst_pcond := BExp_BinExp BIExp_And st.bsst_pcond (BExp_UnaryExp BIExp_Not vaex))
            with bsst_status := BST_AssertionViolated}
     | NONE => {birs_state_set_typeerror st}
     | _ => {birs_state_set_typeerror st}
`;

val birs_exec_stmt_assume_def = Define `
    birs_exec_stmt_assume ex (st : birs_state_t) =
      case birs_eval_exp ex st.bsst_environ of
     | SOME (vaex, BType_Imm Bit1) =>
        {st with bsst_pcond := BExp_BinExp BIExp_And st.bsst_pcond vaex;
         (st with bsst_pcond := BExp_BinExp BIExp_And st.bsst_pcond (BExp_UnaryExp BIExp_Not vaex))
            with bsst_status := BST_AssumptionViolated}
     | NONE => {birs_state_set_typeerror st}
     | _ => {birs_state_set_typeerror st}
`;

val birs_exec_stmt_observe_def = Define `
    birs_exec_stmt_observe oid ec el obf st =
  let
    svol = MAP (\e. birs_eval_exp e st.bsst_environ) el;
  in
   if EXISTS IS_NONE svol then
     ({birs_state_set_typeerror st})
   else
  case birs_eval_exp ec st.bsst_environ of
    | SOME (svob, BType_Imm Bit1) => {st}
    | _ => ({birs_state_set_typeerror st})
`;

val birs_exec_stmtB_def = Define `
   (birs_exec_stmtB (BStmt_Assert ex) st =
     (birs_exec_stmt_assert ex st)) /\
   (birs_exec_stmtB (BStmt_Assume ex) st =
     (birs_exec_stmt_assume ex st)) /\
   (birs_exec_stmtB (BStmt_Assign v ex) st =
     (birs_exec_stmt_assign v ex st)) /\
   (birs_exec_stmtB (BStmt_Observe oid ec el obf) st =
     birs_exec_stmt_observe oid ec el obf st)
`;

(* ... *)

(* TODO: we have a branch with BIR that does not contain an error code in BST_Halted *)
val birs_exec_stmt_halt_def = Define `
    birs_exec_stmt_halt ex (st : birs_state_t) =
      {st with bsst_status := BST_Halted (BVal_Imm (Imm1 0w))}
`;

val birs_exec_stmt_jmp_to_label_def = Define `
    birs_exec_stmt_jmp_to_label p (st : birs_state_t) (l : bir_label_t) =
    if MEM l (bir_labels_of_program p) then
      st with bsst_pc := bir_block_pc l
    else st with bsst_status := (BST_JumpOutside l)
`;

val birs_eval_label_exp_def = Define `
   (birs_eval_label_exp (BLE_Label l) senv pcond = SOME {l}) /\
   (birs_eval_label_exp (BLE_Exp e)   senv pcond =
     case birs_eval_exp e senv of
      | SOME (vaex, BType_Imm _) => SOME {BL_Address iv | ?i. birs_interpret_fun i pcond = SOME bir_val_true /\ birs_interpret_fun i vaex = SOME (BVal_Imm iv)}
      | _ => NONE
   )
`;

val birs_exec_stmt_jmp_def = Define `
    birs_exec_stmt_jmp p le (st : birs_state_t) =
    case birs_eval_label_exp le st.bsst_environ st.bsst_pcond of
      | NONE => {birs_state_set_typeerror st}
      | SOME ls => IMAGE (birs_exec_stmt_jmp_to_label p st) ls
`;

val birs_exec_stmt_cjmp_def = Define `
    birs_exec_stmt_cjmp p ec l1 l2 (st : birs_state_t) =
      case birs_eval_exp ec st.bsst_environ of
     | SOME (vaex, BType_Imm Bit1) =>
        (birs_exec_stmt_jmp p l1 (st with bsst_pcond := BExp_BinExp BIExp_And st.bsst_pcond vaex)) UNION
        (birs_exec_stmt_jmp p l2 (st with bsst_pcond := BExp_BinExp BIExp_And st.bsst_pcond (BExp_UnaryExp BIExp_Not vaex)))
     | NONE => {birs_state_set_typeerror st}
     | _ => {birs_state_set_typeerror st}
`;

val birs_exec_stmtE_def = Define `
   (birs_exec_stmtE p (BStmt_Jmp l) st =
     birs_exec_stmt_jmp p l st) /\
   (birs_exec_stmtE p (BStmt_CJmp e l1 l2) st =
     birs_exec_stmt_cjmp p e l1 l2 st) /\
   (birs_exec_stmtE p (BStmt_Halt ex) st =
     birs_exec_stmt_halt ex st)
`;

val birs_exec_stmt_def = Define `
   (birs_exec_stmt (p:'a bir_program_t) (BStmtB (bst:'a bir_stmt_basic_t)) st =
     let (sts') = birs_exec_stmtB bst st in
     IMAGE (\st'.
     if (birs_state_is_terminated st') then
       (st')
     else
       (st' with bsst_pc updated_by bir_pc_next)) sts') /\
   (birs_exec_stmt p (BStmtE bst) st =
     (birs_exec_stmtE p bst st))
`;

val birs_exec_step_def = Define `
    birs_exec_step p state =
  if (birs_state_is_terminated state) then {state} else
  case (bir_get_current_statement p state.bsst_pc) of
    | NONE => {birs_state_set_failed state}
    | SOME stm => (birs_exec_stmt p stm state)
`;

(* now the symbolic execution record *)
val bir_symb_rec_sbir_def = Define `
  bir_symb_rec_sbir prog =
    <|
      sr_val_true        := bir_val_true;
      sr_mk_exp_symb_f   := BExp_Den;
      sr_mk_exp_conj_f   := BExp_BinExp BIExp_And;
      sr_mk_exp_eq_f     := \e1. if option_CASE (type_of_bir_exp e1) F bir_type_is_Mem then BExp_MemEq e1 else BExp_BinPred BIExp_Equal e1;

      sr_subst_f         := \(s,e). bir_exp_subst1 s e;

      (* symbols of symbolic exepressions *)
      sr_symbols_f       := bir_vars_of_exp;

      (* type business *)
      sr_typeof_val      := type_of_bir_val;
      sr_typeof_symb     := bir_var_type;
      sr_typeof_exp      := type_of_bir_exp;
      sr_ARB_val         := bir_val_default;

      (* interpretation business, type error produces NONE value *)
      sr_interpret_f     := birs_interpret_fun;

      (* finally, concrete and symbolic executions *)
      sr_step_conc       := birs_symb_to_concst o SND o (bir_exec_step prog) o birs_symb_from_concst;

      sr_step_symb       := (IMAGE birs_symb_to_symbst) o (birs_exec_step prog) o birs_symb_from_symbst;
   |>
`;


(* TODO: single step example (with "prototypical" property transfer) *)

(* TODO: multiple step example (and also propert property transfer), best to use the simple motor set function from the beginning. or something equally simple *)

(* TODO: want to have another simple instance language? *)

(* TODO: have to think how to add memory structure expressions on top of BIR expressions, possibly make another instance! *)

val _ = export_theory();
