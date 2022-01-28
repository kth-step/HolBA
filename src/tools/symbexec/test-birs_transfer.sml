
open HolKernel Parse boolLib bossLib;

open bir_symbTheory;

open birs_stepLib;
open birs_composeLib;

open birs_auxTheory;



  open birs_stepLib;

open symb_recordTheory;
open symb_prop_transferTheory;
open bir_symbTheory;

open bir_symb_sound_coreTheory;
open HolBACoreSimps;
open symb_interpretTheory;
open pred_setTheory;

open bir_exp_substitutionsTheory;
open birs_composeLib;
open birs_auxTheory;

val birs_state_ss = rewrites (type_rws ``:birs_state_t``);

(* testing *)
val bprog_test_def = Define `
    bprog_test =
BirProgram [
           <|bb_label := BL_Address (Imm32 2826w);
             bb_statements :=
               [BStmt_Assert
                  (BExp_BinPred BIExp_LessOrEqual
                     (BExp_Den (BVar "countw" (BType_Imm Bit64)))
                     (BExp_Const (Imm64 0xFFFFFFFFFFFFFFFEw)));
                BStmt_Assign (BVar "countw" (BType_Imm Bit64))
                  (BExp_BinExp BIExp_Plus
                     (BExp_Den (BVar "countw" (BType_Imm Bit64)))
                     (BExp_Const (Imm64 1w)))];
             bb_last_statement :=
               BStmt_Jmp (BLE_Label (BL_Address (Imm32 2828w)))|>
] : 'obs_type bir_program_t
`;
val bprog = (fst o dest_eq o concl) bprog_test_def;

val birs_state_init_lbl = (snd o dest_eq o concl o EVAL) ``bir_pc_next (bir_block_pc (BL_Address (Imm32 2826w)))``;






val bir_senv_GEN_bvar_def = Define `
    bir_senv_GEN_bvar (vn,ty) = BVar (CONCAT["sy_";vn]) ty
`;
val bir_senv_GEN_bvar_EQ_thm = store_thm(
   "bir_senv_GEN_bvar_EQ_thm", ``
!x y.
  bir_senv_GEN_bvar x = bir_senv_GEN_bvar y <=> x = y
``,
  Cases_on `x` >> Cases_on `y` >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_senv_GEN_bvar_def] >>

  ASSUME_TAC (INST_TYPE [Type.alpha |-> Type`:char`] (prove(
    ``!A B C. FLAT [A;B] = FLAT [A;C] <=> B = C``,
      SIMP_TAC (std_ss++listSimps.LIST_ss) [listTheory.FLAT_compute, listTheory.FLAT]
  ))) >>

  METIS_TAC []
);

val bir_senv_GEN_list_def = Define `
    bir_senv_GEN_list l = FOLDR (\(vn,ty). \f. (vn =+ SOME (BExp_Den (bir_senv_GEN_bvar (vn,ty)))) f) (K NONE) l
`;
(*
("R7"         =+ (SOME (BExp_Den (BVar "sy_R7" (BType_Imm Bit32)))))
                   (("SP_process" =+ (SOME (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)))))
                      (("countw"     =+ (SOME (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))))
                       (K NONE)
                   ))
*)
val bir_senv_GEN_list_NOT_MEM_thm = store_thm(
   "bir_senv_GEN_list_NOT_MEM_thm", ``
!vn l.
  (~(MEM vn (MAP FST l))) ==>
  (bir_senv_GEN_list l vn = NONE)
``,
  Induct_on `l` >- (
    SIMP_TAC std_ss [listTheory.MEM, bir_senv_GEN_list_def, listTheory.FOLDR]
  ) >>
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [listTheory.MAP, listTheory.MEM] >>
  SIMP_TAC std_ss [bir_senv_GEN_list_def] >>
  FULL_SIMP_TAC std_ss [listTheory.FOLDR] >>
  SIMP_TAC std_ss [GSYM bir_senv_GEN_list_def] >>

  Cases_on `h` >>
  FULL_SIMP_TAC std_ss [pairTheory.FST, combinTheory.APPLY_UPDATE_THM]
);
val bir_senv_GEN_list_APPLY_thm = store_thm(
   "bir_senv_GEN_list_APPLY_thm", ``
!vn ty l.
  (MEM (vn,ty) l) ==>
  (ALL_DISTINCT (MAP FST l)) ==>
  (bir_senv_GEN_list l vn = SOME (BExp_Den (bir_senv_GEN_bvar (vn,ty))))
``,
  Induct_on `l` >> (
    SIMP_TAC std_ss [listTheory.MEM]
  ) >>

  REPEAT STRIP_TAC >- (
    SIMP_TAC std_ss [bir_senv_GEN_list_def, listTheory.FOLDR] >>
    Cases_on `h` >>
    FULL_SIMP_TAC std_ss [combinTheory.APPLY_UPDATE_THM]
  ) >>

  FULL_SIMP_TAC std_ss [listTheory.MAP, listTheory.ALL_DISTINCT] >>
  SIMP_TAC std_ss [bir_senv_GEN_list_def, listTheory.FOLDR] >>
  Cases_on `h` >>

  `q <> vn` by (
    METIS_TAC [listTheory.MEM_MAP_f, pairTheory.FST]
  ) >>
  FULL_SIMP_TAC std_ss [combinTheory.APPLY_UPDATE_THM] >>
  SIMP_TAC std_ss [GSYM bir_senv_GEN_list_def] >>
  METIS_TAC []
);
val MEM_FST_IMP_MEM_thm = store_thm(
   "MEM_FST_IMP_MEM_thm", ``
!vn l.
  (MEM vn (MAP FST l)) ==>
  (?ty. MEM (vn,ty) l)
``,
  REPEAT STRIP_TAC >>
  CCONTR_TAC >>
  FULL_SIMP_TAC (std_ss++listSimps.LIST_ss) [listTheory.MEM_MAP] >>
  Cases_on `y` >>
  FULL_SIMP_TAC (std_ss++listSimps.LIST_ss) [] >>
  METIS_TAC []
);
val bir_interpr_GEN_list_def = Define `
    bir_interpr_GEN_list l envf = FOLDR (\(vn,ty). \f. ((bir_senv_GEN_bvar (vn,ty)) =+ envf vn) f) (K NONE) l
`;
(*
  Q.EXISTS_TAC `SymbInterpret
    ((BVar "sy_R7" (BType_Imm Bit32) =+ SOME v_R7)
    ((BVar "sy_SP_process" (BType_Imm Bit32) =+ SOME v_SP_process)
    ((BVar "sy_countw" (BType_Imm Bit64) =+ SOME v_countw) (K NONE))))` >>
*)
val bir_interpr_GEN_list_NOT_MEM_thm = store_thm(
   "bir_interpr_GEN_list_NOT_MEM_thm", ``
!vn ty l f.
  (~(MEM vn (MAP FST l))) ==>
  (bir_interpr_GEN_list l f (bir_senv_GEN_bvar (vn,ty)) = NONE)
``,
  Induct_on `l` >- (
    SIMP_TAC std_ss [listTheory.MEM, bir_interpr_GEN_list_def, listTheory.FOLDR]
  ) >>
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [listTheory.MAP, listTheory.MEM] >>
  SIMP_TAC std_ss [bir_interpr_GEN_list_def] >>
  FULL_SIMP_TAC std_ss [listTheory.FOLDR] >>
  SIMP_TAC std_ss [GSYM bir_interpr_GEN_list_def] >>

  Cases_on `h` >>
  FULL_SIMP_TAC std_ss [pairTheory.FST, combinTheory.APPLY_UPDATE_THM, bir_senv_GEN_bvar_EQ_thm]
);
val bir_interpr_GEN_list_APPLY_thm = store_thm(
   "bir_interpr_GEN_list_APPLY_thm", ``
!vn ty l f.
  (MEM (vn,ty) l) ==>
  (ALL_DISTINCT (MAP FST l)) ==>
  (bir_interpr_GEN_list l f (bir_senv_GEN_bvar (vn,ty)) = f vn)
``,
  Induct_on `l` >> (
    SIMP_TAC std_ss [listTheory.MEM]
  ) >>

  REPEAT STRIP_TAC >- (
    SIMP_TAC std_ss [bir_interpr_GEN_list_def, listTheory.FOLDR] >>
    Cases_on `h` >>
    FULL_SIMP_TAC std_ss [combinTheory.APPLY_UPDATE_THM]
  ) >>

  FULL_SIMP_TAC std_ss [listTheory.MAP, listTheory.ALL_DISTINCT] >>
  SIMP_TAC std_ss [bir_interpr_GEN_list_def, listTheory.FOLDR] >>
  Cases_on `h` >>

  `q <> vn` by (
    METIS_TAC [listTheory.MEM_MAP_f, pairTheory.FST]
  ) >>
  FULL_SIMP_TAC std_ss [combinTheory.APPLY_UPDATE_THM, bir_senv_GEN_bvar_EQ_thm] >>
  SIMP_TAC std_ss [GSYM bir_interpr_GEN_list_def] >>
  METIS_TAC []
);
val bir_interpr_GEN_list_APPLY2_thm = store_thm(
   "bir_interpr_GEN_list_APPLY2_thm", ``
!vn l f.
  (MEM vn (MAP FST l)) ==>
  (?ty. bir_interpr_GEN_list l f (bir_senv_GEN_bvar (vn,ty)) = f vn)
``,
  Induct_on `l` >> (
    SIMP_TAC std_ss [listTheory.MEM, listTheory.MAP]
  ) >>

  REPEAT STRIP_TAC >- (
    SIMP_TAC std_ss [bir_interpr_GEN_list_def, listTheory.FOLDR] >>
    Cases_on `h` >>
    FULL_SIMP_TAC std_ss [combinTheory.APPLY_UPDATE_THM] >>
    METIS_TAC []
  ) >>

  FULL_SIMP_TAC std_ss [listTheory.MAP, listTheory.ALL_DISTINCT] >>
  SIMP_TAC std_ss [bir_interpr_GEN_list_def, listTheory.FOLDR] >>
  Cases_on `h` >>

  FULL_SIMP_TAC std_ss [] >>
  PAT_X_ASSUM ``!x.A`` (ASSUME_TAC o Q.SPECL [`vn`, `f`]) >>
  REV_FULL_SIMP_TAC std_ss [] >>
  Q.EXISTS_TAC `ty` >>
  REV_FULL_SIMP_TAC std_ss [] >>

  FULL_SIMP_TAC std_ss [combinTheory.APPLY_UPDATE_THM, bir_senv_GEN_bvar_EQ_thm] >>
  SIMP_TAC std_ss [GSYM bir_interpr_GEN_list_def] >>
  METIS_TAC []
);

val bir_interpr_GEN_list_IS_SOME_IMP_EXISTS_thm = store_thm(
   "bir_interpr_GEN_list_IS_SOME_IMP_EXISTS_thm", ``
!l f bv.
  (IS_SOME (bir_interpr_GEN_list l f bv)) ==>
  (?vn ty. bv = bir_senv_GEN_bvar (vn, ty) /\ (MEM (vn,ty) l))
(*
  (?vn ty. bv = bir_senv_GEN_bvar (vn, ty) /\ (MEM vn (MAP FST l) ==> MEM (vn,ty) l))
*)
``,
  Induct_on `l` >> (
    SIMP_TAC std_ss [bir_interpr_GEN_list_def, listTheory.FOLDR]
  ) >>

  REPEAT STRIP_TAC >>
  Cases_on `h` >>
  FULL_SIMP_TAC std_ss [combinTheory.APPLY_UPDATE_THM] >>

  CCONTR_TAC >>
  FULL_SIMP_TAC std_ss [GSYM bir_interpr_GEN_list_def] >>

  Cases_on `bir_senv_GEN_bvar (q,r) = bv` >- (
    FULL_SIMP_TAC std_ss [listTheory.MEM] >>
    METIS_TAC [bir_senv_GEN_bvar_EQ_thm]
  ) >>


  FULL_SIMP_TAC std_ss [] >>
  METIS_TAC [listTheory.MEM]
);





val birenvtyl_def = Define `
    birenvtyl = [("R7", BType_Imm Bit32); ("SP_process", BType_Imm Bit32); ("countw", BType_Imm Bit64)]
`;

val birs_state_init = ``<|
  bsst_pc       := ^birs_state_init_lbl;
  bsst_environ  := bir_senv_GEN_list birenvtyl;
  bsst_status   := BST_Running;
  bsst_pcond    := BExp_Const (Imm1 1w)
|>``;
(* ........................... *)

val bprog_tm = bprog;
val birs_rule_STEP_thm = birs_rule_STEP_prog_fun bprog_tm (bir_prog_has_no_halt_fun bprog_tm);
val birs_rule_STEP_fun_spec = birs_rule_STEP_fun birs_rule_STEP_thm bprog_tm;
(* ........................... *)

(* first step *)
val single_step_thm = birs_rule_STEP_fun_spec birs_state_init;

val exec_thm = single_step_thm;
val (sys_tm, L_tm, Pi_tm) = (symb_sound_struct_get_sysLPi_fun o concl) exec_thm;
(* ........................... *)

(* now the transfer *)
(* ........................... *)

(* prepare property transfer theorem *)
val birs_symb_symbols_f_sound_prog_thm =
  (SPEC (inst [Type`:'obs_type` |-> Type.alpha] bprog) bir_symb_soundTheory.birs_symb_symbols_f_sound_thm);

val birs_prop_transfer_thm =
  (MATCH_MP symb_prop_transferTheory.symb_prop_transfer_thm birs_symb_symbols_f_sound_prog_thm);
(* ........................... *)




val bir_envty_list_inclusive_def = Define `
    bir_envty_list_inclusive l env = EVERY (\(vn,ty). ?v. env vn = SOME v /\ type_of_bir_val v = ty) l
`;
val bir_envty_list_exclusive_def = Define `
    bir_envty_list_exclusive l env = (!vn. (~(EXISTS (\(vni,ty). vni = vn) l)) ==> (env vn = NONE))
`;
(* TODO: should add "(ALL_DISTINCT (MAP FST l)) /\" and simplify the story below... *)
val bir_envty_list_def = Define `
    bir_envty_list l env = (bir_envty_list_inclusive l env /\ bir_envty_list_exclusive l env)
`;
val bir_envty_list_MEM_IMP_thm = store_thm(
   "bir_envty_list_MEM_IMP_thm", ``
!vn ty l f.
  (MEM (vn,ty) l) ==>
  (bir_envty_list l f) ==>
  (?v. f vn = SOME v /\ type_of_bir_val v = ty)
``,
  REWRITE_TAC [bir_envty_list_def, bir_envty_list_inclusive_def, listTheory.EVERY_MEM] >>
  REPEAT STRIP_TAC >>
  PAT_X_ASSUM ``!x.A`` (ASSUME_TAC o Q.SPEC `(vn,ty)`) >>
  FULL_SIMP_TAC std_ss []
);
val NOT_MEM_FST_IMP_thm = store_thm(
   "NOT_MEM_FST_IMP_thm", ``
!vn l.
  (~(MEM vn (MAP FST l))) ==>
  (!e. ~(MEM e l) \/ ~((\(vni,ty). vni = vn) e))
``,
  REPEAT STRIP_TAC >>
  Cases_on `e` >>
  Cases_on `q = vn` >- (
    METIS_TAC [listTheory.MEM_MAP_f, pairTheory.FST]
  ) >>
  FULL_SIMP_TAC std_ss []
);
val bir_envty_list_NOT_MEM_IMP_thm = store_thm(
   "bir_envty_list_NOT_MEM_IMP_thm", ``
!vn l f.
  (~(MEM vn (MAP FST l))) ==>
  (bir_envty_list l f) ==>
  (f vn = NONE)
``,
  REWRITE_TAC [bir_envty_list_def, bir_envty_list_exclusive_def, listTheory.EXISTS_MEM] >>
  REPEAT STRIP_TAC >>
  PAT_X_ASSUM ``!x.A`` (ASSUME_TAC o Q.SPEC `vn`) >>
  FULL_SIMP_TAC std_ss [boolTheory.NOT_EXISTS_THM, NOT_MEM_FST_IMP_thm]
);

(*
val bir_envty_list_IS_SOME_IMP_thm = store_thm(
   "bir_envty_list_IS_SOME_IMP_thm", ``
!l f vn.
  (bir_envty_list l f) ==>
  (ALL_DISTINCT (MAP FST l)) ==>
  (IS_SOME (f vn)) ==>
  (MEM vn (MAP FST l))
``,
  cheat
);
*)


val bir_envty_list_b_def = Define `
    bir_envty_list_b l (BEnv env) = bir_envty_list l env
`;
val bir_envty_list_b_thm = store_thm(
   "bir_envty_list_b_thm", ``
!l env.
  bir_envty_list_b l env = bir_envty_list l (λbvn. bir_env_lookup bvn env)
``,
  REPEAT STRIP_TAC >>
  Cases_on `env` >>
  FULL_SIMP_TAC (std_ss) [bir_envty_list_b_def, bir_envTheory.bir_env_lookup_def] >>
  METIS_TAC []
);

(* basic definitions for the property we want to prove (countw) *)
val bprog_P_def = Define `
    bprog_P ((SymbConcSt pc st status):(bir_programcounter_t, string, bir_val_t, bir_status_t) symb_concst_t) =
      (status = BST_Running /\
       bir_envty_list birenvtyl st)
`;
(* translate the property to BIR state property *)
val bprog_P_thm = store_thm(
   "bprog_P_thm", ``
!bs.
  bprog_P (birs_symb_to_concst bs) =
      (bs.bst_status = BST_Running /\
       bir_envty_list_b birenvtyl bs.bst_environ)
``,
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC (std_ss) [birs_symb_to_concst_def, bprog_P_def, bir_envty_list_b_thm]
);

(* this is the relevant property about the cycle counter *)
val bprog_Q_def = Define `
    bprog_Q
     ((SymbConcSt pc1 st1 status1):(bir_programcounter_t, string, bir_val_t, bir_status_t) symb_concst_t)
     ((SymbConcSt pc2 st2 status2):(bir_programcounter_t, string, bir_val_t, bir_status_t) symb_concst_t)
    =
     (?v. st1 "countw" = SOME (BVal_Imm (Imm64 v)) /\ st2 "countw" = SOME (BVal_Imm (Imm64 (v + 1w))))
`;
val bprog_Q_thm = store_thm(
   "bprog_Q_thm", ``
!bs1 bs2.
  bprog_Q (birs_symb_to_concst bs1) (birs_symb_to_concst bs2) =
    (?v. bir_env_lookup "countw" bs1.bst_environ = SOME (BVal_Imm (Imm64 v)) /\
         bir_env_lookup "countw" bs2.bst_environ = SOME (BVal_Imm (Imm64 (v + 1w))))
``,
  FULL_SIMP_TAC (std_ss) [birs_symb_to_concst_def, bprog_Q_def]
);
(* ........................... *)

(* P is generic enough *)

val birs_matchenv_bir_senv_GEN_thm = store_thm(
   "birs_matchenv_bir_senv_GEN_thm", ``
!l f.
  (bir_envty_list l f) ==>
  (ALL_DISTINCT (MAP FST l)) ==>
  (birs_matchenv (SymbInterpret (bir_interpr_GEN_list l f))
          (bir_senv_GEN_list l) (BEnv f))
``,
  SIMP_TAC std_ss [birs_matchenv_def] >>
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [bir_envTheory.bir_env_lookup_def] >>

  Cases_on `MEM var (MAP FST l)` >- (
    IMP_RES_TAC MEM_FST_IMP_MEM_thm >>
    IMP_RES_TAC bir_envty_list_MEM_IMP_thm >>
    IMP_RES_TAC bir_senv_GEN_list_APPLY_thm >>
    FULL_SIMP_TAC std_ss [] >>

    FULL_SIMP_TAC std_ss [birs_interpret_fun_thm, birs_interpret_fun_ALT_def] >>
    FULL_SIMP_TAC std_ss [birs_interpret_get_var_thm, bir_interpr_GEN_list_APPLY_thm]
  ) >>

  IMP_RES_TAC bir_envty_list_NOT_MEM_IMP_thm >>
  IMP_RES_TAC bir_senv_GEN_list_NOT_MEM_thm >>
  FULL_SIMP_TAC std_ss []
);

(*
val bir_interpr_GEN_list_IS_SOME_IMP_thm = store_thm(
   "bir_interpr_GEN_list_IS_SOME_IMP_thm", ``
!l f bv.
  (bir_envty_list l f) ==>
  (ALL_DISTINCT (MAP FST l)) ==>
  (IS_SOME (bir_interpr_GEN_list l f bv)) ==>
  (?vn ty. bv = bir_senv_GEN_bvar (vn, ty) /\ MEM (vn, ty) l)
``,
  REPEAT STRIP_TAC >>


  IMP_RES_TAC bir_interpr_GEN_list_IS_SOME_IMP_EXISTS_thm >>
  FULL_SIMP_TAC (std_ss) [bir_interpr_GEN_list_APPLY_thm]
bir_envty_list_IS_SOME_IMP_thm

);
*)

val symb_interpr_dom_bir_interpr_GEN_list_thm = store_thm(
   "symb_interpr_dom_bir_interpr_GEN_list_thm", ``
!l f.
  (bir_envty_list l f) ==>
  (ALL_DISTINCT (MAP FST l)) ==>
  (symb_interpr_dom (SymbInterpret (bir_interpr_GEN_list l f))
   =
   set (MAP bir_senv_GEN_bvar l))
``,
  SIMP_TAC std_ss [symb_interpr_dom_def] >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [EXTENSION] >>
  FULL_SIMP_TAC (std_ss) [listTheory.MEM_MAP] >>

  REPEAT STRIP_TAC >>
  EQ_TAC >- (
    REPEAT STRIP_TAC >>

(*
    Cases_on `x` >>
    rename1 `BVar vn ty` >>
*)
    FULL_SIMP_TAC (pure_ss) [GSYM optionTheory.NOT_IS_SOME_EQ_NONE] >>
    FULL_SIMP_TAC (std_ss) [] >>
(*
    FULL_SIMP_TAC (std_ss) [optionTheory.IS_SOME_EXISTS] >>
*)

    METIS_TAC [bir_interpr_GEN_list_IS_SOME_IMP_EXISTS_thm]
(*
    METIS_TAC [bir_interpr_GEN_list_SOME_IMP_EXISTS_thm]
*)
  ) >>

  REPEAT STRIP_TAC >>
  Cases_on `y` >>

  REV_FULL_SIMP_TAC (std_ss) [bir_interpr_GEN_list_APPLY_thm] >>


  IMP_RES_TAC bir_envty_list_MEM_IMP_thm >>
  FULL_SIMP_TAC (std_ss) []
);

val birs_interpr_welltyped_bir_interpr_GEN_list_thm = store_thm(
   "birs_interpr_welltyped_bir_interpr_GEN_list_thm", ``
!l f.
  (bir_envty_list l f) ==>
  (ALL_DISTINCT (MAP FST l)) ==>
  (birs_interpr_welltyped (SymbInterpret (bir_interpr_GEN_list l f)))
``,
  SIMP_TAC std_ss [birs_interpr_welltyped_def, symb_interpr_dom_bir_interpr_GEN_list_thm, symb_interpr_get_def] >>
  FULL_SIMP_TAC (std_ss) [listTheory.MEM_MAP] >>
  REPEAT STRIP_TAC >>

  Cases_on `y` >>
  FULL_SIMP_TAC (std_ss) [bir_interpr_GEN_list_APPLY_thm] >>

  IMP_RES_TAC bir_envty_list_MEM_IMP_thm >>
  FULL_SIMP_TAC (std_ss) [bir_envTheory.bir_var_type_def, bir_senv_GEN_bvar_def]
);

val symb_interpr_for_symbs_bir_interpr_GEN_list_thm = store_thm(
   "symb_interpr_for_symbs_bir_interpr_GEN_list_thm", ``
!l f lbl status.
  (bir_envty_list l f) ==>
  (ALL_DISTINCT (MAP FST l)) ==>
  (symb_interpr_for_symbs
          (birs_symb_symbols
             <|bsst_pc := lbl; bsst_environ := bir_senv_GEN_list l;
               bsst_status := status; bsst_pcond := BExp_Const (Imm1 1w)|>)
          (SymbInterpret (bir_interpr_GEN_list l f)))
``,
  FULL_SIMP_TAC std_ss [symb_interpr_for_symbs_def, symb_interpr_dom_bir_interpr_GEN_list_thm] >>
  FULL_SIMP_TAC (std_ss++birs_state_ss++holBACore_ss) [birs_symb_symbols_def, UNION_EMPTY] >>

  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [pred_setTheory.SUBSET_DEF] >>

  REPEAT STRIP_TAC >>
  `MEM vn (MAP FST l)` by (
    CCONTR_TAC >>
    IMP_RES_TAC bir_senv_GEN_list_NOT_MEM_thm >>
    FULL_SIMP_TAC (std_ss) []
  ) >>

  IMP_RES_TAC MEM_FST_IMP_MEM_thm >>
  IMP_RES_TAC bir_senv_GEN_list_APPLY_thm >>
  FULL_SIMP_TAC (std_ss) [] >>

  `x = bir_senv_GEN_bvar (vn,ty)` by (
    PAT_X_ASSUM ``BExp_Den A = B`` (ASSUME_TAC o GSYM) >>
    FULL_SIMP_TAC (std_ss) [IN_SING, bir_typing_expTheory.bir_vars_of_exp_def]
  ) >>

  METIS_TAC [listTheory.MEM_MAP_f]
);


val bprog_P_entails_gen_thm = store_thm(
   "bprog_P_entails_gen_thm", ``
!lbl status l f.
  (bir_envty_list l f) ==>
  (ALL_DISTINCT (MAP FST l)) ==>
  (?H. birs_symb_matchstate
              <|bsst_pc := lbl;
                bsst_environ := bir_senv_GEN_list l;
                bsst_status := status;
                bsst_pcond := BExp_Const (Imm1 1w)|> H
              (bir_state_t
                 lbl
                 (BEnv f)
                 status)
  )
``,
  REPEAT STRIP_TAC >>
  Q.EXISTS_TAC `SymbInterpret (bir_interpr_GEN_list l f)` >>

  `!H. birs_interpret_fun H (BExp_Const (Imm1 1w)) = SOME bir_val_true` by (
    EVAL_TAC >>
    REWRITE_TAC []
  ) >>

  FULL_SIMP_TAC (std_ss) [birs_symb_matchstate_def] >>
  REPEAT STRIP_TAC >> (
    FULL_SIMP_TAC (std_ss++birs_state_ss++holBACore_ss) []
  ) >> (
    ASM_REWRITE_TAC []
  ) >> (
    FULL_SIMP_TAC std_ss [
      birs_matchenv_bir_senv_GEN_thm,
      birs_interpr_welltyped_bir_interpr_GEN_list_thm,
      symb_interpr_for_symbs_bir_interpr_GEN_list_thm]
  )
);

val string_ss = rewrites (type_rws ``:string``);
val bprog_P_entails_thm = store_thm(
   "bprog_P_entails_thm", ``
P_entails_an_interpret (bir_symb_rec_sbir bprog_test) bprog_P ^sys_tm
``,
  FULL_SIMP_TAC (std_ss++birs_state_ss) [P_entails_an_interpret_def] >>
  REPEAT STRIP_TAC >>

  ASSUME_TAC ((GSYM o Q.SPEC `s`) birs_symb_to_concst_EXISTS_thm) >>
  FULL_SIMP_TAC (std_ss++birs_state_ss) [birs_symb_matchstate_EQ_thm] >>

  FULL_SIMP_TAC (std_ss++birs_state_ss) [birs_symb_to_symbst_def, symb_symbst_pc_def] >>

  Cases_on `s` >> Cases_on `st` >>
  FULL_SIMP_TAC (std_ss++holBACore_ss++symb_typesLib.symb_TYPES_ss) [bprog_P_def, birs_symb_to_concst_def, symb_concst_pc_def] >>

  Cases_on `b0` >>
  FULL_SIMP_TAC (std_ss) [bir_envTheory.bir_env_lookup_def] >>
  PAT_X_ASSUM ``A = (\B. C)`` (ASSUME_TAC o GSYM) >>
  FULL_SIMP_TAC (std_ss) [boolTheory.ETA_THM] >>

  `(ALL_DISTINCT (MAP FST birenvtyl))` by EVAL_TAC >>

  METIS_TAC [bprog_P_entails_gen_thm]
);

(*
  Q.EXISTS_TAC `SymbInterpret
    ((BVar "sy_R7" (BType_Imm Bit32) =+ SOME v_R7)
    ((BVar "sy_SP_process" (BType_Imm Bit32) =+ SOME v_SP_process)
    ((BVar "sy_countw" (BType_Imm Bit64) =+ SOME v_countw) (K NONE))))` >>

  FULL_SIMP_TAC (std_ss) [birs_symb_matchstate_def] >>

  REPEAT STRIP_TAC >> (
    FULL_SIMP_TAC (std_ss++birs_state_ss++holBACore_ss) []
  ) >- (
    FULL_SIMP_TAC (std_ss) [symb_interpr_for_symbs_def] >>
    FULL_SIMP_TAC (std_ss++birs_state_ss) [symb_interpr_dom_def, birs_symb_symbols_def, bir_typing_expTheory.bir_vars_of_exp_def] >>
    FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [pred_setTheory.SUBSET_DEF] >>
    REPEAT STRIP_TAC >>
    Cases_on `vn = "countw"` >> Cases_on `vn = "SP_process"` >> Cases_on `vn = "R7"` >> (
      FULL_SIMP_TAC (std_ss++stringSimps.STRING_ss++string_ss) [combinTheory.APPLY_UPDATE_THM] >>
      PAT_X_ASSUM ``BExp_Den A = B`` (ASSUME_TAC o GSYM) >>
      FULL_SIMP_TAC (std_ss++holBACore_ss) [IN_SING] >>
      REV_FULL_SIMP_TAC (std_ss++holBACore_ss++string_ss) []
    )
  ) >- (
    FULL_SIMP_TAC (std_ss) [birs_interpr_welltyped_def] >>
    FULL_SIMP_TAC (std_ss++birs_state_ss) [symb_interpr_dom_def] >>
    FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>
    REPEAT STRIP_TAC >>
    Cases_on `sy = BVar "sy_countw" (BType_Imm Bit64)` >> Cases_on `sy = BVar "sy_SP_process" (BType_Imm Bit32)` >> Cases_on `sy = BVar "sy_R7" (BType_Imm Bit32)` >> (
      FULL_SIMP_TAC (std_ss++stringSimps.STRING_ss++string_ss++holBACore_ss) [symb_interpr_get_def, combinTheory.APPLY_UPDATE_THM]
    )
  ) >- (
    FULL_SIMP_TAC (std_ss) [birs_matchenv_def] >>
    REPEAT STRIP_TAC >>
    Cases_on `var = "countw"` >> Cases_on `var = "SP_process"` >> Cases_on `var = "R7"` >> (
      FULL_SIMP_TAC (std_ss++stringSimps.STRING_ss++string_ss) [combinTheory.APPLY_UPDATE_THM] >>
      REWRITE_TAC [birs_interpret_fun_thm] >>
      EVAL_TAC
    ) >>
    METIS_TAC []
  ) >>

  EVAL_TAC
);
*)
(* ........................... *)

(* Q is implied by sys and Pi *)
val bprog_Pi_overapprox_Q_thm = store_thm(
   "bprog_Pi_overapprox_Q_thm", ``
Pi_overapprox_Q (bir_symb_rec_sbir bprog_test) bprog_P ^sys_tm ^Pi_tm bprog_Q
``,
  FULL_SIMP_TAC (std_ss++birs_state_ss) [Pi_overapprox_Q_def] >>
  REPEAT STRIP_TAC >>

  ASSUME_TAC ((GSYM o Q.SPEC `s`) birs_symb_to_concst_EXISTS_thm) >>
  FULL_SIMP_TAC (std_ss) [] >>
  ASSUME_TAC ((GSYM o Q.SPEC `s'`) birs_symb_to_concst_EXISTS_thm) >>
  FULL_SIMP_TAC (std_ss) [] >>

  FULL_SIMP_TAC (std_ss) [pred_setTheory.IMAGE_INSERT, pred_setTheory.IMAGE_EMPTY, pred_setTheory.IN_INSERT] >> REPEAT STRIP_TAC >> (
    FULL_SIMP_TAC (std_ss) [pred_setTheory.NOT_IN_EMPTY]
  ) >> (
    PAT_X_ASSUM ``A = birs_symb_to_symbst B`` (fn thm => FULL_SIMP_TAC std_ss [thm]) >>

    FULL_SIMP_TAC (std_ss) [bprog_Q_thm] >>
    FULL_SIMP_TAC (std_ss) [symb_matchstate_ext_def, birs_symb_matchstate_EQ_thm] >>

    FULL_SIMP_TAC (std_ss++birs_state_ss) [birs_symb_matchstate_def] >>

    REPEAT (PAT_X_ASSUM ``symb_interpr_for_symbs (birs_symb_symbols A) B``
      (fn thm =>
         let
           val tm = (hd o snd o strip_comb o concl) thm;
(*           val _ = print_term tm; *)
           val conv = SIMP_CONV std_ss [birs_symb_symbols_thm] THENC SIMP_CONV (std_ss++birs_state_ss) [birs_exps_of_senv_thm, birs_exps_of_senv_COMP_thm] THENC EVAL;
           val thm_res = (computeLib.RESTR_EVAL_CONV [``birs_symb_symbols``] THENC conv) tm;
(*           val _ = print_term (concl thm_res); *)
         in
           ASSUME_TAC (REWRITE_RULE [Once thm_res] thm)
         end)) >>

    `BVar "sy_countw" (BType_Imm Bit64) IN symb_interpr_dom H` by (
      FULL_SIMP_TAC (std_ss) [symb_interpr_for_symbs_def, INSERT_SUBSET]
    ) >>
    `BVar "sy_countw" (BType_Imm Bit64) IN symb_interpr_dom H'` by (
      FULL_SIMP_TAC (std_ss) [symb_interpr_for_symbs_def, INSERT_SUBSET]
    ) >>

    FULL_SIMP_TAC (std_ss++birs_state_ss) [birs_matchenv_def] >>
    REPEAT (PAT_X_ASSUM ``!A.B`` (ASSUME_TAC o EVAL_RULE o Q.SPEC `"countw"`)) >>
    FULL_SIMP_TAC (std_ss) [] >>

    `symb_interpr_get H' (BVar "sy_countw" (BType_Imm Bit64)) = symb_interpr_get H (BVar "sy_countw" (BType_Imm Bit64))` by (
      FULL_SIMP_TAC std_ss [symb_interpr_ext_def, symb_interprs_eq_for_def]
    ) >>

    FULL_SIMP_TAC (std_ss++birs_state_ss) [birs_interpr_welltyped_def] >>
    REPEAT (PAT_X_ASSUM ``!A.B`` (ASSUME_TAC o EVAL_RULE o Q.SPEC `BVar "sy_countw" (BType_Imm Bit64)`)) >>
    FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
    REV_FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>

    Cases_on `symb_interpr_get H (BVar "sy_countw" (BType_Imm Bit64))` >- (
      METIS_TAC [symb_interpr_dom_IMP_get_CASES_thm, optionTheory.option_CLAUSES]
    ) >>
    FULL_SIMP_TAC (std_ss++holBACore_ss) [optionTheory.option_CLAUSES] >>

    FULL_SIMP_TAC (std_ss) [bir_typing_expTheory.bir_vars_of_exp_def, UNION_EMPTY, bir_exp_subst_def, bir_exp_subst_var_def, FINITE_SING, finite_mapTheory.FLOOKUP_FUN_FMAP, IN_SING, birs_interpret_subst_fmap_get_def] >>
    REV_FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>

    `bir_val_is_Imm_s Bit64 x` by (
      METIS_TAC [bir_valuesTheory.bir_val_checker_TO_type_of]
    ) >>
    FULL_SIMP_TAC std_ss [bir_valuesTheory.bir_val_is_Imm_s_def, bir_immTheory.n2bs_def] >>

    FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_val_to_constexp_def] >>
    REPEAT (PAT_X_ASSUM ``BVal_Imm (Imm64 (n2w B)) = A`` (ASSUME_TAC o GSYM)) >>
    FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_val_to_constexp_def]
  )
);
(* ........................... *)

(* apply the theorem for property transfer *)
val bprog_prop_holds_thm =
  MATCH_MP
    (MATCH_MP
      (MATCH_MP
         birs_prop_transfer_thm
         bprog_P_entails_thm)
      bprog_Pi_overapprox_Q_thm)
    single_step_thm;

(* lift to concrete state property *)
val bprog_concst_prop_thm =
  SIMP_RULE (std_ss++birs_state_ss)
    [birs_symb_symbst_pc_thm]
    (REWRITE_RULE
      [symb_prop_transferTheory.prop_holds_def]
      bprog_prop_holds_thm);


(* lift to concrete bir property *)
val bprog_bir_prop_thm = save_thm(
   "bprog_bir_prop_thm",
  (* TODO: finish translation to pure BIR property *)
  REWRITE_RULE [birs_symb_to_concst_EXISTS_thm, bprog_P_thm, bprog_Q_thm, birs_symb_concst_pc_thm]
    (HO_MATCH_MP birs_symb_to_concst_PROP_thm bprog_concst_prop_thm)
);
(* ........................... *)

