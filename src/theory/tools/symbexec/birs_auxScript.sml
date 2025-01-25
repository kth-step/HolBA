open HolKernel Parse boolLib bossLib;

open pred_setTheory;

open wordsTheory wordsLib;

open symb_interpretTheory;
open symb_recordTheory;

open bir_symbTheory;
open bir_symb_sound_coreTheory;

open HolBACoreSimps;

val birs_state_ss = rewrites (type_rws ``:birs_state_t``);

val _ = new_theory "birs_aux";

Theorem w2w_32_64:
 !(b1:word32). w2w ((w2w b1):word64) = b1
Proof
  REPEAT Cases_word >>
  FULL_SIMP_TAC (std_ss++wordsLib.SIZES_ss) [w2w_def,n2w_w2n,w2n_n2w,n2w_11] >>
  IMP_RES_TAC (DECIDE ``n < 4294967296 ==> n < 18446744073709551616:num``) >>
  FULL_SIMP_TAC (std_ss++wordsLib.SIZES_ss) []
QED

Theorem n2w_w2n_w2w_32_64:
 !(b1:word32). n2w ((w2n b1)) = (w2w:word32 -> word64) b1
Proof
  REPEAT Cases_word >>
  FULL_SIMP_TAC (std_ss++wordsLib.SIZES_ss) [w2w_def,n2w_w2n,w2n_n2w,n2w_11]
QED

Theorem w2w_n2w_w2n_64_32:
 !(b1:word64). (w2w:word64 -> word32) b1 = n2w ((w2n b1))
Proof
  REPEAT Cases_word >>
  FULL_SIMP_TAC (std_ss++wordsLib.SIZES_ss) [w2w_def,n2w_w2n,w2n_n2w,n2w_11]
QED

(*
Definition bir_lbl_set_gen_def:
  bir_lbl_set_gen l32s lbl = (* (word32,word32)list -> bir_label_t->bool *)
    ...
End
*)

(*
Definition bir_pc_set_lbl_def:
  bir_pc_set_lbl lbl pc = (* bir_label_t -> bir_programcounter_t->bool *)
    (pc.bpc_label = lbl)
End

Theorem bir_pc_set_lbl_thm:
  !pc lbl.
    (pc IN (bir_pc_set_lbl lbl)) = (pc.bpc_label = lbl)
Proof
  fs [bir_pc_set_lbl_def, SPECIFICATION]
QED

Theorem bir_pc_set_lbl_thm:
  !lbl.
    bir_pc_set_lbl lbl =
    {<| bpc_label:=lbl; bpc_index:=i |> | T}
Proof
  fs [EXTENSION, SPECIFICATION, bir_pc_set_lbl_thm] >>
  cheat
QED
*)

(* with this it needs to be easy to do IN, ADD(~INSERT-SUBSET) and UNION *)
(* TODO: later should be defined in terms of ranges, like list of word32 range etc *)
Definition bir_pc_set_lbls_def:
  bir_pc_set_lbls lbls pc = (* (bir_label_t->bool) -> bir_programcounter_t->bool *)
    (pc.bpc_label IN lbls)
End

Theorem bir_pc_set_lbls_IN_thm:
  !pc lbls.
    (pc IN (bir_pc_set_lbls lbls)) = (pc.bpc_label IN lbls)
Proof
  fs [bir_pc_set_lbls_def, SPECIFICATION]
QED

Theorem bir_pc_set_lbls_EMPTY_thm:
  !pc lbls.
    bir_pc_set_lbls EMPTY = EMPTY
Proof
  fs [EXTENSION, SPECIFICATION, bir_pc_set_lbls_def]
QED

(* TODO: create  and insert_CONV (and union_CONV) that only tries to eleminate if an identical one cannot be found/until there is no other one anymore (this might actually be useful also in other places of this codebase)
    --- this means: the assumption of this function is that not identical means not equal *)
Theorem bir_pc_set_lbls_ADD_thm:
  !pc lbls.
    pc INSERT (bir_pc_set_lbls lbls) SUBSET
    bir_pc_set_lbls (pc.bpc_label INSERT lbls)
Proof
  fs [SUBSET_DEF, IN_INSERT, SPECIFICATION, bir_pc_set_lbls_IN_thm]
QED

Theorem bir_pc_set_lbls_UNION_thm:
  !lbls1 lbls2.
    (bir_pc_set_lbls lbls1) UNION (bir_pc_set_lbls lbls2) =
    bir_pc_set_lbls (lbls1 UNION lbls2)
Proof
  fs [UNION_DEF, EXTENSION, GSPECIFICATION, SPECIFICATION, bir_pc_set_lbls_IN_thm]
QED


(* ........................... *)

Theorem birs_symb_symbst_pc_thm:
  !s.
  symb_symbst_pc (birs_symb_to_symbst s) = s.bsst_pc
Proof
REWRITE_TAC [symb_recordTheory.symb_symbst_pc_def, bir_symbTheory.birs_symb_to_symbst_def]
QED

Theorem birs_symb_concst_pc_thm:
  !s.
  symb_concst_pc (birs_symb_to_concst s) = s.bst_pc
Proof
REWRITE_TAC [symb_recordTheory.symb_concst_pc_def, bir_symbTheory.birs_symb_to_concst_def]
QED
(* ........................... *)

Theorem symb_symbols_set_ALT_thm:
  !sr Pi.
  symb_symbols_set sr Pi = (BIGUNION (IMAGE (symb_symbols sr) Pi))
Proof
FULL_SIMP_TAC (std_ss) [symb_symbols_set_def, IMAGE_DEF]
QED

Theorem birs_symb_symbols_set_EQ_thm:
  !prog Pi.
  symb_symbols_set (bir_symb_rec_sbir prog) (IMAGE birs_symb_to_symbst Pi) = BIGUNION (IMAGE birs_symb_symbols Pi)
Proof
FULL_SIMP_TAC (std_ss) [symb_symbols_set_ALT_thm, EXTENSION] >>
  FULL_SIMP_TAC (std_ss) [IN_BIGUNION_IMAGE] >>
  FULL_SIMP_TAC (std_ss) [IN_IMAGE] >>

  REPEAT STRIP_TAC >>
  EQ_TAC >> (
    REPEAT STRIP_TAC >>
    FULL_SIMP_TAC (std_ss) [] >>
    METIS_TAC [bir_symb_sound_coreTheory.birs_symb_symbols_EQ_thm]
  )
QED
(* ........................... *)

Definition birs_exps_of_senv_def:
  birs_exps_of_senv senv =
      {e | (?vn. senv vn = SOME e)}
End

Definition birs_exps_of_senv_COMP_def:
  birs_exps_of_senv_COMP excset senv =
      {e | (?vn. (~(vn IN excset)) /\ senv vn = SOME e)}
End

Theorem birs_exps_of_senv_thm:
  !senv.
  birs_exps_of_senv senv
  =
  birs_exps_of_senv_COMP EMPTY senv
Proof
FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [birs_exps_of_senv_COMP_def, birs_exps_of_senv_def]
QED

Theorem birs_exps_of_senv_COMP_thm:
  !sr Pi.
  (!excset. birs_exps_of_senv_COMP excset (K NONE) = EMPTY) /\
  (!excset senv vn sv. birs_exps_of_senv_COMP excset ((vn =+ (SOME sv)) senv) =
    if vn IN excset then
      birs_exps_of_senv_COMP (vn INSERT excset) senv
    else
      sv INSERT (birs_exps_of_senv_COMP (vn INSERT excset) senv)) /\
  (!excset senv vn. birs_exps_of_senv_COMP excset ((vn =+ NONE) senv) = (birs_exps_of_senv_COMP (vn INSERT excset) senv))
Proof
REPEAT STRIP_TAC >> (
    FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [birs_exps_of_senv_COMP_def]
  ) >>

  Cases_on `vn IN excset` >> (
    FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [EXTENSION] >>
    REPEAT STRIP_TAC >> EQ_TAC >> (
      REPEAT STRIP_TAC >>
      METIS_TAC [combinTheory.APPLY_UPDATE_THM, optionTheory.option_CLAUSES]
    )
  )
QED
(* ........................... *)

Theorem birs_symb_symbols_thm:
  !sys.
  birs_symb_symbols sys = (BIGUNION (IMAGE bir_vars_of_exp (birs_exps_of_senv sys.bsst_environ))) UNION (bir_vars_of_exp sys.bsst_pcond)
Proof
FULL_SIMP_TAC (std_ss) [birs_symb_symbols_def, IMAGE_DEF, birs_exps_of_senv_def, IN_GSPEC_IFF]
QED
(* ........................... *)



Definition BVarToPair_def:
  BVarToPair (BVar bvn bty) = (bvn, bty)
End
Definition PairToBVar_def:
  PairToBVar (bvn, bty) = (BVar bvn bty)
End

Theorem PairToBVar_BVarToPair_I_thm:
  PairToBVar ∘ BVarToPair = I
Proof
  SIMP_TAC std_ss [boolTheory.FUN_EQ_THM] >>
  REPEAT STRIP_TAC >>
  Cases_on `x` >>
  SIMP_TAC std_ss [PairToBVar_def, BVarToPair_def]
QED

Definition bir_senv_GEN_bvar_def:
  bir_senv_GEN_bvar (vn,ty) = BVar (CONCAT["sy_";vn]) ty
End
Theorem bir_senv_GEN_bvar_EQ_thm:
  !x y.
  bir_senv_GEN_bvar x = bir_senv_GEN_bvar y <=> x = y
Proof
Cases_on `x` >> Cases_on `y` >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_senv_GEN_bvar_def] >>

  ASSUME_TAC (INST_TYPE [Type.alpha |-> Type`:char`] (prove(
    ``!A B C. FLAT [A;B] = FLAT [A;C] <=> B = C``,
      SIMP_TAC (std_ss++listSimps.LIST_ss) [listTheory.FLAT_compute, listTheory.FLAT]
  ))) >>

  METIS_TAC []
QED
(* ........................... *)


Theorem MEM_FST_IMP_MEM_thm:
  !vn l.
  (MEM vn (MAP FST l)) ==>
  (?ty. MEM (vn,ty) l)
Proof
REPEAT STRIP_TAC >>
  CCONTR_TAC >>
  FULL_SIMP_TAC (std_ss++listSimps.LIST_ss) [listTheory.MEM_MAP] >>
  Cases_on `y` >>
  FULL_SIMP_TAC (std_ss++listSimps.LIST_ss) [] >>
  METIS_TAC []
QED
Theorem NOT_MEM_FST_IMP_thm:
  !vn l.
  (~(MEM vn (MAP FST l))) ==>
  (!e. ~(MEM e l) \/ ~((\(vni,ty). vni = vn) e))
Proof
REPEAT STRIP_TAC >>
  Cases_on `e` >>
  Cases_on `q = vn` >- (
    METIS_TAC [listTheory.MEM_MAP_f, pairTheory.FST]
  ) >>
  FULL_SIMP_TAC std_ss []
QED
(* ........................... *)


Definition bir_senv_GEN_list_def:
  bir_senv_GEN_list l = FOLDR (\(vn,ty). \f. (vn =+ SOME (BExp_Den (bir_senv_GEN_bvar (vn,ty)))) f) (K NONE) l
End
(*
("R7"         =+ (SOME (BExp_Den (BVar "sy_R7" (BType_Imm Bit32)))))
                   (("SP_process" =+ (SOME (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)))))
                      (("countw"     =+ (SOME (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))))
                       (K NONE)
                   ))
*)
Theorem bir_senv_GEN_list_NOT_MEM_thm:
  !vn l.
  (~(MEM vn (MAP FST l))) ==>
  (bir_senv_GEN_list l vn = NONE)
Proof
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
QED
Theorem bir_senv_GEN_list_APPLY_thm:
  !vn ty l.
  (MEM (vn,ty) l) ==>
  (ALL_DISTINCT (MAP FST l)) ==>
  (bir_senv_GEN_list l vn = SOME (BExp_Den (bir_senv_GEN_bvar (vn,ty))))
Proof
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
QED

Theorem bir_senv_GEN_list_vars_thm:
  !l.
  (ALL_DISTINCT (MAP FST l)) ==>
  (BIGUNION {bir_vars_of_exp e | (?vn. (bir_senv_GEN_list l) vn = SOME e)} = set (MAP bir_senv_GEN_bvar l))
Proof
Induct_on `l` >- (
    SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [listTheory.MAP, bir_senv_GEN_list_def, listTheory.FOLDR, EXTENSION, listTheory.MEM]
  ) >>

  REPEAT STRIP_TAC >>

  SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [bir_senv_GEN_list_def, listTheory.MAP, listTheory.FOLDR] >>

  SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [EXTENSION, listTheory.LIST_TO_SET_DEF, listTheory.MEM] >>

  REPEAT STRIP_TAC >>
  Cases_on `h` >>
  FULL_SIMP_TAC std_ss [GSYM bir_senv_GEN_list_def, listTheory.ALL_DISTINCT, listTheory.MAP] >>

  EQ_TAC >- (
    FULL_SIMP_TAC std_ss [GSYM EXTENSION] >>
    REPEAT STRIP_TAC >>
    Cases_on `q = vn` >- (
      FULL_SIMP_TAC std_ss [combinTheory.APPLY_UPDATE_THM] >>
      METIS_TAC [bir_typing_expTheory.bir_vars_of_exp_def, IN_SING]
    ) >>

    FULL_SIMP_TAC std_ss [combinTheory.APPLY_UPDATE_THM] >>
    `x IN (BIGUNION {bir_vars_of_exp e | (?vn. bir_senv_GEN_list l vn = SOME e)})` by (
      SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>
      METIS_TAC []
    ) >>

    FULL_SIMP_TAC std_ss [EXTENSION] >>
    METIS_TAC []
  ) >>

  FULL_SIMP_TAC std_ss [GSYM EXTENSION] >>
  REPEAT STRIP_TAC >- (
    Q.EXISTS_TAC `bir_vars_of_exp (BExp_Den (x))` >>
    FULL_SIMP_TAC std_ss [bir_typing_expTheory.bir_vars_of_exp_def, IN_SING] >>
    Q.EXISTS_TAC `BExp_Den (x)` >>
    FULL_SIMP_TAC std_ss [bir_typing_expTheory.bir_vars_of_exp_def, IN_SING] >>
    FULL_SIMP_TAC std_ss [] >>
    Q.EXISTS_TAC `q` >>
    FULL_SIMP_TAC std_ss [combinTheory.APPLY_UPDATE_THM]
  ) >>

  FULL_SIMP_TAC std_ss [EXTENSION] >>
  PAT_X_ASSUM ``!x.A`` (ASSUME_TAC o Q.SPEC `x`) >>
  REV_FULL_SIMP_TAC std_ss [GSYM EXTENSION] >>

  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>
  `q <> vn` by (
    METIS_TAC [bir_senv_GEN_list_NOT_MEM_thm, optionTheory.option_CLAUSES]
  ) >>

  METIS_TAC [combinTheory.APPLY_UPDATE_THM]
QED
(* ........................... *)


Definition bir_interpr_GEN_list_def:
  bir_interpr_GEN_list l envf = FOLDR (\(vn,ty). \f. ((bir_senv_GEN_bvar (vn,ty)) =+ envf vn) f) (K NONE) l
End
(*
  Q.EXISTS_TAC `SymbInterpret
    ((BVar "sy_R7" (BType_Imm Bit32) =+ SOME v_R7)
    ((BVar "sy_SP_process" (BType_Imm Bit32) =+ SOME v_SP_process)
    ((BVar "sy_countw" (BType_Imm Bit64) =+ SOME v_countw) (K NONE))))` >>
*)
Theorem bir_interpr_GEN_list_NOT_MEM_thm:
  !vn ty l f.
  (~(MEM vn (MAP FST l))) ==>
  (bir_interpr_GEN_list l f (bir_senv_GEN_bvar (vn,ty)) = NONE)
Proof
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
QED
Theorem bir_interpr_GEN_list_APPLY_thm:
  !vn ty l f.
  (MEM (vn,ty) l) ==>
  (ALL_DISTINCT (MAP FST l)) ==>
  (bir_interpr_GEN_list l f (bir_senv_GEN_bvar (vn,ty)) = f vn)
Proof
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
QED
Theorem bir_interpr_GEN_list_APPLY2_thm:
  !vn l f.
  (MEM vn (MAP FST l)) ==>
  (?ty. bir_interpr_GEN_list l f (bir_senv_GEN_bvar (vn,ty)) = f vn)
Proof
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
QED

Theorem bir_interpr_GEN_list_IS_SOME_IMP_EXISTS_thm:
  !l f bv.
  (IS_SOME (bir_interpr_GEN_list l f bv)) ==>
  (?vn ty. bv = bir_senv_GEN_bvar (vn, ty) /\ (MEM (vn,ty) l))
Proof
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
QED
(* ........................... *)


Definition bir_envty_list_inclusive_def:
  bir_envty_list_inclusive l env = EVERY (\(vn,ty). ?v. env vn = SOME v /\ type_of_bir_val v = ty) l
End

Theorem bir_envty_list_inclusive_thm:
  !l env.
    bir_envty_list_inclusive l env = EVERY (bir_env_var_is_initialised (BEnv env) o PairToBVar) l
Proof
  SIMP_TAC std_ss [bir_env_oldTheory.bir_env_var_is_initialised_def, bir_envty_list_inclusive_def, combinTheory.o_DEF, bir_envTheory.bir_env_lookup_def] >>

  SIMP_TAC std_ss [boolTheory.EQ_IMP_THM] >>
  REPEAT STRIP_TAC >> (
    FULL_SIMP_TAC std_ss [listTheory.EVERY_MEM] >>
    REPEAT STRIP_TAC >>
    PAT_X_ASSUM ``!x.A`` IMP_RES_TAC >>
    TRY (Cases_on `x`) >> TRY (Cases_on `e`) >>
    FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_envTheory.bir_var_name_def, PairToBVar_def]
  )
QED

Theorem bir_envty_list_inclusive_thm2:
  !l env.
    bir_envty_list_inclusive l env = EVERY (bir_env_var_is_initialised (BEnv env)) (MAP PairToBVar l)
Proof
  SIMP_TAC std_ss [bir_envty_list_inclusive_thm, combinTheory.o_DEF] >>
  FULL_SIMP_TAC (std_ss++holBACore_ss++listSimps.LIST_ss) [listTheory.EVERY_MEM, listTheory.MEM_MAP] >>

  SIMP_TAC std_ss [boolTheory.EQ_IMP_THM] >>
  REPEAT STRIP_TAC >- (
    FULL_SIMP_TAC std_ss [] >>
    REPEAT STRIP_TAC
  ) >>

  METIS_TAC []
QED

Theorem bir_env_vars_are_initialised_IMP_envty_list_inclusive_thm:
  !l f.
    (bir_env_vars_are_initialised (BEnv f) (set l)) ==>
    (bir_envty_list_inclusive (MAP BVarToPair l) f)
Proof
  SIMP_TAC std_ss [bir_envty_list_inclusive_thm2] >>
  FULL_SIMP_TAC std_ss [listTheory.EVERY_MEM] >>
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [listTheory.MAP_MAP_o] >>
  `MAP (PairToBVar ∘ BVarToPair) l = l` by (
    METIS_TAC [listTheory.MAP_ID, PairToBVar_BVarToPair_I_thm]
  ) >>
  FULL_SIMP_TAC std_ss [] >>

  FULL_SIMP_TAC std_ss [bir_env_oldTheory.bir_env_vars_are_initialised_def]
QED

Theorem bir_env_vars_are_initialised_IMP_envty_list_inclusive_thm2:
  !l f.
    (bir_env_vars_are_initialised (BEnv f) (set (MAP PairToBVar l))) ==>
    (bir_envty_list_inclusive l f)
Proof
  SIMP_TAC std_ss [bir_envty_list_inclusive_thm2] >>
  FULL_SIMP_TAC std_ss [listTheory.EVERY_MEM] >>
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [bir_env_oldTheory.bir_env_vars_are_initialised_def]
QED

Definition bir_envty_list_exclusive_def:
  bir_envty_list_exclusive l env = (!vn. (~(EXISTS (\(vni,ty). vni = vn) l)) ==> (env vn = NONE))
End
Definition bir_envty_list_def:
  bir_envty_list l env = (ALL_DISTINCT (MAP FST l) /\ bir_envty_list_inclusive l env /\ bir_envty_list_exclusive l env)
End
Theorem bir_envty_list_MEM_IMP_thm:
  !vn ty l f.
  (MEM (vn,ty) l) ==>
  (bir_envty_list l f) ==>
  (?v. f vn = SOME v /\ type_of_bir_val v = ty)
Proof
REWRITE_TAC [bir_envty_list_def, bir_envty_list_inclusive_def, listTheory.EVERY_MEM] >>
  REPEAT STRIP_TAC >>
  PAT_X_ASSUM ``!x.A`` (ASSUME_TAC o Q.SPEC `(vn,ty)`) >>
  FULL_SIMP_TAC std_ss []
QED
Theorem bir_envty_list_NOT_MEM_IMP_thm:
  !vn l f.
  (~(MEM vn (MAP FST l))) ==>
  (bir_envty_list l f) ==>
  (f vn = NONE)
Proof
REWRITE_TAC [bir_envty_list_def, bir_envty_list_exclusive_def, listTheory.EXISTS_MEM] >>
  REPEAT STRIP_TAC >>
  PAT_X_ASSUM ``!x.A`` (ASSUME_TAC o Q.SPEC `vn`) >>
  FULL_SIMP_TAC std_ss [boolTheory.NOT_EXISTS_THM, NOT_MEM_FST_IMP_thm]
QED

Definition bir_envty_list_b_def:
  bir_envty_list_b l (BEnv env) = bir_envty_list l env
End
Theorem bir_envty_list_b_thm:
  !l env.
  bir_envty_list_b l env = bir_envty_list l (\bvn. bir_env_lookup bvn env)
Proof
REPEAT STRIP_TAC >>
  Cases_on `env` >>
  FULL_SIMP_TAC (std_ss) [bir_envty_list_b_def, bir_envTheory.bir_env_lookup_def] >>
  METIS_TAC []
QED

Theorem bir_state_restrict_vars_envty_list_b_thm:
  !l vs st st'.
    (ALL_DISTINCT (MAP FST l)) ==>
    (set (MAP PairToBVar l) = vs) ==>
    (st' = bir_state_restrict_vars vs st) ==>
    (bir_env_vars_are_initialised st.bst_environ vs) ==>
    (bir_envty_list_b l st'.bst_environ)
Proof
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [bir_envty_list_b_thm, bir_programTheory.bir_state_restrict_vars_ALT_THM] >>

  `bir_envty_list_inclusive l (\bvn. bir_env_lookup bvn (bir_env_restrict_vars vs st.bst_environ))` by (
    `bir_env_vars_are_initialised (BEnv (\bvn. bir_env_lookup bvn (bir_env_restrict_vars vs st.bst_environ))) vs` by (
      IMP_RES_TAC bir_env_oldTheory.bir_env_restrict_vars_IMP_vars_are_initialised_THM >>
      Cases_on `bir_env_restrict_vars vs st.bst_environ` >>
      Cases_on `st.bst_environ` >>
      SIMP_TAC std_ss [bir_env_oldTheory.bir_env_restrict_vars_def, bir_envTheory.bir_env_lookup_def] >>
      METIS_TAC []
    ) >>
    METIS_TAC [bir_env_vars_are_initialised_IMP_envty_list_inclusive_thm2]
  ) >>

  (* variable list has dinstinct variable names *)
  FULL_SIMP_TAC (std_ss) [bir_envty_list_def] >>

  (* exclusive part, due to restriction *)
  SIMP_TAC std_ss [bir_envty_list_exclusive_def] >>

  `!bvn l. EXISTS (\(vni:string,ty:bir_type_t). vni = bvn) l = MEM bvn (MAP FST l)` by (
    REPEAT (POP_ASSUM (K ALL_TAC)) >>
    SIMP_TAC std_ss [listTheory.MEM_MAP, listTheory.EXISTS_MEM] >>

    `!e bvn. (FST e = bvn)  = (\(vni:string,ty:bir_type_t). vni = bvn) e` by (
      Cases_on `e` >>
      SIMP_TAC std_ss [pairTheory.FST]
    ) >>
    METIS_TAC []
  ) >>
  FULL_SIMP_TAC std_ss [] >>
  REPEAT STRIP_TAC >>

  `bvn NOTIN (IMAGE bir_var_name vs)` by (
    PAT_X_ASSUM ``set A = B`` (ASSUME_TAC o GSYM) >>
    FULL_SIMP_TAC std_ss [listTheory.LIST_TO_SET_MAP, pred_setTheory.IMAGE_IMAGE] >>
    `bir_var_name ∘ PairToBVar = FST` by (
      REPEAT (POP_ASSUM (K ALL_TAC)) >>
      FULL_SIMP_TAC std_ss [boolTheory.FUN_EQ_THM] >>
      Cases_on `x` >>
      FULL_SIMP_TAC (std_ss) [PairToBVar_def, bir_envTheory.bir_var_name_def]
    ) >>
    FULL_SIMP_TAC std_ss [GSYM listTheory.LIST_TO_SET_MAP]
  ) >>

  METIS_TAC [bir_env_oldTheory.bir_env_restrict_vars_NOTIN_IMAGE_THM]
QED
(* ........................... *)


Theorem birs_matchenv_bir_senv_GEN_thm:
  !l f.
  (bir_envty_list l f) ==>
  (birs_matchenv (SymbInterpret (bir_interpr_GEN_list l f))
          (bir_senv_GEN_list l) (BEnv f))
Proof
SIMP_TAC std_ss [birs_matchenv_def] >>
  REPEAT STRIP_TAC >>
  `ALL_DISTINCT (MAP FST l)` by FULL_SIMP_TAC std_ss [bir_envty_list_def] >>
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
QED


Theorem symb_interpr_dom_bir_interpr_GEN_list_thm:
  !l f.
  (bir_envty_list l f) ==>
  (symb_interpr_dom (SymbInterpret (bir_interpr_GEN_list l f))
   =
   set (MAP bir_senv_GEN_bvar l))
Proof
SIMP_TAC std_ss [symb_interpr_dom_def] >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [EXTENSION] >>
  FULL_SIMP_TAC (std_ss) [listTheory.MEM_MAP] >>

  REPEAT STRIP_TAC >>
  `ALL_DISTINCT (MAP FST l)` by FULL_SIMP_TAC std_ss [bir_envty_list_def] >>
  EQ_TAC >- (
    REPEAT STRIP_TAC >>

    FULL_SIMP_TAC (pure_ss) [GSYM optionTheory.NOT_IS_SOME_EQ_NONE] >>
    FULL_SIMP_TAC (std_ss) [] >>

    METIS_TAC [bir_interpr_GEN_list_IS_SOME_IMP_EXISTS_thm]
  ) >>

  REPEAT STRIP_TAC >>
  Cases_on `y` >>

  REV_FULL_SIMP_TAC (std_ss) [bir_interpr_GEN_list_APPLY_thm] >>


  IMP_RES_TAC bir_envty_list_MEM_IMP_thm >>
  FULL_SIMP_TAC (std_ss) []
QED

Theorem birs_interpr_welltyped_bir_interpr_GEN_list_thm:
  !l f.
  (bir_envty_list l f) ==>
  (birs_interpr_welltyped (SymbInterpret (bir_interpr_GEN_list l f)))
Proof
SIMP_TAC std_ss [birs_interpr_welltyped_def, symb_interpr_dom_bir_interpr_GEN_list_thm, symb_interpr_get_def] >>
  FULL_SIMP_TAC (std_ss) [listTheory.MEM_MAP] >>
  REPEAT STRIP_TAC >>
  `ALL_DISTINCT (MAP FST l)` by FULL_SIMP_TAC std_ss [bir_envty_list_def] >>

  Cases_on `y` >>
  FULL_SIMP_TAC (std_ss) [bir_interpr_GEN_list_APPLY_thm] >>

  IMP_RES_TAC bir_envty_list_MEM_IMP_thm >>
  FULL_SIMP_TAC (std_ss) [bir_envTheory.bir_var_type_def, bir_senv_GEN_bvar_def]
QED

Theorem symb_interpr_for_symbs_bir_interpr_GEN_list_thm:
  !l f lbl status bpre_sv.
  (bir_envty_list l f) ==>
  (bir_vars_of_exp bpre_sv SUBSET (set (MAP bir_senv_GEN_bvar l))) ==>
  (symb_interpr_for_symbs
          (birs_symb_symbols
             <|bsst_pc := lbl; bsst_environ := bir_senv_GEN_list l;
               bsst_status := status; bsst_pcond := bpre_sv|>)
          (SymbInterpret (bir_interpr_GEN_list l f)))
Proof
FULL_SIMP_TAC std_ss [symb_interpr_for_symbs_def, symb_interpr_dom_bir_interpr_GEN_list_thm] >>
  FULL_SIMP_TAC (std_ss++birs_state_ss++holBACore_ss) [birs_symb_symbols_def, UNION_EMPTY] >>

  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [pred_setTheory.SUBSET_DEF] >>

  REPEAT STRIP_TAC >>
  `ALL_DISTINCT (MAP FST l)` by FULL_SIMP_TAC std_ss [bir_envty_list_def] >>
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
QED

Theorem bir_envty_list_IMP_birs_eval_exp_vars_thm:
  !l bpre bpre_sv ty.
  (ALL_DISTINCT (MAP FST l)) ==>
  (birs_eval_exp bpre (bir_senv_GEN_list l) = SOME (bpre_sv,ty)) ==>
  (bir_vars_of_exp bpre_sv SUBSET set (MAP bir_senv_GEN_bvar l))
Proof
METIS_TAC [bir_symb_soundTheory.birs_eval_exp_IMP_varset_thm, bir_senv_GEN_list_vars_thm]
QED

Theorem bir_envty_list_IMP_birs_eval_exp_interpret_thm:
  !l f e v sv ty.
  (bir_envty_list l f) ==>
  (bir_eval_exp e (BEnv f) = SOME v (*bir_val_true*)) ==>
  (birs_eval_exp e (bir_senv_GEN_list l) = SOME (sv,ty)) ==>
  (birs_interpret_fun (SymbInterpret (bir_interpr_GEN_list l f)) sv = SOME v (*bir_val_true*))
Proof
REPEAT STRIP_TAC >>
  Q.ABBREV_TAC `env = BEnv f` >>
  Q.ABBREV_TAC `senv = bir_senv_GEN_list l` >>
  Q.ABBREV_TAC `H = SymbInterpret (bir_interpr_GEN_list l f)` >>

  `birs_interpr_welltyped H` by (
    METIS_TAC [birs_interpr_welltyped_bir_interpr_GEN_list_thm]
  ) >>
  `birs_matchenv H senv env` by (
    METIS_TAC [birs_matchenv_bir_senv_GEN_thm]
  ) >>

  IMP_RES_TAC bir_symb_sound_coreTheory.birs_eval_exp_sound_thm >>
  POP_ASSUM (ASSUME_TAC o Q.SPEC `e`) >>
  FULL_SIMP_TAC std_ss [] >>
  FULL_SIMP_TAC std_ss [] >>

  METIS_TAC [optionTheory.option_CLAUSES]
QED
(* ........................... *)


Theorem bprog_P_entails_gen_thm:
  !lbl status l f bpre bpre_sv ty.
  (bir_envty_list l f) ==>
  (bir_eval_exp bpre (BEnv f) = SOME bir_val_true) ==>
  (birs_eval_exp bpre (bir_senv_GEN_list l) = SOME (bpre_sv,ty)) ==>
  (?H. birs_symb_matchstate
              <|bsst_pc := lbl;
                bsst_environ := bir_senv_GEN_list l;
                bsst_status := status;
                bsst_pcond := bpre_sv |>
              H
              (bir_state_t
                 lbl
                 (BEnv f)
                 status)
  )
Proof
REPEAT STRIP_TAC >>
  Q.EXISTS_TAC `SymbInterpret (bir_interpr_GEN_list l f)` >>

  `bir_vars_of_exp bpre_sv SUBSET set (MAP bir_senv_GEN_bvar l)` by (
    METIS_TAC [bir_envty_list_IMP_birs_eval_exp_vars_thm, bir_envty_list_def]
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
  ) >>

  METIS_TAC [bir_envty_list_IMP_birs_eval_exp_interpret_thm]
QED
(* ........................... *)


Theorem bir_BEnv_lookup_EQ_thm:
  !env.
  BEnv (λbvn. bir_env_lookup bvn env) = env
Proof
REPEAT STRIP_TAC >>
  Cases_on `env` >>
  FULL_SIMP_TAC (std_ss) [bir_envty_list_b_def, bir_envTheory.bir_env_lookup_def] >>
  METIS_TAC []
QED




Definition birs_gen_env_fun_def:
  birs_gen_env_fun (n, sv) env = (n =+ (SOME sv)) env
End
Definition birs_gen_env_def:
  birs_gen_env l = FOLDR birs_gen_env_fun (K NONE) l
End

Definition birs_env_var_is_initialised_def:
  birs_env_var_is_initialised senv symbs var <=>
  (?se. (senv (bir_var_name var) = SOME se) /\
       (type_of_bir_exp se = SOME (bir_var_type var)) /\
       (bir_vars_of_exp se SUBSET symbs))
End
Definition birs_env_vars_are_initialised_def:
  birs_env_vars_are_initialised senv symbs vs <=>
  (!v. v IN vs ==> birs_env_var_is_initialised senv symbs v)
End

Theorem birs_env_vars_are_initialised_EMPTY_thm:
  !senv symbs.
    (birs_env_vars_are_initialised senv symbs EMPTY)
Proof
  METIS_TAC [birs_env_vars_are_initialised_def, pred_setTheory.NOT_IN_EMPTY]
QED

Theorem birs_env_vars_are_initialised_INSERT_thm:
  !v vs senv symbs.
   birs_env_vars_are_initialised senv symbs (v INSERT vs) <=>
     birs_env_var_is_initialised senv symbs v /\
     birs_env_vars_are_initialised senv symbs vs
Proof
  REWRITE_TAC [birs_env_vars_are_initialised_def] >>
  SIMP_TAC std_ss [boolTheory.EQ_IMP_THM] >>
  REPEAT STRIP_TAC >> (
    METIS_TAC [pred_setTheory.IN_INSERT, pred_setTheory.COMPONENT]
  )
QED

Theorem birs_gen_env_NULL_thm:
  !n sv l.
    birs_gen_env ([]) = (K NONE)
Proof
SIMP_TAC std_ss [birs_gen_env_def, listTheory.FOLDR]
QED
Theorem birs_gen_env_thm:
  !n sv l.
    birs_gen_env ((n, sv)::l) = (n =+ (SOME sv)) (birs_gen_env l)
Proof
SIMP_TAC std_ss [birs_gen_env_def, listTheory.FOLDR, birs_gen_env_fun_def]
QED

(*
EVAL ``birs_gen_env [("R0",BExp_Den (BVar "sy_R0" (BType_Imm Bit32))); ("R1",BExp_Den (BVar "sy_R1" (BType_Imm Bit32)))]``
(REWRITE_CONV [birs_gen_env_thm, birs_gen_env_NULL_thm]) ``birs_gen_env [("R0",BExp_Den (BVar "sy_R0" (BType_Imm Bit32))); ("R1",BExp_Den (BVar "sy_R1" (BType_Imm Bit32)))]``
*)

Theorem birs_update_env_thm:
  !n sv l.
    birs_update_env (n, sv) (birs_gen_env l) = birs_gen_env((n, sv)::(FILTER (\x. (FST x) <> n) l))
Proof
SIMP_TAC std_ss [birs_update_env_def, birs_gen_env_thm] >>
  REWRITE_TAC [boolTheory.FUN_EQ_THM] >>

  REPEAT STRIP_TAC >>
  Cases_on `x = n` >> (
    ASM_SIMP_TAC std_ss [combinTheory.UPDATE_APPLY]
  ) >>

  Induct_on `l` >> (
    SIMP_TAC std_ss [listTheory.FILTER]
  ) >>

  REPEAT STRIP_TAC >>
  Cases_on `h` >>
  Cases_on `q = n` >> (
    ASM_SIMP_TAC std_ss [birs_gen_env_thm, combinTheory.UPDATE_APPLY]
  ) >>

  Cases_on `x = q` >> (
    ASM_SIMP_TAC std_ss [combinTheory.UPDATE_APPLY]
  )
QED

(*
(REWRITE_CONV [birs_update_env_thm] THENC RESTR_EVAL_CONV [``birs_gen_env``])
  ``birs_update_env ("R0", BExp_Const (Imm32 0w)) (birs_gen_env [("R2",BExp_Den (BVar "sy_R0" (BType_Imm Bit32))); ("R1",BExp_Den (BVar "sy_R1" (BType_Imm Bit32)))])``
*)

Theorem birs_gen_env_GET_NULL_thm:
  !m.
    birs_gen_env [] m = NONE
Proof
SIMP_TAC std_ss [birs_gen_env_NULL_thm]
QED
Theorem birs_gen_env_GET_thm:
  !n sv l m.
    birs_gen_env ((n, sv)::l) m = if n = m then SOME sv else birs_gen_env l m
Proof
SIMP_TAC std_ss [birs_gen_env_thm, combinTheory.APPLY_UPDATE_THM]
QED

(*
(REWRITE_CONV [birs_gen_env_GET_thm, birs_gen_env_GET_NULL_thm] THENC EVAL) ``birs_gen_env [("R0",BExp_Den (BVar "sy_R0" (BType_Imm Bit32))); ("R1",BExp_Den (BVar "sy_R1" (BType_Imm Bit32)))] "R0"``
*)

Theorem birs_symb_env_subst1_gen_env_thm:
  !v e l.
    birs_symb_env_subst1 v e (birs_gen_env l) =
      birs_gen_env (MAP (\x. (FST x, bir_exp_subst1 v e (SND x))) l)
Proof
  rewrite_tac [bir_symb_soundTheory.birs_symb_env_subst1_def] >>
  Induct_on ‘l’ >- (
    fs [birs_gen_env_NULL_thm]
  ) >>
  Cases_on ‘h’ >>
  rpt strip_tac >>
  fs [birs_gen_env_thm] >>
  CONV_TAC FUN_EQ_CONV >>
  rpt strip_tac >>
  fs [combinTheory.o_THM] >>
  Cases_on ‘x = q’ >> (
    fs [combinTheory.UPDATE_APPLY]
  ) >>
  metis_tac [GSYM combinTheory.o_THM]
QED


Definition BExp_IntervalPred_def:
  BExp_IntervalPred e (e_l, e_h) =
    BExp_BinExp BIExp_And
      (BExp_BinPred BIExp_LessOrEqual e_l e)
      (BExp_BinPred BIExp_LessOrEqual e e_h)
End

Theorem bir_vars_of_exp_BExp_IntervalPred_thm:
  !e e_l e_h.
    bir_vars_of_exp (BExp_IntervalPred e (e_l, e_h)) =
      (bir_vars_of_exp e UNION
       bir_vars_of_exp e_l UNION
       bir_vars_of_exp e_h)
Proof
  fs [BExp_IntervalPred_def, bir_typing_expTheory.bir_vars_of_exp_def] >>
  metis_tac [UNION_COMM, UNION_ASSOC, UNION_IDEMPOT]
QED

Theorem bir_eval_exp_BExp_IntervalPred_thm:
  !e e_l e_h env.
    bir_eval_exp (BExp_IntervalPred e (e_l, e_h)) env = (
      bir_eval_bin_exp BIExp_And
        (bir_eval_bin_pred BIExp_LessOrEqual
          (bir_eval_exp e_l env)
          (bir_eval_exp e env))
        (bir_eval_bin_pred BIExp_LessOrEqual
          (bir_eval_exp e env)
          (bir_eval_exp e_h env)))
Proof
  fs [BExp_IntervalPred_def, bir_expTheory.bir_eval_exp_def]
QED

Theorem type_of_bir_exp_BExp_IntervalPred_thm:
  !e e_l e_h.
    type_of_bir_exp (BExp_IntervalPred e (e_l, e_h)) =
      (case (type_of_bir_exp e, type_of_bir_exp e_l, type_of_bir_exp e_h) of
        (SOME (BType_Imm ty), SOME (BType_Imm lty), SOME (BType_Imm hty)) =>
          (if ((ty = lty) /\ (ty = hty)) then SOME (BType_Imm Bit1) else NONE)
        | _, _ => NONE)
Proof
  fs [BExp_IntervalPred_def, bir_typing_expTheory.type_of_bir_exp_def] >>
  Cases_on ‘type_of_bir_exp e’ >> Cases_on ‘type_of_bir_exp e_l’ >> Cases_on ‘type_of_bir_exp e_h’ >> (
    EVAL_TAC
  ) >- (
    CASE_TAC
  ) >- (
    CASE_TAC
  ) >- (
    Cases_on ‘x’ >> Cases_on ‘x'’ >> EVAL_TAC >> CASE_TAC
  ) >>

  Cases_on ‘x’ >> Cases_on ‘x'’ >> Cases_on ‘x''’ >> FULL_SIMP_TAC std_ss [bir_valuesTheory.bir_type_t_11] >> EVAL_TAC >> CASE_TAC >> (
    FULL_SIMP_TAC std_ss []) >>
  CASE_TAC >> FULL_SIMP_TAC std_ss []
QED



val _ = export_theory();
