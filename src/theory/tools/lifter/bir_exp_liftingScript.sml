open HolKernel Parse boolLib bossLib;
open bir_expTheory HolBACoreSimps;
open bir_typing_expTheory bir_valuesTheory
open bir_envTheory bir_immTheory bir_exp_immTheory
open bir_immSyntax wordsTheory
open bir_exp_memTheory bir_bool_expTheory
open bir_nzcv_expTheory bir_interval_expTheory
open bir_lifter_general_auxTheory
open bir_extra_expsTheory
open finite_mapTheory;
open pred_setTheory;
open bir_auxiliaryLib;

val _ = new_theory "bir_exp_lifting";

(***********************************)
(* memory map conversion functions *)
(***********************************)


val bir_mmap_w_w2n_def = Define `
   (bir_mmap_w_w2n (mmap_w: 'a word |-> 'b word)): num |-> num =
      FUN_FMAP (\x. w2n (FAPPLY mmap_w (n2w x)))
               (IMAGE w2n (FDOM mmap_w))
    `;

val bir_mmap_n2w_def = Define `
   (bir_mmap_n2w (mmap: num |-> num)) : 'a word |-> 'b word =
      FUN_FMAP (\x. n2w (FAPPLY mmap (w2n x)))
               (IMAGE n2w ((FDOM mmap) INTER {n | n < dimword (:'a)}))
    `;

val bir_load_mmap_w_def = Define `
    bir_load_mmap_w (mmap_w: 'a word |-> 'b word) a =
      n2w (bir_load_mmap (bir_mmap_w_w2n mmap_w) (w2n (a : 'a word))) : 'b word
    `;

val bir_load_mmap_w_alt_thm = store_thm("bir_load_mmap_w_alt_thm", ``
  !mmap_w a. bir_load_mmap_w (mmap_w: 'a word |-> 'b word) a =
	       case FLOOKUP mmap_w a of
		 | NONE => 0w
		 | SOME v => v
``,
  REPEAT STRIP_TAC >>
  REWRITE_TAC [bir_load_mmap_w_def] >>

  REWRITE_TAC [bir_load_mmap_def, bir_mmap_w_w2n_def] >>

  Cases_on `FLOOKUP mmap_w a` >- (
    `~((w2n a) IN (IMAGE w2n (FDOM mmap_w)))` by (
      FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [FLOOKUP_DEF] >>
      METIS_TAC [w2n_11]
    ) >>
    ASM_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [FLOOKUP_FUN_FMAP, FDOM_FINITE, IMAGE_FINITE]
  ) >>

  `((w2n a) IN (IMAGE w2n (FDOM mmap_w)))` by (
    FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [FLOOKUP_DEF] >>
    METIS_TAC[]
  ) >>
  `a IN (FDOM mmap_w)` by (
    FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [w2n_11]
  ) >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [FLOOKUP_FUN_FMAP, FDOM_FINITE, IMAGE_FINITE, n2w_w2n, FLOOKUP_DEF] >>
`(?x.w2n x' = w2n x /\ x IN FDOM mmap_w) = T` by (REWRITE_TAC[EQ_CLAUSES] >> METIS_TAC[]) >>
ASM_REWRITE_TAC[] >>
  EVAL_TAC
);


val bir_mf2mm_def = Define `
   (bir_mf2mm (mf: 'a word -> 'b word)) : 'a word |-> 'b word =
      FUN_FMAP mf (UNIV:'a word -> bool)(*{ x | mf x <> 0w }*)
    `;



val bir_FLOOKUP_mmap_w2n__thm = store_thm("bir_FLOOKUP_mmap_w2n__thm", ``
  !mmap_w a. FLOOKUP (bir_mmap_w_w2n mmap_w) (a MOD dimword (:'a)) =
               OPTION_MAP w2n (FLOOKUP mmap_w (n2w a : 'a word))
``,
  REPEAT STRIP_TAC >>
  REWRITE_TAC [FLOOKUP_DEF] >>

  `FDOM (bir_mmap_w_w2n mmap_w) = IMAGE w2n (FDOM mmap_w)` by (
    SIMP_TAC std_ss [bir_mmap_w_w2n_def, FDOM_FINITE, IMAGE_FINITE, FDOM_FMAP]
  ) >>
  ASM_REWRITE_TAC [] >>
  POP_ASSUM (K ALL_TAC) >>

  SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>
  Cases_on `?x. (a MOD dimword (:'a) = w2n x) /\ x IN FDOM mmap_w` >- (
    ASM_REWRITE_TAC [] >>
    FULL_SIMP_TAC std_ss [n2w_w2n] >>

    `(a MOD dimword (:'a)) IN (IMAGE w2n (FDOM mmap_w))` by (
      FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>
      METIS_TAC []
    ) >>

    REV_FULL_SIMP_TAC std_ss [bir_mmap_w_w2n_def, FDOM_FINITE, IMAGE_FINITE,
                              FDOM_FMAP, FUN_FMAP_DEF, n2w_w2n] >>
    `n2w a = x` by (
      METIS_TAC [n2w_w2n, n2w_mod]
    ) >>
    ASM_REWRITE_TAC []
  ) >>

  ASM_REWRITE_TAC [] >>
  FULL_SIMP_TAC std_ss [] >>
  POP_ASSUM (ASSUME_TAC o (SPEC ``n2w (a MOD dimword (:'a)) : 'a word``)) >>

  FULL_SIMP_TAC (arith_ss++wordsLib.WORD_ss) [w2n_n2w, n2w_mod, arithmeticTheory.MOD_MOD]
);

val bir_FLOOKUP_mmap_n2w__thm = store_thm("bir_FLOOKUP_mmap_n2w__thm", ``
  !mmap a. FLOOKUP (bir_mmap_n2w mmap) a =
             OPTION_MAP n2w (FLOOKUP mmap ((w2n (a : 'a word))))
``,
  REPEAT STRIP_TAC >>
  REWRITE_TAC [FLOOKUP_DEF] >>

  `FDOM (bir_mmap_n2w mmap : 'a word |-> 'b word) =
   (IMAGE n2w ((FDOM mmap) INTER {n | n < dimword (:'a)}))` by (
    SIMP_TAC std_ss [bir_mmap_n2w_def, FDOM_FINITE, IMAGE_FINITE, FDOM_FMAP, INTER_FINITE]
  ) >>
  ASM_REWRITE_TAC [] >>
  POP_ASSUM (K ALL_TAC) >>

  SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>
  Cases_on `?x. (a = n2w x) /\ x IN FDOM mmap /\ x < dimword(:'a)` >- (
    ASM_REWRITE_TAC [] >>
    FULL_SIMP_TAC std_ss [n2w_w2n, w2n_n2w, bir_mmap_n2w_def] >>

    `a IN (IMAGE n2w (FDOM mmap ∩ {n | n < dimword (:α)}))` by (
      FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>
      METIS_TAC []
    ) >>

    REV_FULL_SIMP_TAC std_ss [FDOM_FINITE, IMAGE_FINITE, INTER_FINITE,
                              FDOM_FMAP, FUN_FMAP_DEF, n2w_w2n, w2n_n2w]
  ) >>

  ASM_REWRITE_TAC [] >>
  FULL_SIMP_TAC std_ss [] >>
  POP_ASSUM (ASSUME_TAC o (SPEC ``w2n (a : 'a word)``)) >>
  FULL_SIMP_TAC std_ss [n2w_w2n, w2n_lt]
);

val w2n_MOD_dimword_thm = prove(``
  !a. (w2n (a : 'a word)) MOD dimword (:'a) = w2n a
``,
  REPEAT STRIP_TAC >>
  SIMP_TAC (arith_ss++wordsLib.WORD_ss) [w2n_lt]
);

val bir_FLOOKUP_mmap_w2n_thm = store_thm("bir_FLOOKUP_mmap_w2n_thm", ``
  !mmap_w a. FLOOKUP (bir_mmap_w_w2n mmap_w) (w2n (a:'a word)) =
               OPTION_MAP w2n (FLOOKUP mmap_w a)
``,
  REPEAT STRIP_TAC >>
  METIS_TAC [bir_FLOOKUP_mmap_w2n__thm, n2w_w2n, w2n_MOD_dimword_thm]
);

val bir_FLOOKUP_mmap_n2w_thm = store_thm("bir_FLOOKUP_mmap_n2w_thm", ``
  !mmap a. FLOOKUP (bir_mmap_n2w mmap) (n2w a : 'a word) =
             OPTION_MAP n2w (FLOOKUP mmap (a MOD dimword (:'a)))
``,
  REPEAT STRIP_TAC >>
  REWRITE_TAC [bir_FLOOKUP_mmap_n2w__thm, w2n_n2w]
);



val bir_load_mmap_n2w_thm = store_thm("bir_load_mmap_n2w_thm", ``
  !mmap a.   bir_load_mmap_w (bir_mmap_n2w mmap) (a : 'a word)
           = n2w (bir_load_mmap mmap (w2n a)) : 'b word
``,
  REPEAT STRIP_TAC >>
  REWRITE_TAC [bir_load_mmap_w_alt_thm, bir_load_mmap_def, bir_FLOOKUP_mmap_n2w__thm] >>

  Cases_on `FLOOKUP mmap (w2n a)` >> (
    SIMP_TAC (std_ss++wordsLib.WORD_ss) [optionTheory.OPTION_MAP_DEF]
  )
);

val bir_load_mmap_w2n_thm = store_thm("bir_load_mmap_w2n_thm", ``
  !mmap_w a.   bir_load_mmap (bir_mmap_w_w2n mmap_w) (w2n (a : 'a word))
             = w2n (bir_load_mmap_w mmap_w a : 'b word)
``,
  REPEAT STRIP_TAC >>
  REWRITE_TAC [bir_load_mmap_w_alt_thm, bir_load_mmap_def, bir_FLOOKUP_mmap_w2n_thm] >>

  Cases_on `FLOOKUP mmap_w a` >> (
    SIMP_TAC (std_ss++wordsLib.WORD_ss) [optionTheory.OPTION_MAP_DEF]
  )
);



val bir_mmap_w_n2w_w2n_thm = store_thm("bir_mmap_w_n2w_w2n_thm", ``
  !mmap_w. bir_mmap_n2w (bir_mmap_w_w2n mmap_w) = mmap_w
``,
  REWRITE_TAC [fmap_eq_flookup, bir_FLOOKUP_mmap_n2w__thm,
               bir_FLOOKUP_mmap_w2n__thm, n2w_w2n, Once (GSYM w2n_MOD_dimword_thm)] >>
  REPEAT STRIP_TAC >>

  Cases_on `FLOOKUP mmap_w x` >> (
    SIMP_TAC (std_ss++wordsLib.WORD_ss) [optionTheory.OPTION_MAP_DEF, n2w_w2n]
  )
);

val bir_load_mmap_MOD_dimword_thm = store_thm("bir_load_mmap_MOD_dimword_thm", ``
  !mem_n a.   bir_load_mmap (bir_mmap_w_w2n (bir_mmap_n2w mem_n : 'a word |-> 'b word))
                            (a MOD dimword (:'a))
            = (bir_load_mmap mem_n (a MOD dimword (:'a))) MOD dimword (:'b)
``,
  REPEAT STRIP_TAC >>
  REWRITE_TAC [bir_load_mmap_def, bir_FLOOKUP_mmap_w2n__thm, bir_FLOOKUP_mmap_n2w__thm, w2n_n2w] >>

  Cases_on `FLOOKUP mem_n (a MOD dimword (:'a))` >> (
    SIMP_TAC arith_ss [w2n_n2w, ZERO_LT_dimword]
  )
);

val bir_load_mmap_w_bir_mmap_n2w_thm = store_thm("bir_load_mmap_w_bir_mmap_n2w_thm", ``
  !mem_n a.   bir_load_mmap_w (bir_mmap_n2w mem_n) a
            = n2w (bir_load_mmap mem_n (w2n a))
``,
  REPEAT STRIP_TAC >>
  REWRITE_TAC [bir_load_mmap_def, bir_load_mmap_w_alt_thm, bir_FLOOKUP_mmap_n2w__thm] >>

  Cases_on `FLOOKUP mem_n (w2n a)` >> (
    SIMP_TAC std_ss []
  )
);



val bir_load_w2n_mf2mm_load_n2w_thm = prove (``
  !mem_n a.
    (bir_load_mmap (bir_mmap_w_w2n (bir_mf2mm (bir_load_mmap_w
                      (bir_mmap_n2w mem_n : 'a word |-> 'b word))))
                   (a MOD dimword(:'a)))
    =
    ((bir_load_mmap mem_n (a MOD dimword(:'a))) MOD dimword(:'b))
``,

  REPEAT STRIP_TAC >>
  REWRITE_TAC [bir_load_mmap_def, bir_FLOOKUP_mmap_w2n__thm, bir_FLOOKUP_mmap_n2w__thm, w2n_n2w] >>

  Cases_on `FLOOKUP mem_n (a MOD dimword (:'a))` >> (
    SIMP_TAC arith_ss [w2n_n2w, ZERO_LT_dimword, bir_mf2mm_def] >>
    `(n2w a) IN (UNIV: 'a word -> bool)` by (
      ASM_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [WORD_FINITE]
    ) >>
    ASM_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [WORD_FINITE, FLOOKUP_FUN_FMAP, bir_load_mmap_n2w_thm, w2n_n2w, bir_load_mmap_def, arithmeticTheory.ZERO_MOD, ZERO_LT_dimword]
  )
);

val bir_load_mmap_n2w_FUPDATE_thm = prove(``
!mem_n a v.
bir_load_mmap_w (bir_mmap_n2w (FUPDATE mem_n (w2n a, v)))
=
(a =+ n2w v) (bir_load_mmap_w (bir_mmap_n2w mem_n))
``,
  REPEAT STRIP_TAC >>
  MATCH_MP_TAC boolTheory.EQ_EXT >>
  STRIP_TAC >>

  REWRITE_TAC [updateTheory.UPDATE_def] >>
  BETA_TAC >>
  REWRITE_TAC [bir_load_mmap_w_alt_thm] >>

  Cases_on `a = x` >> (
    ASM_SIMP_TAC std_ss [bir_FLOOKUP_mmap_n2w__thm, FLOOKUP_UPDATE, w2n_11]
  )
);



(* ---------------------------------------------------------------------- *)

val bir_load_w2n_mf_simp_thm = store_thm("bir_load_w2n_mf_simp_thm", ``
  !mem_f a. bir_load_mmap (bir_mmap_w_w2n (bir_mf2mm mem_f)) (w2n (a:'a word)) = w2n (mem_f a)
``,
  REPEAT STRIP_TAC >>
  SIMP_TAC std_ss [bir_load_mmap_def] >>

  ASSUME_TAC (SPEC ``UNIV : 'a word -> bool`` WORD_FINITE) >>
(* {x | mem_f x <> 0w}:'a word -> bool *)

  Cases_on `FLOOKUP (bir_mmap_w_w2n (bir_mf2mm mem_f)) (w2n a)` >- (
    FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [bir_mmap_w_w2n_def, bir_mf2mm_def] >>
    REV_FULL_SIMP_TAC (std_ss) [FLOOKUP_FUN_FMAP, FDOM_FMAP, IMAGE_FINITE] >>

    FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>

    METIS_TAC [word_0_n2w]
  ) >>

  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [bir_mmap_w_w2n_def, bir_mf2mm_def] >>
  REV_FULL_SIMP_TAC (std_ss) [FLOOKUP_FUN_FMAP, FDOM_FMAP, IMAGE_FINITE] >>
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>

  `a IN (UNIV : 'a word -> bool)` by (
    SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) []
  ) >>

  METIS_TAC [FUN_FMAP_DEF, n2w_w2n]
);

val n2w_bir_load_mmap_w2n_thm = store_thm("n2w_bir_load_mmap_w2n_thm", ``
  !mem_n. (\a. n2w (bir_load_mmap mem_n (w2n a))) = bir_load_mmap_w (bir_mmap_n2w mem_n)
``,
  SIMP_TAC std_ss [boolTheory.EQ_EXT, bir_load_mmap_w_bir_mmap_n2w_thm]
);



(*********************************)
(* Predicates describing lifting *)
(*********************************)


val bir_is_lifted_mem_exp_def = Define `bir_is_lifted_mem_exp
  (env:bir_var_environment_t) (e : bir_exp_t) (m : 'a word -> 'b word) <=>
  (?sa sb mem_n.
     (size_of_bir_immtype sa = (dimindex (:'a))) /\
     (size_of_bir_immtype sb = (dimindex (:'b))) /\
     (type_of_bir_exp e = SOME (BType_Mem sa sb)) /\
     (bir_env_vars_are_initialised env (bir_vars_of_exp e)) /\
     (bir_eval_exp e env = SOME (BVal_Mem sa sb mem_n)) /\
     (m = bir_load_mmap_w (bir_mmap_n2w mem_n)))
`;

val bir_is_lifted_imm_exp_def = Define `bir_is_lifted_imm_exp env e i =
  ((type_of_bir_exp e = SOME (BType_Imm (type_of_bir_imm i))) /\
  (bir_env_vars_are_initialised env (bir_vars_of_exp e)) /\
  (bir_eval_exp e env = SOME (BVal_Imm i)))`;


val _ = Datatype `bir_lift_val_t =
    BLV_Imm bir_imm_t
  | BLV_Mem ('a word -> 'b word)
`;


val bir_is_lifted_exp_def = Define `
  (bir_is_lifted_exp env e (BLV_Imm i) = bir_is_lifted_imm_exp env e i) /\
  (bir_is_lifted_exp env e (BLV_Mem m) = bir_is_lifted_mem_exp env e m)`;


(* Below, we often just want to write bir_is_lifted_mem_exp instead of
   bir_is_lifted_exp env e (BLV_Imm i). The bir_is_lifted_expLib using the following
   rewrite during preprocessing of lifting theorems. However, in the case of
   immediates, 2 new type vars are introduced by this rewrite. The ones used in the
   theorem below are chosen. They should be uncommon names to avoid clashes. In particular,
   avoid using these type-vars in any theorem you want to hand over to the lifting lib
   as a lemma. *)
val bir_is_lifted_exp_INTRO = store_thm ("bir_is_lifted_exp_INTRO",
``(!env e i.
      bir_is_lifted_imm_exp env e i <=>
      bir_is_lifted_exp env e ((BLV_Imm i):('addr_word_ty, 'value_word_ty) bir_lift_val_t)) /\
  (!env e m.
     bir_is_lifted_mem_exp env e m <=>
     bir_is_lifted_exp env e ((BLV_Mem m):('addr_word_ty, 'value_word_ty) bir_lift_val_t))``,
SIMP_TAC std_ss [bir_is_lifted_exp_def]);



(************)
(* Literals *)
(************)

(* One for all immediates, but should only be used for literals *)
val bir_is_lifted_imm_exp_CONSTANT = store_thm ("bir_is_lifted_imm_exp_CONSTANT",
  ``!env i. bir_is_lifted_imm_exp env (BExp_Const i) i``,

SIMP_TAC std_ss [bir_is_lifted_imm_exp_def,
  type_of_bir_exp_def, type_of_bir_val_def,
  bir_vars_of_exp_def, bir_env_oldTheory.bir_env_vars_are_initialised_EMPTY, bir_eval_exp_def]);


(*********************)
(* Unary expressions *)
(*********************)

val thm_t = build_immtype_t_conj
``!s uo env (w:'a word) e.

      bir_is_lifted_imm_exp env e (w2bs w s) ==>
      bir_is_lifted_imm_exp env (BExp_UnaryExp uo e)
        (w2bs (bir_unary_exp_GET_OPER uo w) s)``;

val bir_is_lifted_imm_exp_UNARY_EXP0 = prove (``^thm_t``,
SIMP_TAC (std_ss++holBACore_ss) [bir_is_lifted_imm_exp_def,
  bir_env_oldTheory.bir_env_vars_are_initialised_UNION, w2w_id]);


val bir_is_lifted_imm_exp_UNARY_EXP = save_thm ("bir_is_lifted_imm_exp_UNARY_EXP",
let
  val thm0 = bir_is_lifted_imm_exp_UNARY_EXP0
  val thm1 = SIMP_RULE (std_ss++DatatypeSimps.expand_type_quants_ss [``:bir_unary_exp_t``]) [
    bir_unary_exp_GET_OPER_def, GSYM CONJ_ASSOC, w2bs_REWRS, w2w_id] thm0
in
  thm1
end);


(**********************)
(* Binary expressions *)
(**********************)

val thm_t = build_immtype_t_conj
``!s bo env (w1:'a word) (w2 :'a word) e1 e2.

      bir_is_lifted_imm_exp env e1 (w2bs w1 s) ==>
      bir_is_lifted_imm_exp env e2 (w2bs w2 s) ==>
      bir_is_lifted_imm_exp env (BExp_BinExp bo e1 e2)
        (w2bs (bir_bin_exp_GET_OPER bo w1 w2) s)``;

val bir_is_lifted_imm_exp_BIN_EXP0 = prove (``^thm_t``,
SIMP_TAC (std_ss++holBACore_ss) [bir_is_lifted_imm_exp_def,
  bir_env_oldTheory.bir_env_vars_are_initialised_UNION, w2w_id]);

val bir_is_lifted_imm_exp_BIN_EXP = save_thm ("bir_is_lifted_imm_exp_BIN_EXP",
let
  val thm0 = bir_is_lifted_imm_exp_BIN_EXP0
  val thm1 = SIMP_RULE (std_ss++DatatypeSimps.expand_type_quants_ss [``:bir_bin_exp_t``]) [
    bir_bin_exp_GET_OPER_def, GSYM CONJ_ASSOC, w2bs_REWRS, w2w_id] thm0
in
  thm1
end);



val thm_t = build_immtype_t_conj
``!s bo env (w1:'a word) (n2 : num) e1.
      MEM bo [BIExp_LeftShift; BIExp_RightShift; BIExp_SignedRightShift] ==>
      (MEM n2 (COUNT_LIST (SUC (dimindex (:'a))))) ==>
      bir_is_lifted_imm_exp env e1 (w2bs w1 s) ==>
      bir_is_lifted_imm_exp env (BExp_BinExp bo e1 (BExp_Const (n2bs n2 s)))
        (w2bs (bir_bin_exp_GET_OPER bo w1 (n2w n2)) s)``;

val bir_is_lifted_imm_exp_SHIFTS_n2w0 = prove (``^thm_t``,
SIMP_TAC (std_ss++holBACore_ss) [bir_is_lifted_imm_exp_def,
  bir_env_oldTheory.bir_env_vars_are_initialised_UNION, w2w_id, bir_env_oldTheory.bir_env_vars_are_initialised_EMPTY]);

val bir_is_lifted_imm_exp_SHIFTS_n2w = save_thm ("bir_is_lifted_imm_exp_SHIFTS_n2w",
let
  val thm0 = bir_is_lifted_imm_exp_SHIFTS_n2w0
  val thm1 = SIMP_RULE (list_ss++wordsLib.WORD_ss) [
    bir_bin_exp_GET_OPER_def, GSYM CONJ_ASSOC, w2bs_REWRS, w2w_id,
    DISJ_IMP_THM, FORALL_AND_THM, n2bs_def] thm0
  val thm2 = SIMP_RULE (std_ss) [rich_listTheory.COUNT_LIST_compute,
    rich_listTheory.COUNT_LIST_AUX_compute, DISJ_IMP_THM, listTheory.MEM,
    FORALL_AND_THM] thm1
in
  thm2
end);




val thm_t = build_immtype_t_conj
``!s bo env (w1:'a word) (w2 : 'b word) e1 e2.
      (dimword (:'b) <= dimword (:'a)) ==>
      MEM bo [BIExp_LeftShift; BIExp_RightShift; BIExp_SignedRightShift] ==>
      bir_is_lifted_imm_exp env e1 (w2bs w1 s) ==>
      bir_is_lifted_imm_exp env e2 (w2bs w2 s) ==>
      bir_is_lifted_imm_exp env (BExp_BinExp bo e1 e2)
        (w2bs (bir_bin_exp_GET_OPER bo w1 (n2w (w2n w2))) s)``;

val bir_is_lifted_imm_exp_SHIFTS_w2n0 = prove (``^thm_t``,
SIMP_TAC (std_ss++holBACore_ss) [bir_is_lifted_imm_exp_def,
  bir_env_oldTheory.bir_env_vars_are_initialised_UNION, w2w_id, bir_env_oldTheory.bir_env_vars_are_initialised_EMPTY,
  w2w_def]);


val bir_is_lifted_imm_exp_SHIFTS_w2n = save_thm ("bir_is_lifted_imm_exp_SHIFTS_w2n",
let
  val aux_thm = prove (``dimword (:'b) <= n ==> (w2n (w:'b word) < n)``,
    REPEAT STRIP_TAC >>
    `w2n w < dimword (:'b)` by METIS_TAC[w2n_lt] >>
    DECIDE_TAC);

  val thm0 = bir_is_lifted_imm_exp_SHIFTS_w2n0
  val thm1 = SIMP_RULE (list_ss++wordsLib.SIZES_ss) [
    bir_bin_exp_GET_OPER_def, GSYM CONJ_ASSOC, w2bs_REWRS, w2w_id,
    DISJ_IMP_THM, IMP_CONJ_THM, FORALL_AND_THM, n2bs_def,
    GSYM wordsTheory.word_shift_bv, w2n_lt, aux_thm]
    thm0


  val words_sizes = List.map (fn sz => fcpLib.index_type (Arbnum.fromInt sz))
          bir_immSyntax.known_imm_sizes;

  val thm2 = LIST_CONJ (List.map (fn sz => INST_TYPE [``:'b`` |-> sz] thm1) words_sizes)

  val thm3 = SIMP_RULE (std_ss++wordsLib.SIZES_ss) [w2w_id, GSYM CONJ_ASSOC] thm2


in
  thm3
end);



(**********************)
(* Binary Preds       *)
(**********************)

val thm_t = build_immtype_t_conj
``!s bo env (w1:'a word) (w2 :'a word) e1 e2.

      bir_is_lifted_imm_exp env e1 (w2bs w1 s) ==>
      bir_is_lifted_imm_exp env e2 (w2bs w2 s) ==>
      bir_is_lifted_imm_exp env (BExp_BinPred bo e1 e2)
        (bool2b (bir_bin_pred_GET_OPER bo w1 w2))``;

val bir_is_lifted_imm_exp_BIN_PRED0 = prove (``^thm_t``,
SIMP_TAC (std_ss++holBACore_ss) [bir_is_lifted_imm_exp_def,
  bir_env_oldTheory.bir_env_vars_are_initialised_UNION, BType_Bool_def, w2w_id]);


val bir_is_lifted_imm_exp_BIN_PRED = save_thm ("bir_is_lifted_imm_exp_BIN_PRED",
let
  val thm0 = bir_is_lifted_imm_exp_BIN_PRED0
  val thm1 = SIMP_RULE (std_ss++DatatypeSimps.expand_type_quants_ss [``:bir_bin_pred_t``]) [
    bir_bin_pred_GET_OPER_def, GSYM CONJ_ASSOC, w2bs_REWRS, w2w_id] thm0
in
  thm1
end);


val bir_is_lifted_imm_exp_bool2w = store_thm (
"bir_is_lifted_imm_exp_bool2w",
``!env e b.
      bir_is_lifted_imm_exp env e (bool2b b) ==>
      bir_is_lifted_imm_exp env e (Imm1 (bool2w b))``,
SIMP_TAC std_ss [bir_immTheory.bool2b_def]);



(***********)
(* Casting *)
(***********)

(* The semantics of casting in bir contain a lot of redundancy.
   A low-cast is for example the same as a normal cast. So, the theorems
   below are designed carefully use the most appropriate cast operation. *)

(* No cast needed, since types are identical *)

val thm_t = build_immtype_t_conj
``!s env (w:'a word) e.
      bir_is_lifted_imm_exp env e (w2bs w s) ==> (
      bir_is_lifted_imm_exp env e (w2bs ((w2w w):'a word) s) /\
      bir_is_lifted_imm_exp env e (w2bs ((w2wh w):'a word) s) /\
      bir_is_lifted_imm_exp env e (w2bs ((sw2sw w):'a word) s))``;


val bir_is_lifted_imm_exp_NO_CAST0 = prove (``^thm_t``,
SIMP_TAC std_ss [w2w_id, sw2sw_id, w2wh_id]);

val bir_is_lifted_imm_exp_NO_CAST = save_thm ("bir_is_lifted_imm_exp_NO_CAST",
let
  val thm0 = bir_is_lifted_imm_exp_NO_CAST0
  val thm1 = SIMP_RULE std_ss [GSYM CONJ_ASSOC, w2bs_REWRS, IMP_CONJ_THM,
    FORALL_AND_THM] thm0
  val thm2 = ONCE_REWRITE_RULE [w2w_id] thm1
in
  thm2
end);


(* decreasing the word length, lower bits *)
val thm_t = build_immtype_t_conj_gen "sb" Type.beta (build_immtype_t_conj_gen "sa" Type.alpha
``!env (w:'b word) e.
      (size_of_bir_immtype sa < size_of_bir_immtype sb) ==>
      bir_is_lifted_imm_exp env e (w2bs w sb) ==> (
      bir_is_lifted_imm_exp env (BExp_Cast BIExp_LowCast e sa) (w2bs ((w2w w):'a word) sa) /\
      bir_is_lifted_imm_exp env (BExp_Cast BIExp_LowCast e sa) (w2bs ((sw2sw w):'a word) sa))``);

val bir_is_lifted_imm_exp_LCAST0 = prove (``^thm_t``,
SIMP_TAC (std_ss++holBACore_ss++wordsLib.WORD_ss) [bir_is_lifted_imm_exp_def,
  bir_env_oldTheory.bir_env_vars_are_initialised_UNION, bir_auxiliaryTheory.sw2sw_w2w_downcast,
  w2w_id]);

val bir_is_lifted_imm_exp_LCAST = save_thm ("bir_is_lifted_imm_exp_LCAST",
let
  val thm0 = bir_is_lifted_imm_exp_LCAST0
  val thm1 = SIMP_RULE std_ss [GSYM CONJ_ASSOC, w2bs_REWRS, w2w_id, size_of_bir_immtype_def,
    IMP_CONJ_THM, FORALL_AND_THM] thm0
in
  thm1
end);


(* decreasing the word length, higher bits *)
val thm_t = build_immtype_t_conj_gen "sb" Type.beta (build_immtype_t_conj_gen "sa" Type.alpha
``!env (w:'b word) e.
      (size_of_bir_immtype sa < size_of_bir_immtype sb) ==>
      bir_is_lifted_imm_exp env e (w2bs w sb) ==> (
      bir_is_lifted_imm_exp env (BExp_Cast BIExp_HighCast e sa) (w2bs ((w2wh w):'a word) sa))``);

val bir_is_lifted_imm_exp_HCAST0 = prove (``^thm_t``,
SIMP_TAC (std_ss++holBACore_ss++wordsLib.WORD_ss) [bir_is_lifted_imm_exp_def,
  bir_env_oldTheory.bir_env_vars_are_initialised_UNION, w2w_id]);

val bir_is_lifted_imm_exp_HCAST = save_thm ("bir_is_lifted_imm_exp_HCAST",
let
  val thm0 = bir_is_lifted_imm_exp_HCAST0
  val thm1 = SIMP_RULE std_ss [GSYM CONJ_ASSOC, w2bs_REWRS, w2w_id, size_of_bir_immtype_def,
    IMP_CONJ_THM, FORALL_AND_THM] thm0
in
  thm1
end);


(* increasing the word length, unsigned cast *)
val thm_t = build_immtype_t_conj_gen "sb" Type.beta (build_immtype_t_conj_gen "sa" Type.alpha
``!env (w:'b word) e.
      (size_of_bir_immtype sb < size_of_bir_immtype sa) ==>
      bir_is_lifted_imm_exp env e (w2bs w sb) ==> (
      bir_is_lifted_imm_exp env (BExp_Cast BIExp_UnsignedCast e sa) (w2bs ((w2w w):'a word) sa) /\
      bir_is_lifted_imm_exp env (BExp_Cast BIExp_UnsignedCast e sa) (w2bs ((w2wh w):'a word) sa))``);

val bir_is_lifted_imm_exp_UNSIGNED_CAST0 = prove (``^thm_t``,
SIMP_TAC (std_ss++holBACore_ss++wordsLib.WORD_ss) [bir_is_lifted_imm_exp_def,
  bir_env_oldTheory.bir_env_vars_are_initialised_UNION, w2w_id, w2wh_w2w]);

val bir_is_lifted_imm_exp_UNSIGNED_CAST = save_thm ("bir_is_lifted_imm_exp_UNSIGNED_CAST",
let
  val thm0 = bir_is_lifted_imm_exp_UNSIGNED_CAST0
  val thm1 = SIMP_RULE std_ss [GSYM CONJ_ASSOC, w2bs_REWRS, w2w_id, size_of_bir_immtype_def,
     IMP_CONJ_THM, FORALL_AND_THM] thm0
in
  thm1
end);



(* increasing the word length, signed cast, notice that signed casts are not available
   for single bits *)
val thm_t = build_immtype_t_conj_gen "sb" Type.beta (build_immtype_t_conj_gen "sa" Type.alpha
``!env (w:'b word) e.
      (size_of_bir_immtype sb <> 1) ==>
      (size_of_bir_immtype sb < size_of_bir_immtype sa) ==>
      bir_is_lifted_imm_exp env e (w2bs w sb) ==> (
      bir_is_lifted_imm_exp env (BExp_Cast BIExp_SignedCast e sa) (w2bs ((sw2sw w):'a word) sa))``);

val bir_is_lifted_imm_exp_SIGNED_CAST0 = prove (``^thm_t``,
SIMP_TAC (std_ss++holBACore_ss++wordsLib.WORD_ss) [bir_is_lifted_imm_exp_def,
  bir_env_oldTheory.bir_env_vars_are_initialised_UNION, w2w_id]);

val bir_is_lifted_imm_exp_SIGNED_CAST = save_thm ("bir_is_lifted_imm_exp_SIGNED_CAST",
let
  val thm0 = bir_is_lifted_imm_exp_SIGNED_CAST0
  val thm1 = SIMP_RULE std_ss [GSYM CONJ_ASSOC, w2bs_REWRS, w2w_id, size_of_bir_immtype_def,
     IMP_CONJ_THM, FORALL_AND_THM] thm0
in
  thm1
end);



(* combine everything *)
val bir_is_lifted_imm_exp_CASTS = save_thm ("bir_is_lifted_imm_exp_CASTS",
  SIMP_RULE std_ss [GSYM CONJ_ASSOC] (
  LIST_CONJ [bir_is_lifted_imm_exp_NO_CAST,
             bir_is_lifted_imm_exp_LCAST,
             bir_is_lifted_imm_exp_HCAST,
             bir_is_lifted_imm_exp_UNSIGNED_CAST,
             bir_is_lifted_imm_exp_SIGNED_CAST]));



(****************)
(* if-then-else *)
(****************)

val thm_t = build_immtype_t_conj
``!s env c (w1:'a word) w2 ec e1 e2.
      bir_is_lifted_imm_exp env ec (bool2b c) ==>
      bir_is_lifted_imm_exp env e1 (w2bs w1 s) ==>
      bir_is_lifted_imm_exp env e2 (w2bs w2 s) ==>
      bir_is_lifted_imm_exp env (BExp_IfThenElse ec e1 e2) (w2bs (if c then w1 else w2) s)``;

val bir_is_lifted_imm_exp_COND0 = prove (``^thm_t``,
SIMP_TAC (std_ss++holBACore_ss++boolSimps.LIFT_COND_ss) [bir_is_lifted_imm_exp_def,
  bir_env_oldTheory.bir_env_vars_are_initialised_UNION, BType_Bool_def, w2w_id]);

val bir_is_lifted_imm_exp_COND = save_thm ("bir_is_lifted_imm_exp_COND",
let
  val thm0 = bir_is_lifted_imm_exp_COND0
  val thm1 = SIMP_RULE std_ss [GSYM CONJ_ASSOC, w2bs_REWRS, IMP_CONJ_THM,
    FORALL_AND_THM, w2w_id] thm0
in
  thm1
end);

val bir_is_lifted_imm_exp_PROTECTED_COND = save_thm ("bir_is_lifted_imm_exp_PROTECTED_COND",
  PURE_REWRITE_RULE [GSYM PROTECTED_COND_def] bir_is_lifted_imm_exp_COND);


(****************)
(* Load         *)
(****************)

val bir_is_lifted_imm_exp_LOAD0 = prove (
``!guard sa sv sr env en em em ea (va :'a word) mem_f.
    (size_of_bir_immtype sa = (dimindex (:'a))) ==>
    (size_of_bir_immtype sv = (dimindex (:'v))) ==>
    (size_of_bir_immtype sr = (dimindex (:'r))) ==>
    (guard sa sv sr en) ==>
    bir_is_lifted_mem_exp env em (mem_f : 'a word -> 'v word) ==>
    bir_is_lifted_imm_exp env ea (w2bs va sa) ==>
    (!r.
    (bir_load_from_mem sv sr sa (bir_mmap_w_w2n (bir_mf2mm mem_f)) en (w2n va) = SOME r) ==>

    (bir_is_lifted_imm_exp env (BExp_Load em ea en sr) r))
``,
  SIMP_TAC (std_ss++holBACore_ss++wordsLib.WORD_ss) [bir_is_lifted_imm_exp_def,
    bir_is_lifted_mem_exp_def, PULL_EXISTS,
    bir_eval_load_BASIC_REWR, bir_env_oldTheory.bir_env_vars_are_initialised_UNION] >>
  REPEAT (GEN_TAC ORELSE DISCH_TAC) >>
  `sa' = sa` by METIS_TAC[size_of_bir_immtype_INJ] >>
  `sb = sv` by METIS_TAC[size_of_bir_immtype_INJ] >>
  FULL_SIMP_TAC std_ss [] >>
  REPEAT STRIP_TAC >- (
    METIS_TAC[bir_exp_memTheory.type_of_bir_load_from_mem]
  ) >- (
    FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_load_from_mem_EQ_SOME] >>
    FULL_SIMP_TAC (std_ss++holBACore_ss) []
  ) >>

  `bir_load_from_mem sv sr sa mem_n en
	  (b2n (w2bs va sa)) =
   bir_load_from_mem sv sr sa (bir_mmap_w_w2n (bir_mf2mm mem_f)) en (w2n va)` suffices_by (
     STRIP_TAC >>
     FULL_SIMP_TAC std_ss []
  ) >>
  Q.PAT_X_ASSUM `bir_load_from_mem _ _ _ _ _ _ = SOME _` (K ALL_TAC) >>

  ASM_SIMP_TAC std_ss [bir_load_from_mem_def, GSYM bitstringTheory.w2v_v2w, bitstringTheory.v2w_n2v,
    bir_load_bitstring_from_mmap_def,
    w2bs_def, b2n_n2bs, n2w_w2n, bir_auxiliaryTheory.w2n_MOD_2EXP_ID] >>
  ASM_SIMP_TAC arith_ss [w2n_n2w, bir_mem_addr_def, GSYM wordsTheory.MOD_2EXP_DIMINDEX,
    wordsTheory.ZERO_LT_dimword, bir_load_mmap_MOD_dimword_thm, n2w_mod, bir_load_w2n_mf2mm_load_n2w_thm]
);


fun bir_is_lifted_imm_exp_LOAD_gen gt =
let
  val thms0 = MP_size_of_bir_immtype_t_EQ_dimindex (SPEC gt bir_is_lifted_imm_exp_LOAD0)
  val thms1 = flatten (map MP_size_of_bir_immtype_t_EQ_dimindex thms0)
  val thms2 = flatten (map MP_size_of_bir_immtype_t_EQ_dimindex thms1)

  val thm1 = LIST_CONJ thms2
  val thm2 = SIMP_RULE (std_ss++holBACore_ss++(DatatypeSimps.expand_type_quants_ss [``:bir_endian_t``])) [
     bir_load_from_mem_REWRS, n2w_w2n, w2bs_REWRS, w2w_id, bir_mem_addr_w2n_SIZES, bir_mem_addr_w2n_add_SIZES, GSYM CONJ_ASSOC, FORALL_AND_THM, bir_load_w2n_mf_simp_thm] thm1
in
  thm2
end;

fun mk_bir_is_lifted_imm_exp_LOAD addr_size value_size result_size endian =
  bir_is_lifted_imm_exp_LOAD_gen ``\(sa:bir_immtype_t) (sv:bir_immtype_t) (sr:bir_immtype_t) (en:bir_endian_t). (sa = ^addr_size) /\ (sv = ^value_size) /\ (sr = ^result_size) /\ (en = ^endian)``;


(* Build the theorem for common values *)
val bir_is_lifted_imm_exp_LOAD_ENDIAN = save_thm ("bir_is_lifted_imm_exp_LOAD_ENDIAN",
  bir_is_lifted_imm_exp_LOAD_gen ``\(sa:bir_immtype_t) (sv:bir_immtype_t) (sr:bir_immtype_t) (en:bir_endian_t). (sv <> sr) /\ (sa <> Bit1) /\ (sv <> Bit1)``);

val bir_is_lifted_imm_exp_LOAD_ENDIAN_BYTE = save_thm ("bir_is_lifted_imm_exp_LOAD_ENDIAN_BYTE",
  bir_is_lifted_imm_exp_LOAD_gen ``\(sa:bir_immtype_t) (sv:bir_immtype_t) (sr:bir_immtype_t) (en:bir_endian_t). (sa <> Bit1) /\ (sv <> sr) /\ (sv = Bit8)``);

val bir_is_lifted_imm_exp_LOAD_NO_ENDIAN = save_thm ("bir_is_lifted_imm_exp_LOAD_NO_ENDIAN",
  bir_is_lifted_imm_exp_LOAD_gen ``\(sa:bir_immtype_t) (sv:bir_immtype_t) (sr:bir_immtype_t) (en:bir_endian_t). (sv = sr)``);





(****************)
(* STORE        *)
(****************)

val bir_update_mmap_words_def = Define `
    (!mmap a.      (bir_update_mmap_words mmap a [] = mmap)) /\
    (!mmap a v vs. (bir_update_mmap_words mmap a (v::vs) =
                        bir_update_mmap_words ((a =+ v2w v) mmap) (a + 1w) vs))`;

val bir_update_mmap_words_rev_def = Define `
    (!mmap a.      (bir_update_mmap_words_rev mmap a [] = mmap)) /\
    (!mmap a v vs. (bir_update_mmap_words_rev mmap a (v::vs) =
                         ((a =+ v2w v) (bir_update_mmap_words_rev mmap (a + 1w) vs))))`;

val bir_store_in_mem_words_def = Define `bir_store_in_mem_words
  (value_ty : bir_immtype_t) (a_ty : bir_immtype_t) (result : bir_imm_t) (mmap : 'a word -> 'v word) (en: bir_endian_t) (a : 'a word) =

   let result_ty = type_of_bir_imm result in
   case (bir_number_of_mem_splits value_ty result_ty a_ty) of
    | NONE => NONE
    | SOME (n:num) => (
        let vs = bitstring_split (size_of_bir_immtype value_ty) (b2v result) in
        let vs' = (case en of BEnd_LittleEndian => SOME (REVERSE vs)
                          |  BEnd_BigEndian => SOME vs
                          |  BEnd_NoEndian => if (n = 1) then SOME vs else NONE) in

        case vs' of NONE => NONE
                 |  SOME vs'' => SOME (bir_update_mmap_words mmap a vs'')
   )`;

val bir_store_in_mem_words_rev_def = Define `bir_store_in_mem_words_rev
  (value_ty : bir_immtype_t) (a_ty : bir_immtype_t) (result : bir_imm_t) (mmap : 'a word -> 'v word) (en: bir_endian_t) (a : 'a word) =

   let result_ty = type_of_bir_imm result in
   case (bir_number_of_mem_splits value_ty result_ty a_ty) of
    | NONE => NONE
    | SOME (n:num) => (
        let vs = bitstring_split (size_of_bir_immtype value_ty) (b2v result) in
        let vs' = (case en of BEnd_LittleEndian => SOME (REVERSE vs)
                          |  BEnd_BigEndian => SOME vs
                          |  BEnd_NoEndian => if (n = 1) then SOME vs else NONE) in

        case vs' of NONE => NONE
                 |  SOME vs'' => SOME (bir_update_mmap_words_rev mmap a vs'')
   )`;

val v2w_w2v_SEG_GEN = store_thm ("v2w_w2v_SEG_GEN",
  ``!s b (w:'a word).
      (s + b <= dimindex (:'a)) ==>
      (dimindex (:'b) = s) ==>
      ((v2w (SEG s b (w2v w)) : 'b word) =
        (((dimindex (:'a) - SUC b)) >< (dimindex (:'a) - (b + s))) w)``,

REPEAT STRIP_TAC >>
ONCE_REWRITE_TAC [fcpTheory.CART_EQ] >>
ASM_SIMP_TAC (list_ss++boolSimps.EQUIV_EXTRACT_ss) [bitstringTheory.v2w_def, fcpTheory.FCP_BETA,
  bitstringTheory.testbit, LET_DEF, rich_listTheory.LENGTH_SEG, word_extract_def,
  bitstringTheory.length_w2v, w2w,
  rich_listTheory.SEG_TAKE_DROP,
  rich_listTheory.EL_TAKE,
  rich_listTheory.EL_DROP,
  bitstringTheory.el_w2v,
  word_bits_def]);


val v2w_w2v_SEG_REWRS = save_thm ("v2w_w2v_SEG_REWRS",
let
  val words_sizes = bir_immSyntax.known_imm_sizes;

  val combined_sizes = flatten (map (fn sz1 => map (fn sz2 => (sz1, sz2)) words_sizes) words_sizes)
  val combined_sizes = filter (fn (sz1, sz2) => (sz1 < sz2) andalso (sz2 mod sz1 = 0)) combined_sizes

  fun mk_sizes_thms (sz1, sz2) = let
    val sz1_ty = fcpLib.index_type (Arbnum.fromInt sz1)
    val sz2_ty = fcpLib.index_type (Arbnum.fromInt sz2)

    val thm0 = INST_TYPE [Type.alpha |-> sz2_ty, Type.beta |-> sz1_ty] v2w_w2v_SEG_GEN
    val thm1 = SIMP_RULE (arith_ss++wordsLib.SIZES_ss) [] thm0

    fun get_inst_sizes c =
       if (c < sz2) then c::(get_inst_sizes (c+sz1)) else []
    val b_values = List.map (fn i => numSyntax.mk_numeral (Arbnum.fromInt i)) (get_inst_sizes 0)

    val thms = List.map (fn i =>
       SIMP_RULE arith_ss [] (SPEC i thm1)) b_values
  in thms end

  val thm0 = LIST_CONJ (flatten (map mk_sizes_thms combined_sizes))
in
  thm0
end);


val bir_store_in_mem_words_REWRS = save_thm ("bir_store_in_mem_words_REWRS",
let
  val thm_def = prove (``!(value_ty :bir_immtype_t) (a_ty :bir_immtype_t) (result :bir_imm_t)
      (mmap :'a word -> 'v word) (en :bir_endian_t) (a :'a word).
     (size_of_bir_immtype value_ty = dimindex (:'v)) ==>
     (size_of_bir_immtype a_ty = dimindex (:'a)) ==> (
     bir_store_in_mem_words value_ty a_ty result mmap en a =
     (let (result_ty :bir_immtype_t) = type_of_bir_imm result
      in
        case bir_number_of_mem_splits value_ty result_ty a_ty of
          (NONE :num option) => (NONE :('a word -> 'v word) option)
        | SOME n =>
            (let (vs :bitstring list) =
                   bitstring_split (size_of_bir_immtype value_ty)
                     (b2v result)
             in
             let (vs' :bitstring list option) =
                   case en of
                     BEnd_BigEndian => SOME vs
                   | BEnd_LittleEndian => SOME (REVERSE vs)
                   | BEnd_NoEndian =>
                       if n = (1 :num) then SOME vs
                       else (NONE :bitstring list option)
             in
               case vs' of
                 (NONE :bitstring list option) =>
                   (NONE :('a word -> 'v word) option)
               | SOME vs'' => SOME (bir_update_mmap_words mmap a vs''))))``,
     SIMP_TAC std_ss [bir_store_in_mem_words_def])


  val thms1 = MP_size_of_bir_immtype_t_EQ_dimindex thm_def
  val thms2 = flatten (map MP_size_of_bir_immtype_t_EQ_dimindex thms1)
  val thm0 = LIST_CONJ thms2

  val thm1 = SIMP_RULE (list_ss++DatatypeSimps.expand_type_quants_ss [``:bir_immtype_t``, ``:bir_imm_t``]) [
    bir_number_of_mem_splits_REWRS, LET_DEF, type_of_bir_imm_def] thm0

  val thm2 = SIMP_RULE (list_ss++wordsLib.SIZES_ss) [b2v_def, bitstring_split_num_REWRS,
     bitstringTheory.length_w2v, size_of_bir_immtype_def] thm1
  val thm3 = SIMP_RULE (list_ss++holBACore_ss++(DatatypeSimps.expand_type_quants_ss [``:bir_endian_t``])) [LET_DEF] thm2

  val thm4 = Ho_Rewrite.REWRITE_RULE [fold_bir_endian_THM] thm3

  val thm5 = SIMP_RULE (std_ss++wordsLib.WORD_ss) [bir_update_mmap_words_def, bitstringTheory.v2w_w2v, v2w_w2v_SEG_REWRS] thm4


  val thm6 = SIMP_RULE list_ss [GSYM CONJ_ASSOC, FORALL_AND_THM] thm5

in thm6
end);

val bir_store_in_mem_words_rev_REWRS = save_thm ("bir_store_in_mem_words_rev_REWRS",
let
  val thm_def = prove (``!(value_ty :bir_immtype_t) (a_ty :bir_immtype_t) (result :bir_imm_t)
      (mmap :'a word -> 'v word) (en :bir_endian_t) (a :'a word).
     (size_of_bir_immtype value_ty = dimindex (:'v)) ==>
     (size_of_bir_immtype a_ty = dimindex (:'a)) ==> (
     bir_store_in_mem_words_rev value_ty a_ty result mmap en a =
     (let (result_ty :bir_immtype_t) = type_of_bir_imm result
      in
        case bir_number_of_mem_splits value_ty result_ty a_ty of
          (NONE :num option) => (NONE :('a word -> 'v word) option)
        | SOME n =>
            (let (vs :bitstring list) =
                   bitstring_split (size_of_bir_immtype value_ty)
                     (b2v result)
             in
             let (vs' :bitstring list option) =
                   case en of
                     BEnd_BigEndian => SOME vs
                   | BEnd_LittleEndian => SOME (REVERSE vs)
                   | BEnd_NoEndian =>
                       if n = (1 :num) then SOME vs
                       else (NONE :bitstring list option)
             in
               case vs' of
                 (NONE :bitstring list option) =>
                   (NONE :('a word -> 'v word) option)
               | SOME vs'' => SOME (bir_update_mmap_words_rev mmap a vs''))))``,
     SIMP_TAC std_ss [bir_store_in_mem_words_rev_def])


  val thms1 = MP_size_of_bir_immtype_t_EQ_dimindex thm_def
  val thms2 = flatten (map MP_size_of_bir_immtype_t_EQ_dimindex thms1)
  val thm0 = LIST_CONJ thms2

  val thm1 = SIMP_RULE (list_ss++DatatypeSimps.expand_type_quants_ss [``:bir_immtype_t``, ``:bir_imm_t``]) [
    bir_number_of_mem_splits_REWRS, LET_DEF, type_of_bir_imm_def] thm0

  val thm2 = SIMP_RULE (list_ss++wordsLib.SIZES_ss) [b2v_def, bitstring_split_num_REWRS,
     bitstringTheory.length_w2v, size_of_bir_immtype_def] thm1
  val thm3 = SIMP_RULE (list_ss++holBACore_ss++(DatatypeSimps.expand_type_quants_ss [``:bir_endian_t``])) [LET_DEF] thm2

  val thm4 = Ho_Rewrite.REWRITE_RULE [fold_bir_endian_THM] thm3

  val thm5 = SIMP_RULE (std_ss++wordsLib.WORD_ss) [bir_update_mmap_words_rev_def, bitstringTheory.v2w_w2v, v2w_w2v_SEG_REWRS] thm4


  val thm6 = SIMP_RULE list_ss [GSYM CONJ_ASSOC, FORALL_AND_THM] thm5

in thm6
end);



val bir_update_mmap_words_INTRO = store_thm ("bir_update_mmap_words_INTRO",
``!sa (a: 'a word).
    (size_of_bir_immtype sa = dimindex (:'a)) ==>
    !vs va_n va mem_n.
    (bir_mem_addr sa va_n = w2n va) ==>
    (n2w (bir_load_mmap (bir_update_mmap sa mem_n va_n vs) (w2n a)) =
                        (bir_update_mmap_words (bir_load_mmap_w (bir_mmap_n2w mem_n)) va vs) a)
``,
  NTAC 2 GEN_TAC >> STRIP_TAC >>
  Induct >> (
    SIMP_TAC std_ss [bir_update_mmap_def, bir_update_mmap_words_def, bir_load_mmap_w_bir_mmap_n2w_thm]
  ) >>
  REPEAT STRIP_TAC >>
  Q.PAT_X_ASSUM `!va_n va mem_n. _` (MP_TAC o Q.SPECL [`SUC va_n`, `va + 1w`]) >>
  `bir_mem_addr sa (SUC va_n) = w2n (va + 1w)` by (
    Q.PAT_X_ASSUM `_ = w2n va` (MP_TAC o GSYM) >>
    FULL_SIMP_TAC std_ss [bir_mem_addr_def, bitTheory.MOD_2EXP_def,
      GSYM dimword_def] >>
    Cases_on `va` >>
    ASM_SIMP_TAC arith_ss [w2n_n2w, word_add_n2w,
      bitTheory.MOD_PLUS_LEFT, arithmeticTheory.ADD1]
  ) >>
  ASM_SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss) [(* updateTheory.UPDATE_def, *)
    w2n_11, bitstringTheory.n2w_v2n, bir_load_mmap_n2w_FUPDATE_thm]
);

val bir_update_mmap_words_rev_INTRO = store_thm ("bir_update_mmap_words_rev_INTRO",
``!sa (a: 'a word).
    (size_of_bir_immtype sa = dimindex (:'a)) ==>
    !vs va_n va mem_n.
    (bir_mem_addr sa va_n = w2n va) ==>
    (n2w (bir_load_mmap (bir_update_mmap sa mem_n va_n vs) (w2n a)) =
                        (bir_update_mmap_words_rev (bir_load_mmap_w (bir_mmap_n2w mem_n)) va vs) a)
``,
  NTAC 2 GEN_TAC >> STRIP_TAC >>
  Induct >> (
    SIMP_TAC std_ss [bir_update_mmap_def, bir_update_mmap_words_rev_def,
                     bir_load_mmap_w_bir_mmap_n2w_thm]
  ) >>
  REPEAT STRIP_TAC >>
  Q.PAT_X_ASSUM `!va_n va mem_n. _` (MP_TAC o Q.SPECL [`SUC va_n`, `va + 1w`]) >>
  `bir_mem_addr sa (SUC va_n) = w2n (va + 1w)` by (
    Q.PAT_X_ASSUM `_ = w2n va` (MP_TAC o GSYM) >>
    FULL_SIMP_TAC std_ss [bir_mem_addr_def, bitTheory.MOD_2EXP_def,
      GSYM dimword_def] >>
    Cases_on `va` >>
    ASM_SIMP_TAC arith_ss [w2n_n2w, word_add_n2w,
      bitTheory.MOD_PLUS_LEFT, arithmeticTheory.ADD1]
  ) >>


  REPEAT STRIP_TAC >>
  REV_FULL_SIMP_TAC std_ss [] >>

  ASM_SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss) [(* updateTheory.UPDATE_def, *)
    w2n_11, bitstringTheory.n2w_v2n, bir_load_mmap_n2w_FUPDATE_thm, bir_update_mmap_words_rev_def]
);


val bir_update_mmap_words_INTRO_w2n = store_thm ("bir_update_mmap_words_INTRO_w2n",
``!sa (a: 'a word) vs va_n va mem_n.
    (size_of_bir_immtype sa = dimindex (:'a)) ==>
    (n2w (bir_load_mmap (bir_update_mmap sa mem_n va_n vs) (w2n a)) =
                        (bir_update_mmap_words (bir_load_mmap_w (bir_mmap_n2w mem_n)) (n2w va_n) vs) a)``,

REPEAT STRIP_TAC >>
`(bir_mem_addr sa va_n = w2n (n2w va_n))` suffices_by METIS_TAC[bir_update_mmap_words_INTRO] >>
ASM_SIMP_TAC std_ss [bir_mem_addr_def, w2n_n2w,
  bitTheory.MOD_2EXP_def, GSYM dimword_def]);


val bir_is_lifted_mem_exp_STORE0 = prove (
``!guard sa sv sr env en em em ea (va :'a word) er (vr : 'r word) mem_f.
    (size_of_bir_immtype sa = (dimindex (:'a))) ==>
    (size_of_bir_immtype sv = (dimindex (:'v))) ==>
    (size_of_bir_immtype sr = (dimindex (:'r))) ==>
    (guard sa sv sr en) ==>
    bir_is_lifted_mem_exp env em (mem_f : 'a word -> 'v word) ==>
    bir_is_lifted_imm_exp env ea (w2bs va sa) ==>
    bir_is_lifted_imm_exp env er (w2bs vr sr) ==>
    (!r.
    (bir_store_in_mem_words sv sa (w2bs vr sr) mem_f en va = SOME r) ==>
    (bir_is_lifted_mem_exp env (BExp_Store em ea en er) r))
``,
  SIMP_TAC (std_ss++holBACore_ss++wordsLib.WORD_ss) [bir_is_lifted_imm_exp_def,
    bir_is_lifted_mem_exp_def, PULL_EXISTS,
    bir_env_oldTheory.bir_env_vars_are_initialised_UNION, bir_eval_store_BASIC_REWR] >>
  REPEAT (GEN_TAC ORELSE DISCH_TAC) >>
  `sa' = sa` by METIS_TAC[size_of_bir_immtype_INJ] >>
  `sb = sv` by METIS_TAC[size_of_bir_immtype_INJ] >>
  REPEAT (BasicProvers.VAR_EQ_TAC) >>

  FULL_SIMP_TAC std_ss [w2n_n2w, w2bs_def, b2n_n2bs, bitTheory.MOD_2EXP_def,
    GSYM dimword_def, w2n_lt] >>

  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_store_in_mem_words_def, LET_DEF,
    bir_store_in_mem_def] >>

  Cases_on `bir_number_of_mem_splits sb sr sa` >> FULL_SIMP_TAC std_ss [] >>
  rename1 `_ = SOME n` >>
  REPEAT CASE_TAC >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
    REPEAT BasicProvers.VAR_EQ_TAC >>
    ASM_SIMP_TAC (std_ss++boolSimps.ETA_ss) [bir_update_mmap_words_INTRO_w2n, n2w_w2n] >>

    METIS_TAC [bir_update_mmap_words_INTRO_w2n, n2w_w2n, bir_load_mmap_w_bir_mmap_n2w_thm]
  )
);


fun bir_is_lifted_mem_exp_STORE_gen gt =
let
  val thms0 = MP_size_of_bir_immtype_t_EQ_dimindex (SPEC gt bir_is_lifted_mem_exp_STORE0)
  val thms1 = flatten (map MP_size_of_bir_immtype_t_EQ_dimindex thms0)
  val thms2 = flatten (map MP_size_of_bir_immtype_t_EQ_dimindex thms1)

  val thm1 = LIST_CONJ thms2
  val thm2 = SIMP_RULE (std_ss++holBACore_ss++(DatatypeSimps.expand_type_quants_ss [``:bir_endian_t``])) [n2w_w2n, w2bs_REWRS, w2w_id, bir_mem_addr_w2n_SIZES, bir_mem_addr_w2n_add_SIZES, GSYM CONJ_ASSOC, FORALL_AND_THM, bir_store_in_mem_words_REWRS] thm1
in
  thm2
end;

fun mk_bir_is_lifted_mem_exp_STORE addr_size value_size result_size endian =
  bir_is_lifted_mem_exp_STORE_gen ``\(sa:bir_immtype_t) (sv:bir_immtype_t) (sr:bir_immtype_t) (en:bir_endian_t). (sa = ^addr_size) /\ (sv = ^value_size) /\ (sr = ^result_size) /\ (en = ^endian)``;


(* Build the theorem for common values *)
val bir_is_lifted_mem_exp_STORE_ENDIAN = save_thm ("bir_is_lifted_mem_exp_STORE_ENDIAN",
  bir_is_lifted_mem_exp_STORE_gen ``\(sa:bir_immtype_t) (sv:bir_immtype_t) (sr:bir_immtype_t) (en:bir_endian_t). (sv <> sr) /\ (sa <> Bit1) /\ (sv <> Bit1)``);

val bir_is_lifted_mem_exp_STORE_ENDIAN_BYTE = save_thm ("bir_is_lifted_mem_exp_STORE_ENDIAN_BYTE",
  bir_is_lifted_mem_exp_STORE_gen ``\(sa:bir_immtype_t) (sv:bir_immtype_t) (sr:bir_immtype_t) (en:bir_endian_t). (sa <> Bit1) /\ (sv <> sr) /\ (sv = Bit8)``);

val bir_is_lifted_mem_exp_STORE_NO_ENDIAN = save_thm ("bir_is_lifted_mem_exp_STORE_NO_ENDIAN",
  bir_is_lifted_mem_exp_STORE_gen ``\(sa:bir_immtype_t) (sv:bir_immtype_t) (sr:bir_immtype_t) (en:bir_endian_t). (sv = sr)``);



(***************)
(* boolean ops *)
(***************)

val bir_is_lifted_imm_exp_implies_is_bool_exp_env = store_thm ("bir_is_lifted_imm_exp_implies_is_bool_exp_env",
``!env e b.
    bir_is_lifted_imm_exp env e (bool2b b) ==>
    bir_is_bool_exp_env env e``,

SIMP_TAC std_ss [bir_is_lifted_imm_exp_def, bir_is_bool_exp_env_def,
  bir_is_bool_exp_def, type_of_bool2b]);


val bir_is_lifted_imm_exp_bool2b_TF = prove (
``(!env. bir_is_lifted_imm_exp env bir_exp_true (bool2b T)) /\
  (!env. bir_is_lifted_imm_exp env bir_exp_false (bool2b F))``,

SIMP_TAC (std_ss++holBACore_ss) [bir_is_lifted_imm_exp_def,
  bir_exp_true_def, bir_exp_false_def, bir_env_oldTheory.bir_env_vars_are_initialised_EMPTY]);


val bir_is_lifted_imm_exp_bool2b_COND = prove (
``!env c b1 b2 ec e1 e2.
      bir_is_lifted_imm_exp env ec (bool2b c) ==>
      bir_is_lifted_imm_exp env e1 (bool2b b1) ==>
      bir_is_lifted_imm_exp env e2 (bool2b b2) ==>
      bir_is_lifted_imm_exp env (BExp_IfThenElse ec e1 e2) (bool2b (if c then b1 else b2))``,

SIMP_TAC (std_ss++holBACore_ss++boolSimps.LIFT_COND_ss) [bir_is_lifted_imm_exp_def,
  bir_env_oldTheory.bir_env_vars_are_initialised_UNION, BType_Bool_def]);


val bir_is_lifted_imm_exp_bool2b_UnaryExp0 = prove (
``!uo bop env e b.
      (bir_unary_exp_GET_BOOL_OPER uo = SOME (T, bop)) ==>
      bir_is_lifted_imm_exp env e (bool2b b) ==>
      bir_is_lifted_imm_exp env (BExp_UnaryExp uo e) (bool2b (bop b))``,

REPEAT STRIP_TAC >>
`bir_unary_exp uo (bool2b b) = bool2b (bop b)` by METIS_TAC[
  bir_unary_exp_GET_BOOL_OPER_THM] >>
FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_is_lifted_imm_exp_def]);


val bir_is_lifted_imm_exp_bool2b_UnaryExp =
  SIMP_RULE (std_ss++DatatypeSimps.expand_type_quants_ss[``:bir_unary_exp_t``]) [
    bir_unary_exp_GET_BOOL_OPER_def]
    bir_is_lifted_imm_exp_bool2b_UnaryExp0;


val bir_is_lifted_imm_exp_bool2b_BinExp0 = prove (
``!uo bop env e1 e2 b1 b2.
      (bir_bin_exp_GET_BOOL_OPER uo = SOME (T, bop)) ==>
      bir_is_lifted_imm_exp env e1 (bool2b b1) ==>
      bir_is_lifted_imm_exp env e2 (bool2b b2) ==>
      bir_is_lifted_imm_exp env (BExp_BinExp uo e1 e2) (bool2b (bop b1 b2))``,

REPEAT STRIP_TAC >>
`bir_bin_exp uo (bool2b b1) (bool2b b2) = bool2b (bop b1 b2)` by METIS_TAC[
  bir_bin_exp_GET_BOOL_OPER_THM] >>
FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_is_lifted_imm_exp_def,
  bir_env_oldTheory.bir_env_vars_are_initialised_UNION]);


val bir_is_lifted_imm_exp_bool2b_BinExp =
  SIMP_RULE (std_ss++DatatypeSimps.expand_type_quants_ss[``:bir_bin_exp_t``]) [
    bir_bin_exp_GET_BOOL_OPER_def]
    bir_is_lifted_imm_exp_bool2b_BinExp0;




val bir_is_lifted_imm_exp_bool2b_BinPred0 = prove (
``!uo bop env e1 e2 b1 b2.
      (bir_bin_pred_GET_BOOL_OPER uo = SOME (T, bop)) ==>
      bir_is_lifted_imm_exp env e1 (bool2b b1) ==>
      bir_is_lifted_imm_exp env e2 (bool2b b2) ==>
      bir_is_lifted_imm_exp env (BExp_BinPred uo e1 e2) (bool2b (bop b1 b2))``,

REPEAT STRIP_TAC >>
`bir_bin_pred uo (bool2b b1) (bool2b b2) = bop b1 b2` by METIS_TAC[
  bir_bin_pred_GET_BOOL_OPER_THM] >>
FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_is_lifted_imm_exp_def,
  bir_env_oldTheory.bir_env_vars_are_initialised_UNION, BType_Bool_def]);


val bir_is_lifted_imm_exp_bool2b_BinPred =
  SIMP_RULE (std_ss++DatatypeSimps.expand_type_quants_ss[``:bir_bin_pred_t``]) [
    bir_bin_pred_GET_BOOL_OPER_def]
    bir_is_lifted_imm_exp_bool2b_BinPred0;




val bir_is_lifted_imm_exp_bool2b = save_thm ("bir_is_lifted_imm_exp_bool2b",
  LIST_CONJ [bir_is_lifted_imm_exp_bool2b_TF,
             bir_is_lifted_imm_exp_bool2b_UnaryExp,
             bir_is_lifted_imm_exp_bool2b_BinExp,
             bir_is_lifted_imm_exp_bool2b_COND,
             bir_is_lifted_imm_exp_bool2b_BinPred]);




(********)
(* nzcv *)
(********)

val thm_t = let
  val exp_t = ``XXX_exp : bir_immtype_t -> bir_exp_t -> bir_exp_t -> bir_exp_t``
  val val_t = ``XXX_val : 'a word -> 'a word -> bool``

  val thm_t =
  ``!s env (w1:'a word) w2 e1 e2.
        bir_is_lifted_imm_exp env e1 (w2bs w1 s) ==>
        bir_is_lifted_imm_exp env e2 (w2bs w2 s) ==>
        bir_is_lifted_imm_exp env (^exp_t s e1 e2) (bool2b (^val_t w1 w2))``;

  val l = [
     (``(\s:bir_immtype_t. BExp_nzcv_ADD_N s)``, ``nzcv_BIR_ADD_N``),
     (``(\s:bir_immtype_t. BExp_nzcv_ADD_Z)``, ``nzcv_BIR_ADD_Z``),
     (``(\s:bir_immtype_t. BExp_nzcv_ADD_C)``, ``nzcv_BIR_ADD_C``),
     (``(\s:bir_immtype_t. BExp_nzcv_ADD_V s)``, ``nzcv_BIR_ADD_V``),
     (``(\s:bir_immtype_t. BExp_nzcv_SUB_N s)``, ``nzcv_BIR_SUB_N``),
     (``(\s:bir_immtype_t. BExp_nzcv_SUB_Z)``, ``nzcv_BIR_SUB_Z``),
     (``(\s:bir_immtype_t. BExp_nzcv_SUB_C)``, ``nzcv_BIR_SUB_C``),
     (``(\s:bir_immtype_t. BExp_nzcv_SUB_V s)``, ``nzcv_BIR_SUB_V``)
  ];

  val tl = map build_immtype_t_conj (map (fn (te, tv) => (subst [exp_t |-> te, val_t |-> tv] thm_t)) l)


  val exp_t = ``XXX_exp : bir_immtype_t -> bir_exp_t -> bir_exp_t -> bir_exp_t -> bir_exp_t``
  val val_t = ``XXX_val : 'a word -> 'a word -> bool -> bool``

  val thm_t =
  ``!s env (w1:'a word) w2 c e1 e2 ec.
        bir_is_lifted_imm_exp env ec (bool2b c) ==>
        bir_is_lifted_imm_exp env e1 (w2bs w1 s) ==>
        bir_is_lifted_imm_exp env e2 (w2bs w2 s) ==>
        bir_is_lifted_imm_exp env (^exp_t s e1 e2 ec) (bool2b (^val_t w1 w2 c))``;

  val l = [
     (``(\s:bir_immtype_t. BExp_ADD_WITH_CARRY_N s)``, ``awc_BIR_N``),
     (``(\s:bir_immtype_t. BExp_ADD_WITH_CARRY_Z s)``, ``awc_BIR_Z``),
     (``(\s:bir_immtype_t. BExp_ADD_WITH_CARRY_C)``, ``awc_BIR_C``),
     (``(\s:bir_immtype_t. BExp_ADD_WITH_CARRY_V s)``, ``awc_BIR_V``)
  ];

  val tl2 = map build_immtype_t_conj (map (fn (te, tv) => (subst [exp_t |-> te, val_t |-> tv] thm_t)) l)



in  list_mk_conj (tl @ tl2) end;


val bir_is_lifted_imm_exp_NZCV0 = prove (``^thm_t``,
SIMP_TAC (std_ss++holBACore_ss++boolSimps.LIFT_COND_ss) [bir_is_lifted_imm_exp_def,
  bir_env_oldTheory.bir_env_vars_are_initialised_UNION, BType_Bool_def, w2w_id,
  pairTheory.pair_case_thm,
  BExp_nzcv_SUB_type_of, BExp_nzcv_SUB_vars_of,
  BExp_nzcv_ADD_type_of, BExp_nzcv_ADD_vars_of,
  BExp_ADD_WITH_CARRY_type_of, BExp_ADD_WITH_CARRY_vars_of,

  BExp_nzcv_SUB_N_eval, BExp_nzcv_SUB_Z_eval, BExp_nzcv_SUB_C_eval, BExp_nzcv_SUB_V_eval,
  BExp_nzcv_ADD_N_eval, BExp_nzcv_ADD_Z_eval, BExp_nzcv_ADD_C_eval, BExp_nzcv_ADD_V_eval,
  BExp_ADD_WITH_CARRY_N_eval, BExp_ADD_WITH_CARRY_Z_eval,
  BExp_ADD_WITH_CARRY_C_eval, BExp_ADD_WITH_CARRY_V_eval
]);

val bir_is_lifted_imm_exp_NZCV = save_thm ("bir_is_lifted_imm_exp_NZCV",
let
  val thm0 = bir_is_lifted_imm_exp_NZCV0
  val thm1 = SIMP_RULE std_ss [GSYM CONJ_ASSOC, w2bs_REWRS, IMP_CONJ_THM,
    FORALL_AND_THM, w2w_id] thm0
in
  thm1
end);




(************************************)
(* WI_distinct_compute_MEM_UNCHANGED *)
(************************************)

val thm_t = let
  val thm_t =
  ``!sz env (wb:'a word) wb_e mb_n me_n wb_e isz.
        bir_is_lifted_imm_exp env wb_e (w2bs wb sz) ==>
        bir_is_lifted_imm_exp env (BExp_unchanged_mem_interval_distinct sz mb_n me_n wb_e isz)
               (bool2b (WI_distinct_MEM_UNCHANGED_COMPUTE (n2w mb_n) (n2w me_n) wb isz))``;

  val tl = build_immtype_t_conj thm_t

in tl end;

val bir_is_lifted_imm_exp_WI_distinct_MEM_UNCHANGED_COMPUTE0 = prove (``^thm_t``,
SIMP_TAC (std_ss++holBACore_ss++boolSimps.LIFT_COND_ss) [bir_is_lifted_imm_exp_def,
  bir_env_oldTheory.bir_env_vars_are_initialised_UNION, BType_Bool_def, w2w_id,
  pairTheory.pair_case_thm,

  BExp_unchanged_mem_interval_distinct_type_of,
  BExp_unchanged_mem_interval_distinct_vars_of,
  BExp_unchanged_mem_interval_distinct_eval
]);

val bir_is_lifted_imm_exp_WI_distinct_MEM_UNCHANGED_COMPUTE = save_thm ("bir_is_lifted_imm_exp_WI_distinct_MEM_UNCHANGED_COMPUTE",
let
  val thm0 = bir_is_lifted_imm_exp_WI_distinct_MEM_UNCHANGED_COMPUTE0
  val thm1 = SIMP_RULE std_ss [GSYM CONJ_ASSOC, w2bs_REWRS, IMP_CONJ_THM,
    FORALL_AND_THM, w2w_id] thm0
in
  thm1
end);



(************)
(* word_msb *)
(************)

val thm_t = build_immtype_t_conj
``!s env (w:'a word) e.
      bir_is_lifted_imm_exp env e (w2bs w s) ==>
      bir_is_lifted_imm_exp env (BExp_MSB s e)
             (bool2b (word_msb w))``;

val bir_is_lifted_imm_exp_MSB0 = prove (``^thm_t``,
SIMP_TAC (std_ss++holBACore_ss++boolSimps.LIFT_COND_ss) [bir_is_lifted_imm_exp_def,
  BExp_MSB_vars_of, BExp_MSB_type_of, BType_Bool_def, BExp_MSB_eval,
  pairTheory.pair_case_thm, w2w_id]);


val bir_is_lifted_imm_exp_MSB = save_thm ("bir_is_lifted_imm_exp_MSB",
let
  val thm0 = bir_is_lifted_imm_exp_MSB0
  val thm1 = SIMP_RULE std_ss [GSYM CONJ_ASSOC, w2bs_REWRS, w2w_id] thm0
in
  CONJ thm1 (SIMP_RULE (std_ss++wordsLib.SIZES_ss) [word_msb] thm1)
end);


(************)
(* word_lsb *)
(************)

val thm_t = build_immtype_t_conj
``!s env (w:'a word) e.
      bir_is_lifted_imm_exp env e (w2bs w s) ==>
      bir_is_lifted_imm_exp env (BExp_LSB e)
             (bool2b (word_lsb w))``;

val bir_is_lifted_imm_exp_LSB0 = prove (``^thm_t``,
SIMP_TAC (std_ss++holBACore_ss++boolSimps.LIFT_COND_ss) [bir_is_lifted_imm_exp_def,
   BExp_LSB_vars_of, BExp_LSB_type_of, BExp_LSB_eval, w2w_id, BType_Bool_def]);

val bir_is_lifted_imm_exp_LSB = save_thm ("bir_is_lifted_imm_exp_LSB",
let
  val thm0 = bir_is_lifted_imm_exp_LSB0
  val thm1 = SIMP_RULE std_ss [GSYM CONJ_ASSOC, w2bs_REWRS, w2w_id] thm0

in
  CONJ thm1 (REWRITE_RULE [word_lsb] thm1)
end);


(************)
(* word_bit *)
(************)

val thm_t = build_immtype_t_conj
``!s env (w:'a word) n e.
      (MEM n (COUNT_LIST (dimindex (:'a) - 1))) ==> (0 < n) ==>
      bir_is_lifted_imm_exp env e (w2bs w s) ==>
      bir_is_lifted_imm_exp env (BExp_word_bit s e n) (bool2b (word_bit n w))``;

val bir_is_lifted_imm_exp_word_bit0 = prove (``^thm_t``,
SIMP_TAC (std_ss++holBACore_ss++boolSimps.LIFT_COND_ss) [bir_is_lifted_imm_exp_def,
  BExp_word_bit_vars_of, BExp_word_bit_type_of, BExp_word_bit_eval, pairTheory.pair_case_thm,
  w2w_id, BType_Bool_def]);


val bir_is_lifted_imm_exp_word_bit_const = save_thm ("bir_is_lifted_imm_exp_word_bit_const",
let
  val thm0 = bir_is_lifted_imm_exp_word_bit0
  val thm1 = SIMP_RULE (std_ss++wordsLib.SIZES_ss) [GSYM CONJ_ASSOC, w2bs_REWRS, IMP_CONJ_THM,
    FORALL_AND_THM, w2w_id, n2bs_def] thm0

  val thm2 = SIMP_RULE std_ss [rich_listTheory.COUNT_LIST_compute,
    rich_listTheory.COUNT_LIST_AUX_compute, DISJ_IMP_THM, listTheory.MEM,
    FORALL_AND_THM] thm1
in
  thm2
end);


val word_bit_mod_remove = prove (
``!(w:'a word) (nw:'b word).
    (dimindex (:'b) <= dimindex (:'a)) ==>
    (word_bit ((w2n nw) MOD (dimword (:'a))) w =
     word_bit (w2n nw) w)``,

REPEAT STRIP_TAC >>
`w2n nw < dimword (:'a)` suffices_by ASM_SIMP_TAC arith_ss [] >>
`dimword (:'b) <= dimword (:'a)` by METIS_TAC[wordsTheory.dimindex_dimword_le_iso] >>
`w2n nw < dimword (:'b)` by METIS_TAC[w2n_lt] >>
DECIDE_TAC);


val thm_t = build_immtype_t_conj
``!s env (w:'a word) (nw:'b word) e en.
      (dimindex (:'b) <= dimindex (:'a)) ==>
      bir_is_lifted_imm_exp env e (w2bs w s) ==>
      bir_is_lifted_imm_exp env en (w2bs nw s) ==>
      bir_is_lifted_imm_exp env (BExp_word_bit_exp s e en)
             (bool2b (word_bit (w2n nw) w))``;

val bir_is_lifted_imm_exp_word_bit0 = prove (``^thm_t``,
SIMP_TAC (std_ss++holBACore_ss++boolSimps.LIFT_COND_ss) [bir_is_lifted_imm_exp_def,
  BExp_word_bit_exp_type_of, BExp_word_bit_exp_vars_of, BExp_word_bit_exp_eval,
  pairTheory.pair_case_thm, bir_env_oldTheory.bir_env_vars_are_initialised_UNION, w2w_id, BType_Bool_def] >>
SIMP_TAC std_ss [w2w_def, w2n_n2w, word_bit_mod_remove]);


val bir_is_lifted_imm_exp_word_bit_exp = save_thm ("bir_is_lifted_imm_exp_word_bit_exp",
let
  val thm0 = bir_is_lifted_imm_exp_word_bit0
  val thm1 = SIMP_RULE (std_ss++wordsLib.SIZES_ss) [GSYM CONJ_ASSOC, w2bs_REWRS, IMP_CONJ_THM,
    FORALL_AND_THM, w2w_id, n2bs_def] thm0

  val words_sizes = List.map (fn sz => fcpLib.index_type (Arbnum.fromInt sz))
          bir_immSyntax.known_imm_sizes;

  val thm2 = LIST_CONJ (List.map (fn sz => INST_TYPE [``:'b`` |-> sz] thm1) words_sizes)

  val thm3 = SIMP_RULE (std_ss++wordsLib.SIZES_ss) [w2w_id, GSYM CONJ_ASSOC] thm2
in
  thm3
end);



(***********)
(* aligned *)
(***********)

val bir_is_lifted_imm_exp_ALIGNED0 = prove (
``!env (w:'a word).
      bir_is_lifted_exp env bir_exp_true (BLV_Imm (bool2b (aligned 0 w)))``,

SIMP_TAC std_ss [alignmentTheory.aligned_0, bir_is_lifted_exp_def,
  bir_is_lifted_imm_exp_bool2b_TF]);


val thm_t = build_immtype_t_conj
``!s env (w:'a word) e.
      p < dimindex (:'a) ==>
      bir_is_lifted_imm_exp env e (w2bs w s) ==>
      bir_is_lifted_imm_exp env (BExp_Aligned s p e)
        (bool2b (aligned p w))``;

val bir_is_lifted_imm_exp_ALIGNED_GEN = prove (``!p. ^thm_t``,
SIMP_TAC (std_ss++holBACore_ss) [bir_is_lifted_imm_exp_def,
  bir_env_oldTheory.bir_env_vars_are_initialised_UNION, pairTheory.pair_case_thm,
  BExp_Aligned_vars_of, BExp_Aligned_eval,
  BExp_Aligned_type_of, BType_Bool_def, w2w_id]);


val bir_is_lifted_imm_exp_ALIGNED = save_thm ("bir_is_lifted_imm_exp_ALIGNED",
let
  val thms0 = map (fn n => SPEC (numSyntax.mk_numeral (Arbnum.fromInt (n+1))) bir_is_lifted_imm_exp_ALIGNED_GEN)
    (List.tabulate (63, I))
  val thm1 = LIST_CONJ (bir_is_lifted_imm_exp_ALIGNED0::thms0)
  val thm2 = SIMP_RULE (std_ss++wordsLib.SIZES_ss) [w2bs_REWRS, w2w_id, GSYM CONJ_ASSOC] thm1
in
  thm2
end);


(*********)
(* align *)
(*********)

val thm_t = build_immtype_t_conj
``!s env (w:'a word) e p.
      bir_is_lifted_imm_exp env e (w2bs w s) ==>
      bir_is_lifted_imm_exp env (BExp_Align s p e)
        (w2bs (align p w) s)``;

val bir_is_lifted_imm_exp_ALIGN_GEN = prove (``^thm_t``,
SIMP_TAC (std_ss++holBACore_ss) [bir_is_lifted_imm_exp_def,
  bir_env_oldTheory.bir_env_vars_are_initialised_UNION, pairTheory.pair_case_thm,
  BExp_Align_vars_of, BExp_Align_eval,
  BExp_Align_type_of, w2w_id]);


val bir_is_lifted_imm_exp_ALIGN = save_thm ("bir_is_lifted_imm_exp_ALIGN",
let
  val thm0 = bir_is_lifted_imm_exp_ALIGN_GEN
  val thm1 = SIMP_RULE std_ss [w2bs_REWRS, w2w_id, GSYM CONJ_ASSOC] thm0
in
  thm1
end);


(******************)
(* reverse endian *)
(******************)

val bir_is_lifted_imm_exp_WORD_REVERSE_8_16 = store_thm ("bir_is_lifted_imm_exp_WORD_REVERSE_8_16",
``!env w e.
      bir_is_lifted_imm_exp env e (Imm16 w) ==>
      bir_is_lifted_imm_exp env (BExp_word_reverse_8_16 e)
        (Imm16 (word_reverse_8_16 w))``,

SIMP_TAC (std_ss++holBACore_ss) [bir_is_lifted_imm_exp_def,
  BExp_word_reverse_8_16_eval,
  BExp_word_reverse_8_16_type_of,
  BExp_word_reverse_8_16_vars_of]);


val bir_is_lifted_imm_exp_WORD_REVERSE_8_32 = store_thm ("bir_is_lifted_imm_exp_WORD_REVERSE_8_32",
``!env w e.
      bir_is_lifted_imm_exp env e (Imm32 w) ==>
      bir_is_lifted_imm_exp env (BExp_word_reverse_8_32 e)
        (Imm32 (word_reverse_8_32 w))``,

SIMP_TAC (std_ss++holBACore_ss) [bir_is_lifted_imm_exp_def,
  BExp_word_reverse_8_32_eval,
  BExp_word_reverse_8_32_type_of,
  BExp_word_reverse_8_32_vars_of]);


val bir_is_lifted_imm_exp_WORD_REVERSE_8_64 = store_thm ("bir_is_lifted_imm_exp_WORD_REVERSE_8_64",
``!env w e.
      bir_is_lifted_imm_exp env e (Imm64 w) ==>
      bir_is_lifted_imm_exp env (BExp_word_reverse_8_64 e)
        (Imm64 (word_reverse_8_64 w))``,

SIMP_TAC (std_ss++holBACore_ss) [bir_is_lifted_imm_exp_def,
  BExp_word_reverse_8_64_eval,
  BExp_word_reverse_8_64_type_of,
  BExp_word_reverse_8_64_vars_of]);


val bir_is_lifted_imm_exp_WORD_REVERSE_16_32 = store_thm ("bir_is_lifted_imm_exp_WORD_REVERSE_16_32",
``!env w e.
      bir_is_lifted_imm_exp env e (Imm32 w) ==>
      bir_is_lifted_imm_exp env (BExp_word_reverse_16_32 e)
        (Imm32 (word_reverse_16_32 w))``,

SIMP_TAC (std_ss++holBACore_ss) [bir_is_lifted_imm_exp_def,
  BExp_word_reverse_16_32_eval,
  BExp_word_reverse_16_32_type_of,
  BExp_word_reverse_16_32_vars_of]);


val bir_is_lifted_imm_exp_WORD_REVERSE_16_64 = store_thm ("bir_is_lifted_imm_exp_WORD_REVERSE_16_64",
``!env w e.
      bir_is_lifted_imm_exp env e (Imm64 w) ==>
      bir_is_lifted_imm_exp env (BExp_word_reverse_16_64 e)
        (Imm64 (word_reverse_16_64 w))``,

SIMP_TAC (std_ss++holBACore_ss) [bir_is_lifted_imm_exp_def,
  BExp_word_reverse_16_64_eval,
  BExp_word_reverse_16_64_type_of,
  BExp_word_reverse_16_64_vars_of]);


val bir_is_lifted_imm_exp_WORD_REVERSE_32_64 = store_thm ("bir_is_lifted_imm_exp_WORD_REVERSE_32_64",
``!env w e.
      bir_is_lifted_imm_exp env e (Imm64 w) ==>
      bir_is_lifted_imm_exp env (BExp_word_reverse_32_64 e)
        (Imm64 (word_reverse_32_64 w))``,

SIMP_TAC (std_ss++holBACore_ss) [bir_is_lifted_imm_exp_def,
  BExp_word_reverse_32_64_eval,
  BExp_word_reverse_32_64_type_of,
  BExp_word_reverse_32_64_vars_of]);



val bir_is_lifted_imm_exp_WORD_REVERSE_1 = store_thm ("bir_is_lifted_imm_exp_WORD_REVERSE_1",
``(!env w e.
      bir_is_lifted_imm_exp env e (Imm8 w) ==>
      bir_is_lifted_imm_exp env (BExp_word_reverse_1_8 e)
        (Imm8 (word_reverse w))) /\
  (!env w e.
      bir_is_lifted_imm_exp env e (Imm16 w) ==>
      bir_is_lifted_imm_exp env (BExp_word_reverse_1_16 e)
        (Imm16 (word_reverse w))) /\
  (!env w e.
      bir_is_lifted_imm_exp env e (Imm32 w) ==>
      bir_is_lifted_imm_exp env (BExp_word_reverse_1_32 e)
        (Imm32 (word_reverse w))) /\
  (!env w e.
      bir_is_lifted_imm_exp env e (Imm64 w) ==>
      bir_is_lifted_imm_exp env (BExp_word_reverse_1_64 e)
        (Imm64 (word_reverse w)))``,

SIMP_TAC (std_ss++holBACore_ss) [bir_is_lifted_imm_exp_def,
  BExp_word_reverse_1_eval,
  BExp_word_reverse_1_type_of,
  BExp_word_reverse_1_vars_of]);


val bir_is_lifted_imm_exp_WORD_REVERSE = save_thm ("bir_is_lifted_imm_exp_WORD_REVERSE",
LIST_CONJ [
  bir_is_lifted_imm_exp_WORD_REVERSE_1,
  bir_is_lifted_imm_exp_WORD_REVERSE_8_16,
  bir_is_lifted_imm_exp_WORD_REVERSE_8_32,
  bir_is_lifted_imm_exp_WORD_REVERSE_8_64,
  bir_is_lifted_imm_exp_WORD_REVERSE_16_32,
  bir_is_lifted_imm_exp_WORD_REVERSE_16_64,
  bir_is_lifted_imm_exp_WORD_REVERSE_32_64])



(****************)
(* Rotate right *)
(****************)

val thm_t = build_immtype_t_conj
``!s env (w1:'a word) (w2 :'a word) e1 e2.

      bir_is_lifted_imm_exp env e1 (w2bs w1 s) ==>
      bir_is_lifted_imm_exp env e2 (w2bs w2 s) ==>
      bir_is_lifted_imm_exp env (BExp_ror_exp s e1 e2)
        (w2bs (w1 #>>~ w2) s)``;

val bir_is_lifted_imm_exp_ROR_EXP0 = prove (``^thm_t``,
SIMP_TAC (std_ss++holBACore_ss) [bir_is_lifted_imm_exp_def,
  bir_env_oldTheory.bir_env_vars_are_initialised_UNION, w2w_id, pairTheory.pair_case_thm,
  BExp_ror_exp_vars_of, BExp_ror_exp_type_of, BExp_ror_exp_eval]);

val bir_is_lifted_imm_exp_ROR_EXP = save_thm ("bir_is_lifted_imm_exp_ROR_EXP",
let
  val thm0 = bir_is_lifted_imm_exp_ROR_EXP0
  val thm1 = SIMP_RULE std_ss [GSYM CONJ_ASSOC, w2bs_REWRS, w2w_id] thm0
in
  thm1
end);


val thm_t = build_immtype_t_conj
``!s env (w1:'a word) (w2 : 'b word) e1 e2.
      (dimword (:'b) <= dimword (:'a)) ==>
      bir_is_lifted_imm_exp env e1 (w2bs w1 s) ==>
      bir_is_lifted_imm_exp env e2 (w2bs w2 s) ==>
      bir_is_lifted_imm_exp env (BExp_ror_exp s e1 e2)
        (w2bs (w1 #>>~ (n2w (w2n w2))) s)``;

val bir_is_lifted_imm_exp_ROR_EXP_w2n0 = prove (``^thm_t``,
SIMP_TAC (std_ss++holBACore_ss) [bir_is_lifted_imm_exp_def, pairTheory.pair_case_thm,
  bir_env_oldTheory.bir_env_vars_are_initialised_UNION, w2w_id, bir_env_oldTheory.bir_env_vars_are_initialised_EMPTY,
  w2w_def, BExp_ror_exp_eval, BExp_ror_exp_type_of, BExp_ror_exp_vars_of]);


val bir_is_lifted_imm_exp_ROR_EXP_w2n = save_thm ("bir_is_lifted_imm_exp_ROR_EXP_w2n",
let
  val aux_thm = prove (``dimword (:'b) <= n ==> (w2n (w:'b word) < n)``,
    REPEAT STRIP_TAC >>
    `w2n w < dimword (:'b)` by METIS_TAC[w2n_lt] >>
    DECIDE_TAC);

  val thm0 = bir_is_lifted_imm_exp_ROR_EXP_w2n0
  val thm1 = SIMP_RULE (list_ss++wordsLib.SIZES_ss) [
    bir_bin_exp_GET_OPER_def, GSYM CONJ_ASSOC, w2bs_REWRS, w2w_id,
    DISJ_IMP_THM, IMP_CONJ_THM, FORALL_AND_THM, n2bs_def,
    word_ror_bv_def, w2n_lt, aux_thm, w2n_n2w]
    thm0


  val words_sizes = List.map (fn sz => fcpLib.index_type (Arbnum.fromInt sz))
          bir_immSyntax.known_imm_sizes;

  val thm2 = LIST_CONJ (List.map (fn sz => INST_TYPE [``:'b`` |-> sz] thm1) words_sizes)

  val thm3 = SIMP_RULE (std_ss++wordsLib.SIZES_ss) [w2w_id, GSYM CONJ_ASSOC] thm2


in
  thm3
end);



val thm_t = build_immtype_t_conj
``!s env (w1:'a word) (n2 : num) e1.
      (MEM n2 (COUNT_LIST (SUC (dimindex (:'a))))) ==>
      bir_is_lifted_imm_exp env e1 (w2bs w1 s) ==>
      bir_is_lifted_imm_exp env (BExp_ror s e1 n2)
        (w2bs (w1 #>> n2) s)``;

val bir_is_lifted_imm_exp_ROR0 = prove (``^thm_t``,
SIMP_TAC (arith_ss++holBACore_ss++wordsLib.SIZES_ss) [bir_is_lifted_imm_exp_def,
  bir_env_oldTheory.bir_env_vars_are_initialised_UNION, w2w_id, bir_env_oldTheory.bir_env_vars_are_initialised_EMPTY,
  BExp_ror_vars_of, BExp_ror_type_of, BExp_ror_eval, rich_listTheory.MEM_COUNT_LIST,
  GSYM arithmeticTheory.LESS_EQ_IFF_LESS_SUC, pairTheory.pair_case_thm]);

val bir_is_lifted_imm_exp_ROR = save_thm ("bir_is_lifted_imm_exp_ROR",
let
  val thm0 = bir_is_lifted_imm_exp_ROR0
  val thm1 = SIMP_RULE (list_ss++wordsLib.WORD_ss) [
    GSYM CONJ_ASSOC, w2bs_REWRS, w2w_id, n2bs_def] thm0
  val thm2 = SIMP_RULE (std_ss) [rich_listTheory.COUNT_LIST_compute,
    rich_listTheory.COUNT_LIST_AUX_compute, DISJ_IMP_THM, listTheory.MEM,
    FORALL_AND_THM] thm1
in
  thm2
end);





(***************)
(* Rotate left *)
(***************)

val thm_t = build_immtype_t_conj
``!s env (w1:'a word) (w2 :'a word) e1 e2.

      bir_is_lifted_imm_exp env e1 (w2bs w1 s) ==>
      bir_is_lifted_imm_exp env e2 (w2bs w2 s) ==>
      bir_is_lifted_imm_exp env (BExp_rol_exp s e1 e2)
        (w2bs (w1 #<<~ w2) s)``;

val bir_is_lifted_imm_exp_ROL_EXP0 = prove (``^thm_t``,
SIMP_TAC (std_ss++holBACore_ss) [bir_is_lifted_imm_exp_def,
  bir_env_oldTheory.bir_env_vars_are_initialised_UNION, w2w_id, pairTheory.pair_case_thm,
  BExp_rol_exp_vars_of, BExp_rol_exp_type_of, BExp_rol_exp_eval]);

val bir_is_lifted_imm_exp_ROL_EXP = save_thm ("bir_is_lifted_imm_exp_ROL_EXP",
let
  val thm0 = bir_is_lifted_imm_exp_ROL_EXP0
  val thm1 = SIMP_RULE std_ss [GSYM CONJ_ASSOC, w2bs_REWRS, w2w_id] thm0
in
  thm1
end);


val thm_t = build_immtype_t_conj
``!s env (w1:'a word) (w2 : 'b word) e1 e2.
      (dimword (:'b) <= dimword (:'a)) ==>
      bir_is_lifted_imm_exp env e1 (w2bs w1 s) ==>
      bir_is_lifted_imm_exp env e2 (w2bs w2 s) ==>
      bir_is_lifted_imm_exp env (BExp_rol_exp s e1 e2)
        (w2bs (w1 #<<~ (n2w (w2n w2))) s)``;

val bir_is_lifted_imm_exp_ROL_EXP_w2n0 = prove (``^thm_t``,
SIMP_TAC (std_ss++holBACore_ss) [bir_is_lifted_imm_exp_def, pairTheory.pair_case_thm,
  bir_env_oldTheory.bir_env_vars_are_initialised_UNION, w2w_id, bir_env_oldTheory.bir_env_vars_are_initialised_EMPTY,
  w2w_def, BExp_rol_exp_eval, BExp_rol_exp_type_of, BExp_rol_exp_vars_of]);


val bir_is_lifted_imm_exp_ROL_EXP_w2n = save_thm ("bir_is_lifted_imm_exp_ROL_EXP_w2n",
let
  val aux_thm = prove (``dimword (:'b) <= n ==> (w2n (w:'b word) < n)``,
    REPEAT STRIP_TAC >>
    `w2n w < dimword (:'b)` by METIS_TAC[w2n_lt] >>
    DECIDE_TAC);

  val thm0 = bir_is_lifted_imm_exp_ROL_EXP_w2n0
  val thm1 = SIMP_RULE (list_ss++wordsLib.SIZES_ss) [
    bir_bin_exp_GET_OPER_def, GSYM CONJ_ASSOC, w2bs_REWRS, w2w_id,
    DISJ_IMP_THM, IMP_CONJ_THM, FORALL_AND_THM, n2bs_def,
    word_rol_bv_def, w2n_lt, aux_thm, w2n_n2w]
    thm0

  val words_sizes = List.map (fn sz => fcpLib.index_type (Arbnum.fromInt sz))
          bir_immSyntax.known_imm_sizes;

  val thm2 = LIST_CONJ (List.map (fn sz => INST_TYPE [``:'b`` |-> sz] thm1) words_sizes)

  val thm3 = SIMP_RULE (std_ss++wordsLib.SIZES_ss) [w2w_id, GSYM CONJ_ASSOC] thm2


in
  thm3
end);



val thm_t = build_immtype_t_conj
``!s env (w1:'a word) (n2 : num) e1.
      (MEM n2 (COUNT_LIST (SUC (dimindex (:'a))))) ==>
      bir_is_lifted_imm_exp env e1 (w2bs w1 s) ==>
      bir_is_lifted_imm_exp env (BExp_rol s e1 n2)
        (w2bs (w1 #<< n2) s)``;

val bir_is_lifted_imm_exp_ROL0 = prove (``^thm_t``,
SIMP_TAC (arith_ss++holBACore_ss++wordsLib.SIZES_ss) [bir_is_lifted_imm_exp_def,
  bir_env_oldTheory.bir_env_vars_are_initialised_UNION, w2w_id, bir_env_oldTheory.bir_env_vars_are_initialised_EMPTY,
  BExp_rol_vars_of, BExp_rol_type_of, BExp_rol_eval, rich_listTheory.MEM_COUNT_LIST,
  GSYM arithmeticTheory.LESS_EQ_IFF_LESS_SUC, pairTheory.pair_case_thm]);

val bir_is_lifted_imm_exp_ROL = save_thm ("bir_is_lifted_imm_exp_ROL",
let
  val thm0 = bir_is_lifted_imm_exp_ROL0
  val thm1 = SIMP_RULE (list_ss++wordsLib.WORD_ss) [
    GSYM CONJ_ASSOC, w2bs_REWRS, w2w_id, n2bs_def] thm0
  val thm2 = SIMP_RULE (std_ss) [rich_listTheory.COUNT_LIST_compute,
    rich_listTheory.COUNT_LIST_AUX_compute, DISJ_IMP_THM, listTheory.MEM,
    FORALL_AND_THM] thm1
in
  thm2
end);



(********)
(* extr *)
(********)

val thm_t = build_immtype_t_conj
``!s env (w1:'a word) (w2 : 'a word) (n : num) e1 e2.
      (MEM n (COUNT_LIST (SUC (dimindex (:'a))))) ==>
      bir_is_lifted_imm_exp env e1 (w2bs w1 s) ==>
      bir_is_lifted_imm_exp env e2 (w2bs w2 s) ==>
      bir_is_lifted_imm_exp env (BExp_extr s e1 e2 n)
        (w2bs (word_shift_extract w1 w2 n) s)``;

val bir_is_lifted_imm_exp_EXTR0 = prove (``^thm_t``,
SIMP_TAC (arith_ss++holBACore_ss++wordsLib.SIZES_ss) [bir_is_lifted_imm_exp_def,
  bir_env_oldTheory.bir_env_vars_are_initialised_UNION, w2w_id, bir_env_oldTheory.bir_env_vars_are_initialised_EMPTY,
  BExp_extr_vars_of, BExp_extr_type_of, BExp_extr_eval, rich_listTheory.MEM_COUNT_LIST,
  GSYM arithmeticTheory.LESS_EQ_IFF_LESS_SUC, pairTheory.pair_case_thm]);

val bir_is_lifted_imm_exp_EXTR = save_thm ("bir_is_lifted_imm_exp_EXTR",
let
  val thm0 = bir_is_lifted_imm_exp_EXTR0
  val thm1 = SIMP_RULE (list_ss++wordsLib.WORD_ss) [
    GSYM CONJ_ASSOC, w2bs_REWRS, w2w_id, n2bs_def] thm0
  val thm2 = SIMP_RULE (std_ss) [rich_listTheory.COUNT_LIST_compute,
    rich_listTheory.COUNT_LIST_AUX_compute, DISJ_IMP_THM, listTheory.MEM,
    FORALL_AND_THM] thm1
in
  thm2
end);





(****************)
(* Combination  *)
(****************)

val bir_is_lifted_imm_exp_DEFAULT_THMS = save_thm ("bir_is_lifted_imm_exp_DEFAULT_THMS",
  LIST_CONJ [bir_is_lifted_imm_exp_UNARY_EXP,
             bir_is_lifted_imm_exp_BIN_EXP,
             bir_is_lifted_imm_exp_SHIFTS_n2w,
             bir_is_lifted_imm_exp_SHIFTS_w2n,
             bir_is_lifted_imm_exp_BIN_PRED,
             bir_is_lifted_imm_exp_bool2b,
             bir_is_lifted_imm_exp_bool2w,
             bir_is_lifted_imm_exp_CASTS,
             bir_is_lifted_imm_exp_COND,
             bir_is_lifted_imm_exp_PROTECTED_COND,
             bir_is_lifted_imm_exp_LOAD_ENDIAN,
             bir_is_lifted_mem_exp_STORE_ENDIAN,
             bir_is_lifted_imm_exp_NZCV,
             bir_is_lifted_imm_exp_WI_distinct_MEM_UNCHANGED_COMPUTE,
             bir_is_lifted_imm_exp_MSB,
             bir_is_lifted_imm_exp_LSB,
             bir_is_lifted_imm_exp_word_bit_const,
             bir_is_lifted_imm_exp_word_bit_exp,
             bir_is_lifted_imm_exp_WORD_REVERSE,
             bir_is_lifted_imm_exp_ROR_EXP,
             bir_is_lifted_imm_exp_ROR_EXP_w2n,
             bir_is_lifted_imm_exp_ROR,
             bir_is_lifted_imm_exp_ROL_EXP,
             bir_is_lifted_imm_exp_ROL_EXP_w2n,
             bir_is_lifted_imm_exp_ROL,
             bir_is_lifted_imm_exp_EXTR,
             bir_is_lifted_imm_exp_ALIGN,
             bir_is_lifted_imm_exp_ALIGNED]);


val _ = export_theory();
