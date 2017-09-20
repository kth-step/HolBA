open HolKernel Parse boolLib bossLib;
open bir_expTheory HolBACoreSimps;
open bir_typing_expTheory bir_valuesTheory
open bir_envTheory bir_immTheory bir_imm_expTheory
open bir_immSyntax wordsTheory
open bir_mem_expTheory bir_bool_expTheory
open bir_nzcv_expTheory

val _ = new_theory "bir_exp_lifting";

(*********************************)
(* Predicates describing lifting *)
(*********************************)


val bir_is_lifted_mem_exp_def = Define `bir_is_lifted_mem_exp
  (env:bir_var_environment_t) (e : bir_exp_t) (mem : 'a word -> 'b word) <=>
  (?sa sb mem_n.
     (size_of_bir_immtype sa = (dimindex (:'a))) /\
     (size_of_bir_immtype sb = (dimindex (:'b))) /\
     (type_of_bir_exp e = SOME (BType_Mem sa sb)) /\
     (bir_env_vars_are_initialised env (bir_vars_of_exp e)) /\
     (bir_eval_exp e env = BVal_Mem sa sb mem_n) /\
     (mem = (\a. n2w (mem_n (w2n a)))))
`;

val bir_is_lifted_imm_exp_def = Define `bir_is_lifted_imm_exp env e i =
  (type_of_bir_exp e = SOME (BType_Imm (type_of_bir_imm i))) /\
  (bir_env_vars_are_initialised env (bir_vars_of_exp e)) /\
  (bir_eval_exp e env = BVal_Imm i)`;


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
  bir_vars_of_exp_def, bir_env_vars_are_initialised_EMPTY, bir_eval_exp_def]);


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
  bir_env_vars_are_initialised_UNION, w2w_id]);


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
  bir_env_vars_are_initialised_UNION, w2w_id]);

val bir_is_lifted_imm_exp_BIN_EXP = save_thm ("bir_is_lifted_imm_exp_BIN_EXP",
let
  val thm0 = bir_is_lifted_imm_exp_BIN_EXP0
  val thm1 = SIMP_RULE (std_ss++DatatypeSimps.expand_type_quants_ss [``:bir_bin_exp_t``]) [
    bir_bin_exp_GET_OPER_def, GSYM CONJ_ASSOC, w2bs_REWRS, w2w_id] thm0
in
  thm1
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
  bir_env_vars_are_initialised_UNION, BType_Bool_def, w2w_id]);


val bir_is_lifted_imm_exp_BIN_PRED = save_thm ("bir_is_lifted_imm_exp_BIN_PRED",
let
  val thm0 = bir_is_lifted_imm_exp_BIN_PRED0
  val thm1 = SIMP_RULE (std_ss++DatatypeSimps.expand_type_quants_ss [``:bir_bin_pred_t``]) [
    bir_bin_pred_GET_OPER_def, GSYM CONJ_ASSOC, w2bs_REWRS, w2w_id] thm0
in
  thm1
end);



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
  bir_env_vars_are_initialised_UNION, bir_auxiliaryTheory.sw2sw_w2w_downcast,
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
  bir_env_vars_are_initialised_UNION, w2w_id]);

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
  bir_env_vars_are_initialised_UNION, w2w_id, w2wh_w2w]);

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
  bir_env_vars_are_initialised_UNION, w2w_id]);

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
  bir_env_vars_are_initialised_UNION, BType_Bool_def, w2w_id]);

val bir_is_lifted_imm_exp_COND = save_thm ("bir_is_lifted_imm_exp_COND",
let
  val thm0 = bir_is_lifted_imm_exp_COND0
  val thm1 = SIMP_RULE std_ss [GSYM CONJ_ASSOC, w2bs_REWRS, IMP_CONJ_THM,
    FORALL_AND_THM, w2w_id] thm0
in
  thm1
end);


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
    (bir_load_from_mem sv sr sa (\n. w2n (mem_f (n2w n))) en (w2n va) = SOME r) ==>

    (bir_is_lifted_imm_exp env (BExp_Load em ea en sr) r))``,

SIMP_TAC (std_ss++holBACore_ss++wordsLib.WORD_ss) [bir_is_lifted_imm_exp_def,
  bir_is_lifted_mem_exp_def, PULL_EXISTS,
  bir_eval_load_BASIC_REWR, bir_env_vars_are_initialised_UNION] >>
REPEAT (GEN_TAC ORELSE DISCH_TAC) >>
`sa' = sa` by METIS_TAC[size_of_bir_immtype_INJ] >>
`sb = sv` by METIS_TAC[size_of_bir_immtype_INJ] >>
FULL_SIMP_TAC std_ss [] >>
REPEAT STRIP_TAC >- (
  METIS_TAC[bir_mem_expTheory.type_of_bir_load_from_mem]
) >- (
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_load_from_mem_EQ_SOME] >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) []
) >>

`bir_load_from_mem sv sr sa mem_n en
        (b2n (w2bs va sa)) =
 bir_load_from_mem sv sr sa (\n. w2n (mem_f (n2w n))) en (w2n va)` suffices_by (STRIP_TAC >> FULL_SIMP_TAC std_ss []) >>

Q.PAT_X_ASSUM `bir_load_from_mem _ _ _ _ _ _ = SOME _` (K ALL_TAC) >>

ASM_SIMP_TAC std_ss [bir_load_from_mem_def, GSYM bitstringTheory.w2v_v2w, bitstringTheory.v2w_n2v,
  bir_load_bitstring_from_mmap_def,
  w2bs_def, b2n_n2bs, n2w_w2n, bir_auxiliaryTheory.w2n_MOD_2EXP_ID] >>
ASM_SIMP_TAC arith_ss [w2n_n2w, bir_mem_addr_def, GSYM wordsTheory.MOD_2EXP_DIMINDEX,
  wordsTheory.ZERO_LT_dimword]);


fun bir_is_lifted_imm_exp_LOAD_gen gt =
let
  val thms0 = MP_size_of_bir_immtype_t_EQ_dimindex (SPEC gt bir_is_lifted_imm_exp_LOAD0)
  val thms1 = flatten (map MP_size_of_bir_immtype_t_EQ_dimindex thms0)
  val thms2 = flatten (map MP_size_of_bir_immtype_t_EQ_dimindex thms1)

  val thm1 = LIST_CONJ thms2
  val thm2 = SIMP_RULE (std_ss++holBACore_ss++(DatatypeSimps.expand_type_quants_ss [``:bir_endian_t``])) [
     bir_load_from_mem_REWRS, n2w_w2n, w2bs_REWRS, w2w_id, bir_mem_addr_w2n_SIZES, bir_mem_addr_w2n_add_SIZES, GSYM CONJ_ASSOC, FORALL_AND_THM] thm1
in
  thm2
end;

(* Build the theorem for sensible values *)
val bir_is_lifted_imm_exp_LOAD_ENDIAN = save_thm ("bir_is_lifted_imm_exp_LOAD_ENDIAN",
  bir_is_lifted_imm_exp_LOAD_gen ``\(sa:bir_immtype_t) (sv:bir_immtype_t) (sr:bir_immtype_t) (en:bir_endian_t). (sv <> sr) /\ (sa <> Bit1) /\ (sv <> Bit1)``);

val bir_is_lifted_imm_exp_LOAD_ENDIAN_BYTE = save_thm ("bir_is_lifted_imm_exp_LOAD_ENDIAN_BYTE",
  bir_is_lifted_imm_exp_LOAD_gen ``\(sa:bir_immtype_t) (sv:bir_immtype_t) (sr:bir_immtype_t) (en:bir_endian_t). (sa <> Bit1) /\ (sv <> sr) /\ (sv = Bit8)``);


fun mk_bir_is_lifted_imm_exp_LOAD addr_size value_size result_size endian =
  bir_is_lifted_imm_exp_LOAD_gen ``\(sa:bir_immtype_t) (sv:bir_immtype_t) (sr:bir_immtype_t) (en:bir_endian_t). (sa = ^addr_size) /\ (sv = ^value_size) /\ (sr = ^result_size) /\ (en = ^endian)``;


val bir_is_lifted_imm_exp_LOAD_ARM_M0 = save_thm ("bir_is_lifted_imm_exp_LOAD_ARM_M0",
  mk_bir_is_lifted_imm_exp_LOAD Bit32_tm Bit8_tm Bit32_tm bir_mem_expSyntax.BEnd_BigEndian_tm)


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
  bir_exp_true_def, bir_exp_false_def, bir_env_vars_are_initialised_EMPTY]);


val bir_is_lifted_imm_exp_bool2b_COND = prove (
``!env c b1 b2 ec e1 e2.
      bir_is_lifted_imm_exp env ec (bool2b c) ==>
      bir_is_lifted_imm_exp env e1 (bool2b b1) ==>
      bir_is_lifted_imm_exp env e2 (bool2b b2) ==>
      bir_is_lifted_imm_exp env (BExp_IfThenElse ec e1 e2) (bool2b (if c then b1 else b2))``,

SIMP_TAC (std_ss++holBACore_ss++boolSimps.LIFT_COND_ss) [bir_is_lifted_imm_exp_def,
  bir_env_vars_are_initialised_UNION, BType_Bool_def]);


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
  bir_env_vars_are_initialised_UNION]);


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
  bir_env_vars_are_initialised_UNION, BType_Bool_def]);


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

in  list_mk_conj tl end;

val bir_is_lifted_imm_exp_NZCV0 = prove (``^thm_t``,
SIMP_TAC (std_ss++holBACore_ss++boolSimps.LIFT_COND_ss) [bir_is_lifted_imm_exp_def,
  bir_env_vars_are_initialised_UNION, BType_Bool_def, w2w_id,
  pairTheory.pair_case_thm,
  BExp_nzcv_SUB_type_of, BExp_nzcv_SUB_vars_of,
  BExp_nzcv_ADD_type_of, BExp_nzcv_ADD_vars_of,

  BExp_nzcv_SUB_N_eval, BExp_nzcv_SUB_Z_eval, BExp_nzcv_SUB_C_eval, BExp_nzcv_SUB_V_eval,
  BExp_nzcv_ADD_N_eval, BExp_nzcv_ADD_Z_eval, BExp_nzcv_ADD_C_eval, BExp_nzcv_ADD_V_eval
]);

val bir_is_lifted_imm_exp_NZCV = save_thm ("bir_is_lifted_imm_exp_NZCV",
let
  val thm0 = bir_is_lifted_imm_exp_NZCV0
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
      bir_is_lifted_imm_exp env (BExp_BinPred BIExp_SignedLessThan e (BExp_Const (n2bs 0 s)))
             (bool2b (word_msb w))``;

val bir_is_lifted_imm_exp_MSB0 = prove (``^thm_t``,
SIMP_TAC (std_ss++holBACore_ss++boolSimps.LIFT_COND_ss) [bir_is_lifted_imm_exp_def,
  pred_setTheory.UNION_EMPTY, BType_Bool_def, w2w_id,
  wordsTheory.word_msb_neg]);

val bir_is_lifted_imm_exp_MSB = save_thm ("bir_is_lifted_imm_exp_MSB",
let
  val thm0 = bir_is_lifted_imm_exp_MSB0
  val thm1 = SIMP_RULE std_ss [GSYM CONJ_ASSOC, w2bs_REWRS, IMP_CONJ_THM,
    FORALL_AND_THM, w2w_id, n2bs_def] thm0
in
  thm1
end);


(***********)
(* aligned *)
(***********)

val bir_is_lifted_imm_exp_ALIGNED0 = prove (
``!env (w:'a word).
      bir_is_lifted_exp env bir_exp_true (BLV_Imm (bool2b (aligned 0 w)))``,

SIMP_TAC std_ss [alignmentTheory.aligned_0, bir_is_lifted_exp_def,
  bir_is_lifted_imm_exp_bool2b_TF]);


val bir_is_lifted_imm_exp_ALIGNED_GEN = prove (
``!p:num env (w:'a word) e.
      bir_is_lifted_imm_exp env e (bool2b ((w && n2w (2 ** p - 1) = 0w))) ==>
      bir_is_lifted_imm_exp env e (bool2b (aligned p w))``,

SIMP_TAC std_ss [alignmentTheory.aligned_bitwise_and]);

val bir_is_lifted_imm_exp_ALIGNED = save_thm ("bir_is_lifted_imm_exp_ALIGNED",
let
  val thms0 = map (fn n => SPEC (numSyntax.mk_numeral (Arbnum.fromInt (n+1))) bir_is_lifted_imm_exp_ALIGNED_GEN)
    (List.tabulate (63, I))
  val thm1 = LIST_CONJ (bir_is_lifted_imm_exp_ALIGNED0::thms0)
  val thm2 = SIMP_RULE std_ss [] thm1
in
  thm2
end);


(****************)
(* Combination  *)
(****************)

val bir_is_lifted_imm_exp_DEFAULT_THMS = save_thm ("bir_is_lifted_imm_exp_DEFAULT_THMS",
  LIST_CONJ [bir_is_lifted_imm_exp_UNARY_EXP,
             bir_is_lifted_imm_exp_BIN_EXP,
             bir_is_lifted_imm_exp_BIN_PRED,
             bir_is_lifted_imm_exp_bool2b,
             bir_is_lifted_imm_exp_CASTS,
             bir_is_lifted_imm_exp_COND,
             bir_is_lifted_imm_exp_LOAD_ENDIAN,
             bir_is_lifted_imm_exp_NZCV,
             bir_is_lifted_imm_exp_MSB,
             bir_is_lifted_imm_exp_ALIGNED]);


val _ = export_theory();
