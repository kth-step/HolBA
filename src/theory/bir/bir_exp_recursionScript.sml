open HolKernel Parse boolLib bossLib;
open bir_expTheory;

val _ = new_theory "bir_exp_recursion";

val _ = Datatype `bir_exp_algebra_t =
  <| bexp_const : bir_imm_t -> 'carrier_t;
     bexp_memconst : bir_immtype_t -> bir_immtype_t -> (num |-> num) -> 'carrier_t;
     bexp_den : bir_var_t -> 'carrier_t;
     bexp_cast : bir_cast_t -> 'carrier_t -> bir_immtype_t -> 'carrier_t;
     bexp_unaryexp : bir_unary_exp_t -> 'carrier_t -> 'carrier_t;
     bexp_binexp : bir_bin_exp_t -> 'carrier_t -> 'carrier_t -> 'carrier_t;
     bexp_binpred : bir_bin_pred_t -> 'carrier_t -> 'carrier_t -> 'carrier_t;
     bexp_memeq : 'carrier_t -> 'carrier_t -> 'carrier_t;
     bexp_ifthenelse : 'carrier_t -> 'carrier_t -> 'carrier_t -> 'carrier_t;
     bexp_load : 'carrier_t -> 'carrier_t -> bir_endian_t -> bir_immtype_t -> 'carrier_t;
     bexp_store : 'carrier_t -> 'carrier_t -> bir_endian_t -> 'carrier_t -> 'carrier_t
  |>
`;

val bir_exp_initial_alg_def = Define`
  bir_exp_initial_alg = <|
    bexp_const := BExp_Const;
    bexp_memconst := BExp_MemConst;
    bexp_den := BExp_Den;
    bexp_cast := BExp_Cast;
    bexp_unaryexp := BExp_UnaryExp;
    bexp_binexp := BExp_BinExp;
    bexp_binpred := BExp_BinPred;
    bexp_memeq := BExp_MemEq;
    bexp_ifthenelse := BExp_IfThenElse;
    bexp_load := BExp_Load;
    bexp_store := BExp_Store |>`;

val bir_exp_constant_alg_def = Define`
 bir_exp_constant_alg k = <|
  bexp_const := \x.k;
  bexp_memconst := \a b c.k;
  bexp_den := \x.k;
  bexp_cast := \a b c.k;
  bexp_unaryexp := \a b.k;
  bexp_binexp := \a b c.k;
  bexp_binpred := \a b c.k;
  bexp_memeq := \a b.k;
  bexp_ifthenelse := \a b c.k;
  bexp_load := \a b c d.k;
  bexp_store := \a b c d.k; |>`;

val bir_exp_homo_bin_alg_def = Define`
  bir_exp_homo_bin_alg f = <|
    bexp_cast := \a b c. b;
    bexp_unaryexp := \a b.b;
    bexp_binexp := \a b c. f b c;
    bexp_binpred := \a b c. f b c;
    bexp_memeq := \a b. f a b;
    bexp_ifthenelse := \a b c. f a (f b c);
    bexp_load := \a b _ _. f a b;
    bexp_store := \a b _ c. f a (f b c)
    |>
`;

val bir_fold_exp_def = Define`
  bir_fold_exp (alg: 'a bir_exp_algebra_t) exp =
   case exp of
      BExp_Const imm => alg.bexp_const imm
    | BExp_MemConst addr_ty val_ty mapping => alg.bexp_memconst addr_ty val_ty mapping
    | BExp_Den var => alg.bexp_den var
    | BExp_Cast cast_kind cast_exp type =>
       alg.bexp_cast cast_kind (bir_fold_exp alg cast_exp) type
    | BExp_UnaryExp uexp_kind exp1 => alg.bexp_unaryexp uexp_kind (bir_fold_exp alg exp1)
    | BExp_BinExp binexp_kind exp1 exp2 =>
       alg.bexp_binexp binexp_kind (bir_fold_exp alg exp1) (bir_fold_exp alg exp2)
    | BExp_BinPred binpred_kind exp1 exp2 =>
       alg.bexp_binpred binpred_kind (bir_fold_exp alg exp1) (bir_fold_exp alg exp2)
    | BExp_MemEq exp1 exp2 => alg.bexp_memeq (bir_fold_exp alg exp1) (bir_fold_exp alg exp2)
    | BExp_IfThenElse exp1 exp2 exp3 =>
      alg.bexp_ifthenelse (bir_fold_exp alg exp1) (bir_fold_exp alg exp2) (bir_fold_exp alg exp3)
    | BExp_Load exp1 exp2 endianness type =>
      alg.bexp_load (bir_fold_exp alg exp1) (bir_fold_exp alg exp2) endianness type
    | BExp_Store exp1 exp2 endianness exp3 =>
      alg.bexp_store (bir_fold_exp alg exp1) (bir_fold_exp alg exp2) endianness (bir_fold_exp alg exp3)
`;

val bir_map_vars_exp_def = Define`
  bir_map_vars_exp (vmap:bir_var_t -> bir_var_t) =
    bir_fold_exp (bir_exp_initial_alg
                  with <| bexp_den := \v. BExp_Den (vmap v) |>)
`;

val bir_bind_exp_def = Define`
  bir_bind_exp f = bir_fold_exp
   (bir_exp_initial_alg
     with <| bexp_den := f |>)
`;

val bir_varset_of_exp_def = Define`
   bir_varset_of_exp = bir_fold_exp
                       (bir_exp_homo_bin_alg (\a b. a UNION b)
                         with <| bexp_den := \v.{v};
                                 bexp_const := \_.{};
                                 bexp_memconst := \_ _ _.{} |>
                               )`;

(* val test_exp1 = ``(BExp_BinExp BIExp_Plus (BExp_Den (BVar "A" (BType_Imm Bit64))) *)
(*                   (BExp_Den (BVar "B" (BType_Imm Bit64))))``; *)
(* val test_exp2 = ``BExp_Const (Imm64 1w)``; *)
(* val test_varset = (rhs o concl) (EVAL ``bir_varset_of_exp ^test_exp1``); *)
(* val test_mapvar = (rhs o concl) (EVAL ``bir_map_vars_exp *)
(*   (\ var. case var of BVar name ty => BVar (name++"'") ty) ^test_exp1``); *)
(* val test_subst = (rhs o concl) (EVAL ``bir_bind_exp (\v. if bir_var_name v = "A" then ^test_exp2 else BExp_Den v) ^test_exp1``); *)

val _ = export_theory ();
