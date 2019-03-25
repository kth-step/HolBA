structure bir_passificationSyntax :> bir_passificationSyntax =
struct
(* For compilation: *)
open HolKernel boolLib liteLib simpLib Parse bossLib;
(* From BIR core: *)
open bir_programSyntax;
(* From BIR core-props: *)
open bir_extra_expsTheory bir_interval_expTheory;

val ERR = mk_HOL_ERR "bir_translationSyntax"

(* TODO: Move these to relevant syntax libraries... *)
val BExp_Aligned_tm =
  prim_mk_const{Name = "BExp_Aligned",
                Thy  = "bir_extra_exps"}
val dest_BExp_Aligned =
  dest_triop BExp_Aligned_tm (ERR "dest_BExp_Aligned" "")
val is_BExp_Aligned = can dest_BExp_Aligned
fun mk_BExp_Aligned (sz, p, exp) =
  mk_triop BExp_Aligned_tm (sz, p, exp)

val BExp_unchanged_mem_interval_distinct_tm =
  prim_mk_const{Name = "BExp_unchanged_mem_interval_distinct",
                Thy  = "bir_interval_exp"}
fun dest_BExp_unchanged_mem_interval_distinct tm =
  (let
    val (const, args) = strip_comb tm
  in
    if (Term.same_const const
                        BExp_unchanged_mem_interval_distinct_tm)
    then (el 1 args, el 2 args, el 3 args, el 4 args, el 5 args)
    else raise (ERR "dest_BExp_unchanged_mem_interval_distinct" "")
  end) handle e =>
       raise (ERR "dest_BExp_unchanged_mem_interval_distinct" "")
val is_BExp_unchanged_mem_interval_distinct =
  can dest_BExp_unchanged_mem_interval_distinct
fun mk_BExp_unchanged_mem_interval_distinct
      (sz, mb_n, me_n, exp, isz) =
        list_mk_comb (BExp_unchanged_mem_interval_distinct_tm,
                      [sz, mb_n, me_n, exp, isz])

(*
(* More sophisticated constructors and destructors for BStmts? *)
fun dest_BStmt_Assert_alt stmt =
  if is_BStmt_Assert stmt
  then let
         val (const, exp) = dest_comb test_stmt
         val const_ty = (type_of const)
         val {Thy = _, Tyop = _, Args = args} =
           dest_thy_type const_ty
         val obs_ty = dest_bir_stmt_basic_t_ty (el 2 args)
       in
         (obs_ty, exp)
       end
  else raise (ERR "dest_BStmt_Assert_alt" "")

fun mk_BStmt_Assert_alt (obs_ty, exp) =
  let
    val stmt_t_ty = mk_bir_stmt_basic_t_ty obs_ty
    val const_ty =
      mk_thy_type{Thy = "min", Tyop = "fun",
                  Args = [``:bir_exp_t``,
                          stmt_t_ty]}
    val const = mk_thy_const{Name = "BStmt_Assert",
                             Thy = "bir_program",
                             Ty = const_ty}
    val stmt = mk_comb (const, exp)
  in
    stmt
  end
*)

end;
