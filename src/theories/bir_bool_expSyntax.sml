structure bir_bool_expSyntax :> bir_bool_expSyntax =
struct

  open Abbrev

  local

  open HolKernel Parse boolLib bossLib

  val ERR = mk_HOL_ERR "bir_bool_expSyntax"

  fun syntax_fns n d m = HolKernel.syntax_fns {n = n, dest = d, make = m} "bir_bool_exp"
  fun syntax_fns0 s = let val (tm, _, _, is_f) = syntax_fns 0
     (fn tm1 => fn e => fn tm2 =>
         if Term.same_const tm1 tm2 then () else raise e)
     (fn tm => fn () => tm) s in (tm, is_f) end;
  val syntax_fns1 = syntax_fns 1 HolKernel.dest_monop HolKernel.mk_monop;
  val syntax_fns2 = syntax_fns 2 HolKernel.dest_binop HolKernel.mk_binop;
  val syntax_fns3 = syntax_fns 3 HolKernel.dest_triop HolKernel.mk_triop;
  val syntax_fns4 = syntax_fns 4 HolKernel.dest_quadop HolKernel.mk_quadop;

  in

  val ( bir_val_true_tm, is_bir_val_true ) = syntax_fns0 "bir_val_true";
  val (bir_val_false_tm, is_bir_val_false) = syntax_fns0 "bir_val_false";

  val ( bir_exp_true_tm, is_bir_exp_true ) = syntax_fns0 "bir_exp_true";
  val (bir_exp_false_tm, is_bir_exp_false) = syntax_fns0 "bir_exp_false";

  val ( bir_exp_or_tm, mk_bir_exp_or , dest_bir_exp_or , is_bir_exp_or ) = syntax_fns2 "bir_exp_or";
  val (bir_exp_and_tm, mk_bir_exp_and, dest_bir_exp_and, is_bir_exp_and) = syntax_fns2 "bir_exp_and";
  val (bir_exp_not_tm, mk_bir_exp_not, dest_bir_exp_not, is_bir_exp_not) = syntax_fns1 "bir_exp_not";
  val (bir_exp_imp_tm, mk_bir_exp_imp, dest_bir_exp_imp, is_bir_exp_imp) = syntax_fns2 "bir_exp_imp";

  end (* local *)

end (* bir_bool_expSyntax *)
