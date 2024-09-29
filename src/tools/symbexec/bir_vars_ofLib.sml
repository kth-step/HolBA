structure bir_vars_ofLib =
struct

local

open HolKernel Parse boolLib bossLib;

open bir_typing_expTheory;
open bir_typing_expSyntax;

open HolBACoreSimps;

  (* error handling *)
  val libname = "bir_vars_ofLib"
  val ERR = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname

in (* local *)

  (* TODO: can probably speed this up by extending the caching into the evaluation of variables subexpressions, like in the function type_of_bir_exp_DIRECT_CONV,
       but only relevant for handling of bigger expressions *)
  fun bir_vars_of_exp_DIRECT_CONV tm =
    let
     val _ = if is_bir_vars_of_exp tm then () else
               raise ERR "bir_vars_of_exp_DIRECT_CONV" "cannot handle term";
    in
      (SIMP_CONV (std_ss++holBACore_ss) [] THENC EVAL) tm
    end;
  val bir_vars_of_exp_DIRECT_CONV = aux_moveawayLib.wrap_cache_result Term.compare bir_vars_of_exp_DIRECT_CONV;

  val bir_vars_of_exp_CONV =
    birs_auxLib.GEN_match_conv (is_bir_vars_of_exp) bir_vars_of_exp_DIRECT_CONV;

end (* local *)

end (* struct *)
