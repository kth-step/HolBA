structure bir_symb2_masterLib = 
struct

local

open HolKernel Parse;

open bir_symb2_init_envLib;
open bir_symb2_execLib;

open bir_exp_to_wordsLib;

val pdecide_on = true;
val debug_on = false;


in

(* SMT helper *)
(*
val btm = precond;
*)
fun pdecide btm =
  if not pdecide_on then true else
  let
    val _ = if debug_on then print_term btm else ();
    val _ = if debug_on then print "\n" else ();

    val wtm = bir2bool btm;
    val _ = if debug_on then print_term wtm else ();
    val _ = if debug_on then print "\n" else ();

    val taut =     ((HolSmtLib.Z3_ORACLE_PROVE wtm; true)
                       handle HOL_ERR e => false);

    val model = ((Z3_SAT_modelLib.Z3_GET_SAT_MODEL wtm; true)
                       handle HOL_ERR e => false);

    val _ = if debug_on then print ("taut: "  ^ (if taut then "true\n" else "false\n")) else ();
    val _ = if debug_on then print ("model: " ^ (if model then "true\n" else "false\n")) else ();
  in
    taut orelse model
  end;


fun symb_exec2_process_to_leafs maxdepth precond prog =
  symb_exec_leaflist (symb_exec_program maxdepth precond prog pdecide);

(*
val st = hd leafs;
*)
fun symb_exec2_get_predword st =
  let
    val (pc, env, pred, status, obs) = dest_bir_symb_state st;
    val btm = pred;

    val _ = if debug_on then print_term btm else ();
    val _ = if debug_on then print "\n" else ();

    val wtm = bir2bool btm;
    val _ = if debug_on then print_term wtm else ();
    val _ = if debug_on then print "\n" else ();
  in
    wtm
  end;


fun symb_exec2_model_t2s model =
  let
    fun pair_t2s (name,tm) = (name, term_to_string tm);
  in
    List.map pair_t2s model
  end;


(*
val wtm =
EVAL (subst [``R0:word64`` |-> ``1w:word64``, ``SP_EL0:word64`` |-> ``0x80000000w:word64``] wtm)

val get_x = bconst ``R0:word64``;
val get_sp = bconst ``SP_EL0:word64``;
*)
fun symb_exec2_get_init_vals wtm =
  let
    val model = ((Z3_SAT_modelLib.Z3_GET_SAT_MODEL wtm)
                       handle HOL_ERR e => []);
    val model_w_strs = symb_exec2_model_t2s model
  in
    model_w_strs
  end;

(*
(*
val subs = [``R0:word64`` |-> ``1w:word64``, ``SP_EL0:word64`` |-> ``0x80000000w:word64``];
val st = (hd leafs);
*)
fun symb_exec2_concr_state subs st =
  let
    val (pc, env, pred, status, obs) = dest_bir_symb_state st;

    val pred_subs = subst subs pred;

    val pred_eval_tm = ``bir_eval_exp ^(pred_subs) (BEnv FEMPTY)``;
    val pred_val = (snd o dest_eq o concl o EVAL) pred_eval_tm;
  in
``<|
  bsst_pc           := ^pc; 
  bsst_environ      := FEMPTY;
  bsst_pred         := ^(bconst );
  bsst_status       := ^status;
  bsst_obs          := ^obs;
 |>``
  end;
*)

end



end
