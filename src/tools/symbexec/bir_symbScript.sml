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
val _ = Datatype `bir_concst_t = symb_concst_t bir_programcounter_t string bir_val_t bir_status_t`;
val _ = Datatype `bir_symbst_t = symb_symbst_t bir_programcounter_t string bir_exp_t bir_status_t`;
(* function to convert between conrete states *)
(*
val _ = Datatype `bir_state_t = <|
  bst_pc       : bir_programcounter_t;
  bst_environ  : bir_var_environment_t;
  bst_status   : bir_status_t
|>`;
*)

(* sr_step_conc is "bir_exec_step" *)
(*
val bir_symb_rec_sbir_def = Define `
  bir_symb_rec_sbir prog =
    <|
      sr_val_true        := bir_val_true;
      sr_mk_exp_symb_f   := BExp_Den;
      sr_mk_exp_conj_f   := BExp_BinExp ();
      sr_mk_exp_eq_f     := \e1. if typeof e1 = SOME MemType then BExp_MemEq () e1 else BExp_BinPred () e1;

      sr_subst_f         := \(s,e). bir_exp_subst (FUPDATE (s,e) FEMPTY);

      (* symbols of symbolic exepressions *)
      sr_symbols_f       := bir_vars_of_exp;

      (* type business *)
      sr_typeof_val      := type_of_bir_val;
      sr_typeof_symb     := bir_var_type;
      sr_typeof_exp      := type_of_bir_exp;
      sr_ARB_val         := bir_val_default;

      (* interpretation business, type error produces NONE value *)
      sr_interpret_f     := ();

      (* finally, concrete and symbolic executions *)
      sr_step_conc       := sr_step_conc;

      sr_step_symb       := ();
   |>
`;
*)

val _ = export_theory();
