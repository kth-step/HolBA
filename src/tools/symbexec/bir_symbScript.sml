open HolKernel Parse boolLib bossLib;

open symb_interpretTheory;
open symb_recordTheory;
open symb_record_soundTheory;

val _ = new_theory "bir_symb";

(*
DEFINITIONS: INSTANTIATION FOR BIR/SBIR
=======================================================
*)
(*
val _ = Datatype `bir_conc_state_t = int`;
val _ = Datatype `bir_symb_state_t = int`;

val bir_symb_rec_sbir_def = Define `
  bir_symb_rec_sbir a b c d =
    <|
      sr_val_true        := a;
      sr_interpret_f     := b;
      sr_step_conc       := c;
      sr_step_symb       := d;
   |>
`;
*)

val _ = export_theory();
