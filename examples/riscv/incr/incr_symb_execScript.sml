open HolKernel Parse boolLib bossLib;

open bir_symbLib;

open incrTheory;
open incr_propTheory;

val _ = new_theory "incr_symb_exec";

(* ----------------------- *)
(* Symbolic analysis setup *)
(* ----------------------- *)

val bprog_tm = (snd o dest_eq o concl) bir_incr_prog_def;

val birs_state_init_lbl = (snd o dest_eq o concl o EVAL) ``bir_block_pc (BL_Address (Imm64 0x00w))``;

val birs_stop_lbls = [(snd o dest_eq o concl o EVAL) ``bir_block_pc (BL_Address (Imm64 0x4w))``];

val bprog_envtyl = (fst o dest_eq o concl) incr_birenvtyl_def;

val birs_pcond = (snd o dest_eq o concl) incr_bsysprecond_thm;

(* --------------------------- *)
(* Symbolic analysis execution *)
(* --------------------------- *)

val result = bir_symb_analysis bprog_tm
 birs_state_init_lbl birs_stop_lbls
 bprog_envtyl birs_pcond;

val _ = show_tags := true;
val _ = Portable.pprint Tag.pp_tag (tag result);

Theorem incr_symb_analysis_thm = result

val _ = export_theory ();
