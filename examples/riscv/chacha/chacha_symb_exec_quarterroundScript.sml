open HolKernel Parse boolLib bossLib;

open wordsTheory;

open bir_symbLib;

open chachaTheory chacha_specTheory;

val _ = new_theory "chacha_symb_exec_quarterround";

(* --------------------------- *)
(* Symbolic analysis execution *)
(* --------------------------- *)

val _ = show_tags := true;

(* ---------- *)
(* first line *)
(* ---------- *)

val symb_analysis_thm =
 bir_symb_analysis_thm
  bir_chacha_prog_def
  chacha_line_init_addr_def [chacha_line_end_addr_def]
  bspec_chacha_line_pre_def chacha_birenvtyl_def;

val _ = Portable.pprint Tag.pp_tag (tag symb_analysis_thm);

Theorem chacha_line_symb_analysis_thm = symb_analysis_thm

(* ----------- *)
(* second line *)
(* ----------- *)

val symb_analysis_thm =
 bir_symb_analysis_thm
  bir_chacha_prog_def
  chacha_other_line_init_addr_def [chacha_other_line_end_addr_def]
  bspec_chacha_line_pre_other_def chacha_birenvtyl_def;

val _ = Portable.pprint Tag.pp_tag (tag symb_analysis_thm);

Theorem chacha_other_line_symb_analysis_thm = symb_analysis_thm

(* ------------------- *)
(* first quarter round *)
(* ------------------- *)

val symb_analysis_thm =
 bir_symb_analysis_thm
  bir_chacha_prog_def
  chacha_quarter_round_init_addr_def [chacha_quarter_round_end_addr_def]
  bspec_chacha_quarter_round_pre_def chacha_birenvtyl_def;

val _ = Portable.pprint Tag.pp_tag (tag symb_analysis_thm);

Theorem chacha_quarter_round_symb_analysis_thm = symb_analysis_thm

(* ----------- *)
(* first round *)
(* ----------- *)

val symb_analysis_thm =
 bir_symb_analysis_thm
  bir_chacha_prog_def
  chacha_round_init_addr_def [chacha_round_end_addr_def]
  bspec_chacha_round_pre_def chacha_birenvtyl_def;

val _ = Portable.pprint Tag.pp_tag (tag symb_analysis_thm);

Theorem chacha_round_symb_analysis_thm = symb_analysis_thm

val _ = export_theory ();
