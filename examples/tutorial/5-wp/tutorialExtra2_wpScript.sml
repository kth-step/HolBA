open HolKernel Parse boolLib bossLib;

(* From tools/wp: *)
open bir_wpLib bir_wp_expLib;
open easy_noproof_wpLib;
open bir_wpTheory bir_htTheory;

(* From theory/bir-support: *)
open bir_program_labelsTheory bir_program_valid_stateTheory
     bir_program_blocksTheory bir_program_multistep_propsTheory
     bir_subprogramTheory bir_bool_expTheory;
open bir_bool_expSyntax;

(* From theory/bir: *)
open bir_programTheory bir_valuesTheory;
open bir_expSyntax bir_programSyntax bir_immSyntax;
open HolBACoreSimps;

(* From shared: *)
open bir_exp_to_wordsLib bslSyntax;

(* From examples support: *)
open tutorial_bir_to_armSupportTheory;
open tutorial_wpSupportLib;

(* From examples: *)
open birExamples2BinaryTheory;

(* From HOL4: *)
open finite_mapSyntax pairSyntax pred_setSyntax;

val _ = new_theory "tutorialExtra2_wp";

val prog_tm = (lhs o concl) bprog_is_even_odd_def;

(*
Sections and hoare triples:
*)

val get_n = bden (bvar "n" ``(BType_Imm Bit32)``);

val get_v1 = bconst ``v1:word32``;

val get_0  = bconst ``0w:word32``;
val get_1  = bconst ``1w:word32``;
val get_2  = bconst ``2w:word32``;

(* =============================================================== *)

(* overall contract is_even *)
val bir_ieo_ev_pre_def = Define `bir_ieo_ev_pre v1 =
^(beq (get_n, get_v1))
`;

val bir_ieo_ev_post_yes_def = Define `bir_ieo_ev_post_yes v1 =
^(beq (bmod (get_v1, get_2), get_0))
`;

val bir_ieo_ev_post_no_def = Define `bir_ieo_ev_post_no v1 =
^(beq (bmod (get_v1, get_2), get_1))
`;


(* overall contract is_odd *)
val bir_ieo_od_pre_def = Define `bir_ieo_od_pre v1 =
^(beq (get_n, get_v1))
`;

val bir_ieo_od_post_yes_def = Define `bir_ieo_od_post_yes v1 =
^(beq (bmod (get_v1, get_2), get_1))
`;

val bir_ieo_od_post_no_def = Define `bir_ieo_od_post_no v1 =
^(beq (bmod (get_v1, get_2), get_0))
`;

(* =============================================================== *)

val bir_ieo_invariant_def = Define `bir_ieo_invariant v1 =
^(beq (bmod (get_v1, get_2), bmod (get_n, get_2)))
`;

val bir_ieo_invariant_mid_def = Define `bir_ieo_invariant_mid v1 =
^(beq (bmod (get_v1, get_2), bmod (bplus(get_n, get_1), get_2)))
`;

val bir_ieo_variant_def = Define `bir_ieo_variant =
^(get_n)
`;

(* =============================================================== *)

(* section is_even_1 *)
val bir_ieo_sec_iseven_1_pre_def = Define `bir_ieo_sec_iseven_1_pre v1 =
bir_ieo_invariant v1
`;

val bir_ieo_sec_iseven_1_post_def = Define `bir_ieo_sec_iseven_1_post v1 =
\l. if l = BL_Address (Imm32 200w) then
      bir_ieo_ev_post_yes v1
    else if l = BL_Address (Imm32 004w) then
      bir_ieo_invariant v1
    else
      bir_exp_false
`;

(* section is_even_2 *)
val bir_ieo_sec_iseven_2_pre_def = Define `bir_ieo_sec_iseven_2_pre v1 =
bir_ieo_invariant v1
`;

val bir_ieo_sec_iseven_2_post_def = Define `bir_ieo_sec_iseven_2_post v1 =
bir_ieo_invariant_mid v1
`;

(* section is_odd_1 *)
val bir_ieo_sec_isodd_1_pre_def = Define `bir_ieo_sec_isodd_1_pre v1 =
bir_ieo_invariant_mid v1
`;

val bir_ieo_sec_isodd_1_post_def = Define `bir_ieo_sec_isodd_1_post v1 =
\l. if l = BL_Address (Imm32 200w) then
      bir_ieo_ev_post_no v1
    else if l = BL_Address (Imm32 004w) then
      bir_ieo_invariant_mid v1
    else
      bir_exp_false
`;

(* section is_odd_2 *)
val bir_ieo_sec_isodd_2_pre_def = Define `bir_ieo_sec_isodd_2_pre v1 =
bir_ieo_invariant_mid v1
`;

val bir_ieo_sec_isodd_2_post_def = Define `bir_ieo_sec_isodd_2_post v1 =
bir_ieo_invariant v1
`;


val _ = export_theory();
