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
open bir_wp_frontendLib;

(* From examples: *)
open birExamples2BinaryTheory;

(* From HOL4: *)
open finite_mapSyntax pairSyntax pred_setSyntax;

val _ = new_theory "tutorialExtra2_wp";

val prog_tm = (lhs o concl) bprog_is_even_odd_def;

(*
Sections and hoare triples:
*)

val get_n  = bden (bvar "n" ``(BType_Imm Bit64)``);

val get_v1 = bconst ``v1:word64``;
val get_v  = bconst ``v :word64``;

val get_0  = bconst ``0w:word64``;
val get_1  = bconst ``1w:word64``;
val get_2  = bconst ``2w:word64``;

(* =============================================================== *)

(* overall contract is_even *)
val bir_ieo_pre_def = Define `bir_ieo_pre v1 =
^(beq (get_n, get_v1))
`;

val bir_ieo_post_even_def = Define `bir_ieo_post_even v1 =
^(beq (bmod (get_v1, get_2), get_0))
`;

val bir_ieo_post_odd_def = Define `bir_ieo_post_odd v1 =
^(beq (bmod (get_v1, get_2), get_1))
`;

(* =============================================================== *)

val bir_ieo_invariant_def = Define `bir_ieo_invariant v1 =
^(beq (bmod (get_v1, get_2), bmod (get_n, get_2)))
`;

val bir_ieo_condition_def = Define `bir_ieo_condition =
^(bgt(get_n, get_1))
`;

val bir_ieo_variant_def = Define `bir_ieo_variant =
^(get_n)
`;

(* =============================================================== *)

(* section is_even loop pre *)
val bir_ieo_sec_iseven_loop_pre_def = Define `bir_ieo_sec_iseven_loop_pre v1 v =
(BExp_BinExp BIExp_And (bir_ieo_invariant v1)
                  (BExp_BinExp BIExp_And bir_ieo_condition
                     (BExp_BinPred BIExp_Equal bir_ieo_variant ^(get_v))))
`;

(* section is_even exit pre *)
val bir_ieo_sec_iseven_exit_pre_def = Define `bir_ieo_sec_iseven_exit_pre v1 =
(BExp_BinExp BIExp_And (bir_ieo_invariant v1) (BExp_UnaryExp BIExp_Not bir_ieo_condition))
`;


(* section is_even loop post *)
val bir_ieo_sec_iseven_loop_post_def = Define `bir_ieo_sec_iseven_loop_post v1 v =
\l. if l = BL_Address (Imm32 0x000w) then
       (BExp_BinExp BIExp_And (bir_ieo_invariant v1)
                  (BExp_BinExp BIExp_And
                     (BExp_BinPred BIExp_LessThan bir_ieo_variant ^get_v)
                     (BExp_BinPred BIExp_LessOrEqual ^get_0 bir_ieo_variant)))
    else
      bir_exp_false
`;


(* section is_even exit post *)
val bir_ieo_sec_iseven_exit_post_def = Define `bir_ieo_sec_iseven_exit_post v1 =
\l. if l = BL_Address (Imm32 0x200w) then
      bir_ieo_post_even v1
    else if l = BL_Address (Imm32 0x204w) then
      bir_ieo_post_odd v1
    else
      bir_exp_false
`;

(* =============================================================== *)

(* section is_odd loop pre *)
val bir_ieo_sec_isodd_loop_pre_def = Define `bir_ieo_sec_isodd_loop_pre v1 v =
(BExp_BinExp BIExp_And (bir_ieo_invariant v1)
                  (BExp_BinExp BIExp_And bir_ieo_condition
                     (BExp_BinPred BIExp_Equal bir_ieo_variant ^(get_v))))
`;

(* section is_odd exit pre *)
val bir_ieo_sec_isodd_exit_pre_def = Define `bir_ieo_sec_isodd_exit_pre v1 =
(BExp_BinExp BIExp_And (bir_ieo_invariant v1) (BExp_UnaryExp BIExp_Not bir_ieo_condition))
`;


(* section is_odd loop post *)
val bir_ieo_sec_isodd_loop_post_def = Define `bir_ieo_sec_isodd_loop_post v1 v =
\l. if l = BL_Address (Imm32 0x100w) then
       (BExp_BinExp BIExp_And (bir_ieo_invariant v1)
                  (BExp_BinExp BIExp_And
                     (BExp_BinPred BIExp_LessThan bir_ieo_variant ^get_v)
                     (BExp_BinPred BIExp_LessOrEqual ^get_0 bir_ieo_variant)))
    else
      bir_exp_false
`;


(* section is_odd exit post *)
val bir_ieo_sec_isodd_exit_post_def = Define `bir_ieo_sec_isodd_exit_post v1 =
\l. if l = BL_Address (Imm32 0x200w) then
      bir_ieo_post_odd v1
    else if l = BL_Address (Imm32 0x204w) then
      bir_ieo_post_even v1
    else
      bir_exp_false
`;



(* =============================================================== *)
(* =============================================================== *)
(* =============================================================== *)



val prefix = "bir_ieo_sec_iseven_loop_";
val first_block_label_tm = ``BL_Address (Imm32 0x000w)``;
val ending_set =  ``{BL_Address (Imm32 0x000w); BL_Address (Imm32 0x200w); BL_Address (Imm32 0x204w)}``;
val postcond_tm = ``bir_ieo_sec_iseven_loop_post v1 v``;

val defs = [bprog_is_even_odd_def, bir_ieo_sec_iseven_loop_post_def,
            bir_ieo_post_odd_def, bir_ieo_post_even_def,
            bir_ieo_invariant_def, bir_ieo_condition_def, bir_ieo_variant_def,
            bir_exp_false_def, BType_Bool_def];

val (bir_ieo_sec_iseven_loop_ht, bir_ieo_sec_iseven_loop_wp_tm) =
  bir_obtain_ht prog_tm first_block_label_tm
                ending_set ending_set_to_sml_list
                postcond_tm postcond_exp_from_label
                prefix defs;

val bir_ieo_sec_iseven_loop_wp_def =
  Define `bir_ieo_sec_iseven_loop_wp v1 v = ^(bir_ieo_sec_iseven_loop_wp_tm)`;
val _ = save_thm (prefix ^ "ht", bir_ieo_sec_iseven_loop_ht);



val prefix = "bir_ieo_sec_iseven_exit_";
val first_block_label_tm = ``BL_Address (Imm32 0x000w)``;
val ending_set =  ``{BL_Address (Imm32 0x000w); BL_Address (Imm32 0x200w); BL_Address (Imm32 0x204w)}``;
val postcond_tm = ``bir_ieo_sec_iseven_exit_post v1``;

val defs = [bprog_is_even_odd_def, bir_ieo_sec_iseven_exit_post_def,
            bir_ieo_post_odd_def, bir_ieo_post_even_def, bir_ieo_invariant_def,
            bir_exp_false_def, BType_Bool_def];

val (bir_ieo_sec_iseven_exit_ht, bir_ieo_sec_iseven_exit_wp_tm) =
  bir_obtain_ht prog_tm first_block_label_tm
                ending_set ending_set_to_sml_list
                postcond_tm postcond_exp_from_label
                prefix defs;

val bir_ieo_sec_iseven_exit_wp_def =
  Define `bir_ieo_sec_iseven_exit_wp v1 = ^(bir_ieo_sec_iseven_exit_wp_tm)`;
val _ = save_thm (prefix ^ "ht", bir_ieo_sec_iseven_exit_ht);

(* =============================================================== *)

val prefix = "bir_ieo_sec_isodd_loop_";
val first_block_label_tm = ``BL_Address (Imm32 0x100w)``;
val ending_set =  ``{BL_Address (Imm32 0x100w); BL_Address (Imm32 0x200w); BL_Address (Imm32 0x204w)}``;
val postcond_tm = ``bir_ieo_sec_isodd_loop_post v1 v``;

val defs = [bprog_is_even_odd_def, bir_ieo_sec_isodd_loop_post_def,
            bir_ieo_post_odd_def, bir_ieo_post_even_def,
            bir_ieo_invariant_def, bir_ieo_condition_def, bir_ieo_variant_def,
            bir_exp_false_def, BType_Bool_def];

val (bir_ieo_sec_isodd_loop_ht, bir_ieo_sec_isodd_loop_wp_tm) =
  bir_obtain_ht prog_tm first_block_label_tm
                ending_set ending_set_to_sml_list
                postcond_tm postcond_exp_from_label
                prefix defs;

val bir_ieo_sec_isodd_loop_wp_def =
  Define `bir_ieo_sec_isodd_loop_wp v1 v = ^(bir_ieo_sec_isodd_loop_wp_tm)`;
val _ = save_thm (prefix ^ "ht", bir_ieo_sec_isodd_loop_ht);



val prefix = "bir_ieo_sec_isodd_exit_";
val first_block_label_tm = ``BL_Address (Imm32 0x100w)``;
val ending_set =  ``{BL_Address (Imm32 0x100w); BL_Address (Imm32 0x200w); BL_Address (Imm32 0x204w)}``;
val postcond_tm = ``bir_ieo_sec_isodd_exit_post v1``;

val defs = [bprog_is_even_odd_def, bir_ieo_sec_isodd_exit_post_def,
            bir_ieo_post_odd_def, bir_ieo_post_even_def, bir_ieo_invariant_def,
            bir_exp_false_def, BType_Bool_def];

val (bir_ieo_sec_isodd_exit_ht, bir_ieo_sec_isodd_exit_wp_tm) =
  bir_obtain_ht prog_tm first_block_label_tm
                ending_set ending_set_to_sml_list
                postcond_tm postcond_exp_from_label
                prefix defs;

val bir_ieo_sec_isodd_exit_wp_def =
  Define `bir_ieo_sec_isodd_exit_wp v1 = ^(bir_ieo_sec_isodd_exit_wp_tm)`;
val _ = save_thm (prefix ^ "ht", bir_ieo_sec_isodd_exit_ht);


val _ = export_theory();
