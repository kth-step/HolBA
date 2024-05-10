open HolKernel Parse boolLib bossLib;

(* From tools/wp: *)
open bir_wpLib bir_wp_expLib;
open bir_wpTheory bir_htTheory;
open bir_wp_interfaceLib;

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

(* From examples: *)
open bir_prog_freuseTheory;

(* From HOL4: *)
open finite_mapSyntax pairSyntax pred_setSyntax;

val _ = new_theory "freuse_wp";

val prog_tm = (lhs o concl) freuse_def;

(*
Sections and hoare triples:
*)

val get_x = bden (bvar "x" ``(BType_Imm Bit32)``);
val get_y = bden (bvar "y" ``(BType_Imm Bit32)``);
val get_z = bden (bvar "z" ``(BType_Imm Bit32)``);

val get_a = bden (bvar "a" ``(BType_Imm Bit32)``);
val get_b = bden (bvar "b" ``(BType_Imm Bit32)``);
val get_c = bden (bvar "c" ``(BType_Imm Bit32)``);

val get_t = bden (bvar "t" ``(BType_Imm Bit32)``);

val get_v1 = bconst ``v1:word32``;
val get_v2 = bconst ``v2:word32``;
val get_v3 = bconst ``v3:word32``;

val get_4  = bconst ``0x004w:word32``;
val get_8  = bconst ``0x008w:word32``;
val get_2  = bconst ``2w:word32``;



(* section add_1 *)
val bir_att_sec_add_1_pre_def = Define `bir_att_sec_add_1_pre v1 v2 v3 =
^(bandl [
   (beq (get_a, get_v1)),
   (beq (get_b, get_v2)),
   (beq (get_t, get_v3))
   ])
`;

val bir_att_sec_add_1_post_def = Define `bir_att_sec_add_1_post v1 v2 v3 =
^(bandl [
   (beq (get_t, get_v3)),
   (beq (get_c, bplus(get_v1, get_v2)))
   ])
`;

(* section add_2 *)
val bir_att_sec_add_2_post_def = Define `bir_att_sec_add_2_post v1 v2 =
^(beq (get_c, bplus(get_v1, get_v2)))
`;



(* section call_1 *)
val bir_att_sec_call_1_pre_def = Define `bir_att_sec_call_1_pre v1 v2 =
^(bandl [
   (beq (get_x, get_v1)),
   (beq (get_y, get_v2))
   ])
`;

val bir_att_sec_call_1_post_def = Define `bir_att_sec_call_1_post v1 v2 =
^(bandl [
   (beq (get_a, get_v1)),
   (beq (get_b, get_v2)),
   (beq (get_t, get_4 ))
   ])
`;

(* section call_2 *)
val bir_att_sec_call_2_pre_def = Define `bir_att_sec_call_2_pre v1 =
^(bandl [
   (beq (get_c, get_v1))
   ])
`;

val bir_att_sec_call_2_post_def = Define `bir_att_sec_call_2_post v1 =
^(bandl [
   (beq (get_a, get_v1)),
   (beq (get_b, get_v1)),
   (beq (get_t, get_8 ))
   ])
`;

val bir_att_sec_1_post_def = Define `bir_att_sec_1_post v1 v2 =
^(bandl [
   (beq (get_c, bplus(get_v1, get_v2)))
   ])
`;

val bir_att_sec_2_post_def = Define `bir_att_sec_2_post v1 v2 =
^(bandl [
   (beq (get_c, bmult(get_2, bplus(get_v1, get_v2))))
   ])
`;






val prefix = "bir_att_sec_add_1_";
val first_block_label_tm = ``BL_Address (Imm32 0x100w)``;
val ending_set =  ``(BL_Address (Imm32 0x104w)) INSERT (BL_Address (Imm32 v3)) INSERT v4s``;
val postcond_tm = ``\l. if (l = BL_Address (Imm32 0x104w))
                        then bir_att_sec_add_1_post v1 v2 v3
                        else bir_exp_false``;

val defs = [freuse_def, bir_att_sec_add_1_post_def,
            bir_exp_false_def, BType_Bool_def];

val (bir_att_sec_add_1_ht, bir_att_sec_add_1_wp_tm) =
  bir_obtain_ht prog_tm first_block_label_tm
                ending_set ending_set_to_sml_list
                postcond_tm postcond_exp_from_label
                prefix defs;

val bir_att_sec_add_1_wp_def =
  Define `bir_att_sec_add_1_wp v1 v2 v3 = ^(bir_att_sec_add_1_wp_tm)`;
val _ = save_thm (prefix ^ "ht", bir_att_sec_add_1_ht);


val prefix = "bir_att_sec_call_1_";
val first_block_label_tm = ``BL_Address (Imm32 0x000w)``;
val ending_set =  ``{BL_Address (Imm32 0x100w); BL_Address (Imm32 0x004w); BL_Address (Imm32 0x008w)}``;
val postcond_tm = ``\l. if (l = BL_Address (Imm32 0x100w))
                        then bir_att_sec_call_1_post v1 v2
                        else bir_exp_false``;

val defs = [freuse_def, bir_att_sec_call_1_post_def,
            bir_exp_false_def, BType_Bool_def];

val (bir_att_sec_call_1_ht, bir_att_sec_call_1_wp_tm) =
  bir_obtain_ht prog_tm first_block_label_tm
                ending_set ending_set_to_sml_list
                postcond_tm postcond_exp_from_label
                prefix defs;

val bir_att_sec_call_1_wp_def =
  Define `bir_att_sec_call_1_wp v1 v2 = ^(bir_att_sec_call_1_wp_tm)`;
val _ = save_thm (prefix ^ "ht", bir_att_sec_call_1_ht);


val prefix = "bir_att_sec_call_2_";
val first_block_label_tm = ``BL_Address (Imm32 0x004w)``;
val ending_set =  ``{BL_Address (Imm32 0x100w); BL_Address (Imm32 0x008w)}``;
val postcond_tm = ``\l. if (l = BL_Address (Imm32 0x100w))
                        then bir_att_sec_call_2_post v1
                        else bir_exp_false``;

val defs = [freuse_def, bir_att_sec_call_2_post_def,
            bir_exp_false_def, BType_Bool_def];

val (bir_att_sec_call_2_ht, bir_att_sec_call_2_wp_tm) =
  bir_obtain_ht prog_tm first_block_label_tm
                ending_set ending_set_to_sml_list
                postcond_tm postcond_exp_from_label
                prefix defs;

val bir_att_sec_call_2_wp_def =
  Define `bir_att_sec_call_2_wp v1 = ^(bir_att_sec_call_2_wp_tm)`;
val _ = save_thm (prefix ^ "ht", bir_att_sec_call_2_ht);



(* TODO: a similar function is also defined in 7-composition, needs to go somewhere else *)
fun try_disch_assump_w_EVAL t =
  let
    val t_d      = DISCH_ALL t;
    val assum_tm = (fst o dest_imp o concl) t_d;
    val t_as     = EVAL assum_tm;
    val t2       = REWRITE_RULE [t_as] (DISCH assum_tm t)
  in
    t2
  end
  handle HOL_ERR _ => t;


val prefix = "bir_att_sec_add_2_";
val precond_tm  = ``bir_att_sec_add_1_post v1 v2 v3``;
val postcond_tm = ``\l. if (l = BL_Address (Imm32 v3))
                        then bir_att_sec_add_2_post v1 v2
                        else bir_exp_false``;

val prog_block_addr = ``(Imm32 0x104w)``;
val prog_tm = ``freuse``;
val prog_block = (snd o dest_eq o concl o EVAL) ``(SND (THE (bir_get_program_block_info_by_label ^prog_tm (BL_Address ^prog_block_addr))))``;
val ret_block_specl = [prog_tm, prog_block, ``BL_Address ^prog_block_addr``, ``Imm32 v3``, ``v4s:bir_label_t->bool``, ``(BVar "t" (BType_Imm Bit32))``, ``bir_att_sec_add_2_post v1 v2``];
val ret_block_thm =
       (try_disch_assump_w_EVAL o try_disch_assump_w_EVAL o
        try_disch_assump_w_EVAL o try_disch_assump_w_EVAL)
       (SPECL ret_block_specl bir_ret_block_triple_wp_thm);
val prog_no_assum_thm = REWRITE_RULE [EVAL ``bir_prog_has_no_assumes ^prog_tm``]
                                     (SPEC prog_tm bir_never_assumviol_ht);

val bir_att_sec_add_2_ht = prove(``
!v1 v2 v3 v4s.
(MEM (BL_Address (Imm32 v3))
     (bir_labels_of_program ^prog_tm)) ==>
((BL_Address (Imm32 v3)) NOTIN v4s) ==>
(bir_exec_to_labels_triple
   ^prog_tm
   (BL_Address ^prog_block_addr)
   ((BL_Address (Imm32 v3)) INSERT v4s)
   ^(precond_tm)
   ^(postcond_tm))
``,

REPEAT STRIP_TAC >>
REWRITE_TAC [bir_att_sec_add_1_post_def] >>
ASSUME_TAC ret_block_thm >>
REV_FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_att_sec_add_2_post_def] >>
IMP_RES_TAC prog_no_assum_thm
);


val _ = save_thm (prefix ^ "ht", bir_att_sec_add_2_ht);



val _ = export_theory();
