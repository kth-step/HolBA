open HolKernel boolLib liteLib simpLib Parse bossLib;

open bir_wpTheory;

(*
open bir_programTheory;
open bir_program_blocksTheory;
open bir_program_terminationTheory;
open bir_typing_progTheory;
open bir_envTheory;
open bir_exp_substitutionsTheory;
open bir_bool_expTheory;
open bir_auxiliaryTheory;
open bir_valuesTheory;
open bir_expTheory;
open bir_program_env_orderTheory;

load "pairLib";
*)

val bir_wp_exec_of_block_sound_alt_thm =prove(
``∀p ls post.
     bir_is_bool_exp post ⇒
     bir_is_well_typed_program p ⇒
     bir_is_valid_program p ⇒
     bir_declare_free_prog p ⇒
     bir_jmp_direct_labels_only p ⇒
!wps.
     FEVERY (λ(l1,wp1). bir_is_bool_exp wp1) wps ⇒
     FEVERY (λ(l1,wp1). bir_exec_to_labels_triple p l1 ls wp1 post)
       wps ⇒
!l.
     MEM l (bir_labels_of_program p) ⇒
     bir_edges_blocks_in_prog p l ⇒
     (∀l2. bir_edge_in_prog p l l2 ⇒ l2 ∉ ls) ⇒
!wps'.
     (bir_wp_exec_of_block p l ls post wps = SOME wps') ⇒
     FEVERY (λ(l1,wp1). bir_exec_to_labels_triple p l1 ls wp1 post) wps'
``,
  RW_TAC std_ss [bir_wp_exec_of_block_sound_thm] >>
  METIS_TAC [bir_wp_exec_of_block_sound_thm]
);

(* (fst o dest_imp o concl) thm; *)
fun initial_thm_for_prog_post_ls program post ls =
    let val thm = SPECL [program, ls, post] bir_wp_exec_of_block_sound_alt_thm;
	val post_thm = SIMP_CONV (srw_ss()) [
		       bir_is_bool_exp_def,type_of_bir_exp_def, bir_var_type_def, type_of_bir_imm_def, 
		       bir_type_is_Imm_def, BType_Bool_def] ``bir_is_bool_exp ^post``;
	val thm = MP thm (SIMP_RULE std_ss [] post_thm);
	val prog_type_thm = SIMP_CONV (srw_ss()) [
			    bir_is_well_typed_program_def,bir_is_well_typed_block_def,bir_is_well_typed_stmtE_def,
			    bir_is_well_typed_stmtB_def,bir_is_well_typed_label_exp_def,
			    type_of_bir_exp_def,bir_var_type_def,bir_type_is_Imm_def,type_of_bir_imm_def,
			    bir_extra_expsTheory.BExp_Aligned_type_of,BExp_unchanged_mem_interval_distinct_type_of,
			    bir_mem_expTheory.bir_number_of_mem_splits_REWRS
			    ] ``bir_is_well_typed_program ^program``;
	val thm = MP thm (SIMP_RULE std_ss [] prog_type_thm);
	val prog_valid_thm = SIMP_CONV (srw_ss()) [
			     bir_program_valid_stateTheory.bir_is_valid_program_def,
			     bir_program_valid_stateTheory.bir_program_is_empty_def,
			     bir_program_valid_stateTheory.bir_is_valid_labels_def,
			     bir_labels_of_program_def,BL_Address_HC_def
			     ] ``bir_is_valid_program ^program``;
	val thm = MP thm (SIMP_RULE std_ss [] prog_valid_thm);
	val no_declare_thm = prove((fst o dest_imp o concl) thm, cheat);
	val thm = MP thm (SIMP_RULE std_ss [] no_declare_thm);
	val prog_direct_jmp_thm = prove((fst o dest_imp o concl) thm, cheat);
	val thm = MP thm (SIMP_RULE std_ss [] prog_direct_jmp_thm);
    in
	thm
    end;


fun wp_on_label prog_thm wps wps_bool_thm wps_sound_thm label =
    let val thm1 = SPEC wps prog_thm;
	val thm1 = MP thm1 wps_bool_thm;
	val thm1 = MP thm1 wps_sound_thm;
	val thm2 = SPEC label thm1;
	val label_thm = EVAL ``MEM ^label (bir_labels_of_program ^program)``;
	val thm2 = MP thm2 (SIMP_RULE std_ss [] label_thm);
	val endges_in_prog_thm = prove((fst o dest_imp o concl) thm2, cheat);
	val thm2 = MP thm2 (SIMP_RULE std_ss [] endges_in_prog_thm);
	val wrong_cnd_thm = prove((fst o dest_imp o concl) thm2, cheat);
	val thm2 = MP thm2 (SIMP_RULE std_ss [] wrong_cnd_thm);
	val wps1_thm = EVAL ``bir_wp_exec_of_block ^program ^label ^ls ^post ^wps``;
	val wps1 = (snd o dest_comb o snd o dest_eq o concl) wps1_thm;
	val thm3 = SPEC wps1 thm2;
	val wps1_sound_thm = MP thm3 wps1_thm;
	val wps1_bool_thm = prove(
			    ``FEVERY (λ(l1,wp1). bir_is_bool_exp wp1) ^wps1``, cheat);
    in
	(wps1, wps1_sound_thm, wps1_bool_thm)
    end;


fun is_lbl_in_wps wps label =
    (optionSyntax.is_some o snd o dest_eq o concl o EVAL) ``FLOOKUP ^wps ^label``;

fun recursive_proc program program_thm wps wps_bool_thm wps_sound_thm =
    let val blocks = (snd o dest_BirProgram_list) program;
	val block = List.find (fn block =>
	      let val (label, _, end_statement) = dest_bir_block block;
		  val label = (snd o dest_eq o concl o EVAL) label;
	      in
		  if is_lbl_in_wps wps label then false
		  else if is_BStmt_Halt end_statement then false
		  else if is_BStmt_Jmp end_statement then
		      ((is_lbl_in_wps wps) o dest_BLE_Label o dest_BStmt_Jmp) end_statement
		  else if is_BStmt_CJmp end_statement then
		      (((is_lbl_in_wps wps) o dest_BLE_Label o #2 o dest_BStmt_CJmp) end_statement) andalso (((is_lbl_in_wps wps) o dest_BLE_Label o #3 o dest_BStmt_CJmp) end_statement)             
		  else 
		      false
	      end)
            blocks in
    case block of 
    SOME(bl) => 
      let val (label, _, end_statement) = dest_bir_block bl in
          wp_on_label program_thm wps wps_bool_thm wps_sound_thm label
      end
    | _ => (wps, wps_bool_thm, wps_sound_thm)
    end;


val program = ``
		           (BirProgram
              [<|bb_label :=
                   BL_Address_HC (Imm64 0x400570w)
                     "D101C3FF (sub sp, sp, #0x70)";
                 bb_statements :=
                   [BStmt_Assign (BVar "SP_EL0" (BType_Imm Bit64))
                      (BExp_BinExp BIExp_Minus
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 112w)))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400574w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400574w)
                     "F9000FE0 (str x0, [sp,#24])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 3
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 24w))) 8);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 24w))) BEnd_LittleEndian
                         (BExp_Den (BVar "R0" (BType_Imm Bit64))))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400578w)))|>;
               <|bb_label :=
                   BL_Address_HC (Imm64 0x400578w)
                     "B90017E1 (str w1, [sp,#20])";
                 bb_statements :=
                   [BStmt_Assert
                      (BExp_Aligned Bit64 2
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                    BStmt_Assert
                      (BExp_unchanged_mem_interval_distinct Bit64 0
                         16777216
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 20w))) 4);
                    BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                      (BExp_Store
                         (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                         (BExp_BinExp BIExp_Plus
                            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 20w))) BEnd_LittleEndian
                         (BExp_Cast BIExp_LowCast
                            (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                            Bit32))];
                 bb_last_statement :=
                   BStmt_Jmp (BLE_Label (BL_Address (Imm64
							 0x40057Cw)))|>
	      ])``;


val post = ``(BExp_BinPred BIPred_Eq (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))) (BExp_Const (Imm64 112w)))``;
val ls = ``\x.(x = (BL_Address (Imm64 0x400578w)))``;
val wps = ``(FEMPTY |+ (BL_Address (Imm64 0x400578w), ^post))``;
val wps_bool_thm = prove(
   ``FEVERY (λ(l1,wp1). bir_is_bool_exp wp1) ^wps``, cheat);
val wps_sound_thm = prove(
   ``FEVERY (λ(l1,wp1). bir_exec_to_labels_triple ^program l1 ^ls wp1 ^post) ^wps``, cheat);

val program_thm = initial_thm_for_prog_post_ls program post ls;

val (wps1, wps_sound1, wps_bool1) = recursive_proc program program_thm wps wps_bool_thm wps_sound_thm;

