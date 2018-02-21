open HolKernel boolLib liteLib simpLib Parse bossLib;

open bir_wpTheory;

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



(* initial_thm_for_prog_post_ls *)
fun proc_step0 reusable_thm (program, post, ls) defs =
    let
        val var_l = ``l:(bir_label_t)``;
        val var_wps = ``wps:(bir_label_t |-> bir_exp_t)``;
        val var_wps1 = ``wps':(bir_label_t |-> bir_exp_t)``;
        val thm = SPECL [program, var_l, ls, post, var_wps, var_wps1] reusable_thm;

        val post_bool_conv = [
		       bir_is_bool_exp_def,type_of_bir_exp_def, bir_var_type_def, type_of_bir_imm_def, 
		       bir_type_is_Imm_def, BType_Bool_def];
        val prog_typed_conv = [
			    bir_is_well_typed_program_def,bir_is_well_typed_block_def,bir_is_well_typed_stmtE_def,
			    bir_is_well_typed_stmtB_def,bir_is_well_typed_label_exp_def,
			    type_of_bir_exp_def,bir_var_type_def,bir_type_is_Imm_def,type_of_bir_imm_def,
			    bir_extra_expsTheory.BExp_Aligned_type_of,BExp_unchanged_mem_interval_distinct_type_of,
			    bir_mem_expTheory.bir_number_of_mem_splits_REWRS
			    ];
        val prog_valid_conv = [
			     bir_program_valid_stateTheory.bir_is_valid_program_def,
			     bir_program_valid_stateTheory.bir_program_is_empty_def,
			     bir_program_valid_stateTheory.bir_is_valid_labels_def,
			     bir_labels_of_program_def,BL_Address_HC_def
			     ];
        val no_declare_conv = [
			     bir_declare_free_prog_exec_def, bir_isnot_declare_stmt_def
			     ];

	val post_bool_thm = SIMP_CONV (srw_ss()) (post_bool_conv@defs) ``bir_is_bool_exp ^post``;
	val thm = MP thm (SIMP_RULE std_ss [] post_bool_thm);
	val prog_typed_thm = SIMP_CONV (srw_ss()) (prog_typed_conv@defs) ``bir_is_well_typed_program ^program``;
	val thm = MP thm (SIMP_RULE std_ss [] prog_typed_thm);
	val prog_valid_thm = SIMP_CONV (srw_ss()) (prog_valid_conv@defs) ``bir_is_valid_program ^program``;
	val thm = MP thm (SIMP_RULE std_ss [] prog_valid_thm);
	val no_declare_thm = SIMP_CONV (srw_ss()) (no_declare_conv@defs) ``bir_declare_free_prog_exec ^program``;
	val thm = MP thm (SIMP_RULE std_ss [] no_declare_thm);

	val thm = GENL [var_l, var_wps, var_wps1] thm;
    in
	thm
    end;

fun proc_step1 label prog_thm (program, post, ls) defs =
    let
        val var_wps = ``wps:(bir_label_t |-> bir_exp_t)``;
        val var_wps1 = ``wps':(bir_label_t |-> bir_exp_t)``;
        val thm = SPECL [label, var_wps, var_wps1] prog_thm;

        val label_in_prog_conv = [bir_labels_of_program_def];
        val edges_blocks_in_prog_conv = [bir_edges_blocks_in_prog_exec_def, bir_targets_in_prog_exec_def, bir_get_program_block_info_by_label_def, listTheory.INDEX_FIND_def, BL_Address_HC_def];
        val l_not_in_ls_conv = [BL_Address_HC_def];

        val label_in_prog_thm = SIMP_CONV (srw_ss()) (label_in_prog_conv@defs) ``MEM ^label (bir_labels_of_program ^program)``
        val thm = MP thm (SIMP_RULE std_ss [] label_in_prog_thm);
        val edges_blocks_in_prog_thm = SIMP_CONV (srw_ss()) (edges_blocks_in_prog_conv@defs) ``bir_edges_blocks_in_prog_exec ^program ^label``;
	val thm = MP thm (SIMP_RULE std_ss [] edges_blocks_in_prog_thm);
	val l_not_in_ls_thm = SIMP_CONV (srw_ss()) (l_not_in_ls_conv@defs) ``~(^label IN ^ls)``;
	val thm = MP thm (SIMP_RULE std_ss [] l_not_in_ls_thm);

	val thm = GENL [var_wps, var_wps1] thm;
    in
        thm
    end;


(*
((proc_step2 wps wps_bool_thm wps_sound_thm) o (proc_step1 label) o proc_step0) program post ls
*)

(* wp_on_label *)
fun proc_step2 (wps, wps_bool_sound_thm) prog_l_thm ((program, post, ls), (label)) defs =
    let
        val var_wps1 = ``wps':(bir_label_t |-> bir_exp_t)``;
        val thm = SPECL [wps, var_wps1] prog_l_thm;
	val thm = MP thm (SIMP_RULE std_ss [] wps_bool_sound_thm);

(* TODO: think about / fix EVAL here *)
        val wps1_thm = EVAL ``bir_wp_exec_of_block ^program ^label ^ls ^post ^wps``;
	val wps1 = (snd o dest_comb o snd o dest_eq o concl) wps1_thm;
	val thm = SPEC wps1 (GEN var_wps1 thm);
	val wps1_bool_sound_thm = MP thm wps1_thm;
    in
	(wps1, wps1_bool_sound_thm)
    end;



(*
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




*)







(*

   ==================================== TESTING ========================================

*)



val aes_program_def = Define `
     aes_program =
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
	      ])`;


val aes_post_def = Define `
      aes_post = (BExp_BinPred BIExp_Equal (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))) (BExp_Const (Imm64 112w)))
`;

val aes_ls_def = Define `
      aes_ls = \x.(x = (BL_Address (Imm64 0x400578w)))
`;

val aes_wps_def = Define `
      aes_wps = (FEMPTY |+ (BL_Address (Imm64 0x400578w), aes_post))
`;



val program = ``aes_program``;
val post = ``aes_post``;
val ls = ``aes_ls``;
val wps = ``aes_wps``;


val wps_bool_thm = prove(``
      FEVERY (λ(l1,wp1). bir_is_bool_exp wp1) ^wps
``,

  cheat
);

val wps_sound_thm = prove(``
      FEVERY (λ(l1,wp1). (l1 IN ^ls ==> (wp1 = ^post)) /\
           ((~(l1 IN ^ls)) ==> bir_exec_to_labels_triple ^program l1 ^ls wp1 ^post)) ^wps
``,

  cheat
);

val wps_bool_sound_thm = CONJ wps_bool_thm wps_sound_thm;



val reusable_thm = bir_wp_exec_of_block_reusable_thm;
val defs = [aes_program_def, aes_post_def, aes_ls_def, aes_wps_def];
val prog_thm = proc_step0 reusable_thm (program, post, ls) defs;

(* one step label prep *)
val label = ``BL_Address_HC (Imm64 0x400574w) "F9000FE0 (str x0, [sp,#24])"``;
val prog_l_thm = proc_step1 label prog_thm (program, post, ls) defs;

(* one step wps soundness *)
val (wps1, wps1_bool_sound_thm) = proc_step2 (wps, wps_bool_sound_thm) (prog_l_thm) ((program, post, ls), (label)) defs;

val aes_wps1_def = Define `
      aes_wps1 = ^wps1
`;

val wps1_bool_sound_thm_readable = REWRITE_RULE [GSYM aes_wps1_def] wps1_bool_sound_thm;


(*
val (wps1, wps_sound1, wps_bool1) = recursive_proc program program_thm wps wps_bool_thm wps_sound_thm;
*)

