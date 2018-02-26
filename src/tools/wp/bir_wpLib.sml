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

open bir_expLib;
open finite_mapSyntax;
open pairSyntax;

load "pairLib";


structure bir_wpLib =
struct

(* establish wps_bool_sound_thm for an initial analysis context (program, post, ls, wps) *)
fun init_wps_bool_sound_thm (program, post, ls) wps defs =
      let
        val wps_bool_thm = prove(`` bir_bool_wps_map ^wps ``,
          REWRITE_TAC ([bir_bool_wps_map_def]@defs) >>
          REWRITE_TAC [finite_mapTheory.FEVERY_FUPDATE, finite_mapTheory.DRESTRICT_FEMPTY, finite_mapTheory.FEVERY_FEMPTY] >>
          SIMP_TAC (srw_ss()) [bir_is_bool_exp_def,type_of_bir_exp_def, bir_var_type_def, type_of_bir_imm_def, 
        		       bir_type_is_Imm_def, BType_Bool_def]
          );
        val wps_sound_thm = prove(``bir_sound_wps_map ^program ^ls ^post ^wps``,
          REWRITE_TAC ([bir_sound_wps_map_def]@defs) >>
          REWRITE_TAC [finite_mapTheory.FEVERY_FUPDATE, finite_mapTheory.DRESTRICT_FEMPTY, finite_mapTheory.FEVERY_FEMPTY] >>
          SIMP_TAC (srw_ss()) []
          );
      in
        CONJ wps_bool_thm wps_sound_thm
      end;



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
			    bir_mem_expTheory.bir_number_of_mem_splits_REWRS, BType_Bool_def, bir_exp_true_def, bir_exp_false_def, BExp_MSB_type_of
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

(* include current label in reasoning *)
fun proc_step1 label prog_thm (program, post, ls) defs =
    let
        val var_wps = ``wps:(bir_label_t |-> bir_exp_t)``;
        val var_wps1 = ``wps':(bir_label_t |-> bir_exp_t)``;
        val thm = SPECL [label, var_wps, var_wps1] prog_thm;

        val label_in_prog_conv = [bir_labels_of_program_def, BL_Address_HC_def];
        val edges_blocks_in_prog_conv = [bir_edges_blocks_in_prog_exec_def, bir_targets_in_prog_exec_def, bir_get_program_block_info_by_label_def, listTheory.INDEX_FIND_def, BL_Address_HC_def];
        val l_not_in_ls_conv = [BL_Address_HC_def];

        (* val label_in_prog_thm = SIMP_CONV (srw_ss()) (label_in_prog_conv@defs) ``MEM ^label (bir_labels_of_program ^program)``; *)
        val label_in_prog_thm = EVAL ``MEM ^label (bir_labels_of_program ^program)``;
        val thm = MP thm (SIMP_RULE std_ss [] label_in_prog_thm);
        val edges_blocks_in_prog_thm = SIMP_CONV (srw_ss()) (edges_blocks_in_prog_conv@defs) ``bir_edges_blocks_in_prog_exec ^program ^label``;
	val thm = MP thm (SIMP_RULE std_ss [] edges_blocks_in_prog_thm);
	val l_not_in_ls_thm = SIMP_CONV (srw_ss()) (l_not_in_ls_conv@defs) ``~(^label IN ^ls)``;
	val thm = MP thm (SIMP_RULE std_ss [] l_not_in_ls_thm);

	val thm = GENL [var_wps, var_wps1] thm;
    in
        thm
    end;


(* produce wps1 and reestablish bool_sound_thm for this one *)
fun proc_step2 (wps, wps_bool_sound_thm) prog_l_thm ((program, post, ls), (label)) defs =
    let
        val var_wps1 = ``wps':(bir_label_t |-> bir_exp_t)``;
        val thm = SPECL [wps, var_wps1] prog_l_thm;
	val thm = MP thm (SIMP_RULE std_ss [] wps_bool_sound_thm);

        val wps1_thm = EVAL ``bir_wp_exec_of_block ^program ^label ^ls ^post ^wps``;
	val wps1 = (snd o dest_comb o snd o dest_eq o concl) wps1_thm;
	val thm = SPEC wps1 (GEN var_wps1 thm);
	val wps1_bool_sound_thm = MP thm wps1_thm;
    in
	(wps1, wps1_bool_sound_thm)
    end;




(*
(* helper for simple traversal in recursive procedure *)
fun is_lbl_in_wps wps label =
    (optionSyntax.is_some o snd o dest_eq o concl o EVAL) ``FLOOKUP ^wps ^label``;
*)

fun cmp_label lbla lblb =
      let
        val strip_comment = (snd o dest_comb o concl o EVAL); (*(SIMP_CONV std_ss [BL_Address_HC_def])*)
        val lbla1 = strip_comment lbla;
        val lblb1 = strip_comment lblb;
      in
        term_eq lbla1 lblb1
      end;

(*EVAL ``BL_Address_HC b hc``*)


fun fmap_to_dom_list fmap =
      if is_fempty fmap then [] else
      let
        val (fmap1, kv) = dest_fupdate fmap;
        val k = (fst o dest_pair) kv;
      in
        (k)::(List.filter (fn k1 => not (cmp_label k1 k)) (fmap_to_dom_list fmap1))
      end;

fun init_rec_proc_jobs prog_term wps_term =
      let
        val wpsdom = fmap_to_dom_list wps_term;
        val blocks = (snd o dest_BirProgram_list) prog_term;
        fun blstodofilter block = let
                                    val (label, _, _) = dest_bir_block block;
                                  in
                                    not (List.exists (fn el => cmp_label el label) wpsdom)
                                  end;
        val blstodo = List.filter blstodofilter blocks;
      in
        (wpsdom, blstodo)
      end;

(* recursive procedure for traversing the control flow graph *)
fun recursive_proc prog_thm ((wps, wps_bool_sound_thm), (wpsdom, blstodo)) (program, post, ls) defs =
    let
	val block = List.find (fn block =>
	      let
                  val (label, _, end_statement) = dest_bir_block block;
		  (*val label = (snd o dest_eq o concl o EVAL) label;*)
                  fun is_lbl_in_wps lbl = List.exists (fn el => cmp_label el lbl) wpsdom;
	      in
                  (*(not (is_lbl_in_wps wps label))
                  andalso*)
		  (not (is_BStmt_Halt end_statement))
                  andalso
                  (
                    ((is_BStmt_Jmp end_statement) andalso (
		      (is_lbl_in_wps o dest_BLE_Label o dest_BStmt_Jmp) end_statement
                    ))
                  orelse
		    ((is_BStmt_CJmp end_statement) andalso (
		      (((is_lbl_in_wps o dest_BLE_Label o #2 o dest_BStmt_CJmp) end_statement) andalso ((is_lbl_in_wps o dest_BLE_Label o #3 o dest_BStmt_CJmp) end_statement))
                    ))
                  )
	      end)
            blstodo
    in
      case block of 
          SOME (bl) => 
                let
                  val (label, _, _) = dest_bir_block bl;
                  val _ = if (!debug_trace > 1) then
                            print ("starting with block: " ^ (term_to_string label) ^ "\r\n")
                          else
                            ()
                          ;

                  val time_start = Time.now ();

                  val prog_l_thm = proc_step1 label prog_thm (program, post, ls) defs;
                  val (wps1, wps1_bool_sound_thm) = proc_step2 (wps, wps_bool_sound_thm) prog_l_thm ((program, post, ls), (label)) defs;
                  val blstodo1 = List.filter (fn block =>
                        let
                          val (label_el, _, _) = dest_bir_block block;
                        in
                          not (cmp_label label label_el)
                        end) blstodo;
                  val wpsdom1 = label::wpsdom;

                  val _ = if (!debug_trace > 2) then
                            let
                              val wp_exp_term = (snd o dest_comb o concl o EVAL) ``(FAPPLY ^wps1 ^label)``;
                              val _ = bir_exp_pretty_print wp_exp_term;
                            in
                              ()
                            end
                          else
                            ()
                          ;

                  val _ = if (!debug_trace > 1) then
                            print ("finished block: " ^ (term_to_string label) ^ "\r\n")
                          else
                            ()
                          ;

                  val _ = if (!debug_trace > 1) then
                            print ("it took " ^ (LargeInt.toString (Time.toSeconds ((Time.now ()) - time_start))) ^ "s\r\n\r\n")
                          else
                            ()
                          ;
                in
                  (* recursive call with new wps tuple *)
                  (*(wps1, wps1_bool_sound_thm)*)
                  recursive_proc prog_thm ((wps1, wps1_bool_sound_thm), (wpsdom1, blstodo1)) (program, post, ls) defs
                end
        | _ => (wps, wps_bool_sound_thm)
    end;






end
