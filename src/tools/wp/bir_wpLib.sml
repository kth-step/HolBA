(* For compilation *)
open HolKernel boolLib liteLib simpLib Parse bossLib;

(* Local *)
open bir_wpTheory bir_wp_simpTheory;

(* From /core: *)
open bir_programTheory bir_typing_progTheory bir_envTheory
     bir_auxiliaryTheory bir_valuesTheory bir_expTheory
     bir_exp_memTheory bir_immTheory;
open bir_programSyntax;

(* From /theories: *)
open bir_program_blocksTheory bir_program_terminationTheory
     bir_exp_substitutionsTheory bir_bool_expTheory
     bir_program_env_orderTheory bir_extra_expsTheory
     bir_nzcv_expTheory bir_program_valid_stateTheory;

(* From /libs: *)
open bir_expLib;

structure bir_wpLib =
struct

(* TODO: Replace all expressions in double hyphens by syntactic
 *       functions.
 *
 * Local syntax function library should contain:
 * bir_bool_wps_map, bir_sound_wps_map, *)
(* Establish wps_bool_sound_thm for an initial analysis context *)
fun bir_wp_init_wps_bool_sound_thm (program, post, ls) wps defs =
  let
    fun REPEAT_MAX n tac =
      if n > 0
      then ((tac THEN (REPEAT_MAX (n - 1) tac)) ORELSE ALL_TAC)
      else NO_TAC
    val wps_bool_thm = prove(``bir_bool_wps_map ^wps``,
      REWRITE_TAC ([bir_bool_wps_map_def]@defs) >>
      REPEAT_MAX 20 (
        REWRITE_TAC [finite_mapTheory.FEVERY_FUPDATE,
                     finite_mapTheory.DRESTRICT_FEMPTY,
                     finite_mapTheory.FEVERY_FEMPTY] >>
        SIMP_TAC (srw_ss()) [bir_is_bool_exp_def,
                             type_of_bir_exp_def,
                             bir_var_type_def, type_of_bir_imm_def, 
                             bir_type_is_Imm_def, BType_Bool_def]
      )
    )
    val wps_sound_thm =
      prove(``bir_sound_wps_map ^program ^ls ^post ^wps``,
      REWRITE_TAC ([bir_sound_wps_map_def]@defs) >>
      REPEAT_MAX 20 (
        REWRITE_TAC [finite_mapTheory.FEVERY_FUPDATE,
                     finite_mapTheory.DRESTRICT_FEMPTY,
                     finite_mapTheory.FEVERY_FEMPTY] >>
        SIMP_TAC (srw_ss()) []
      )
    )
  in
    CONJ wps_bool_thm wps_sound_thm
  end;

(* initial_thm_for_prog_post_ls *)
fun bir_wp_comp_wps_iter_step0_init reusable_thm (program, post, ls)
                                    defs =
  let
    val var_l = mk_var("l", bir_label_t_ty)
    val var_wps =
      mk_var("wps", finite_mapSyntax.mk_fmap_ty(bir_label_t_ty,
                                                bir_exp_t_ty)
            )
    val var_wps1 =
      mk_var("wps'", finite_mapSyntax.mk_fmap_ty(bir_label_t_ty,
                                                 bir_exp_t_ty)
            )
    val thm = SPECL [program, var_l, ls, post, var_wps, var_wps1]
                    reusable_thm
    (* TODO: Redefining these convs every call is not part of
     *       computation, so these should be placed externally... *)
    val post_bool_conv = [bir_is_bool_exp_def, type_of_bir_exp_def,
                          bir_var_type_def, type_of_bir_imm_def, 
                          bir_type_is_Imm_def, BType_Bool_def]
    val prog_typed_conv = [bir_is_well_typed_program_def,
                           bir_is_well_typed_block_def,
                           bir_is_well_typed_stmtE_def,
                           bir_is_well_typed_stmtB_def,
                           bir_is_well_typed_label_exp_def,
                           type_of_bir_exp_def, bir_var_type_def,
                           bir_type_is_Imm_def, type_of_bir_imm_def,
                           BExp_Aligned_type_of,
                           BExp_unchanged_mem_interval_distinct_type_of,
                           bir_number_of_mem_splits_REWRS,
                           BType_Bool_def,
                           bir_exp_true_def,
                           bir_exp_false_def, BExp_MSB_type_of,
                           BExp_nzcv_ADD_DEFS,
                           BExp_nzcv_SUB_DEFS,
                           n2bs_def, BExp_word_bit_def,
                           BExp_Align_type_of, BExp_ror_type_of,
                           BExp_LSB_type_of,
                           BExp_word_bit_exp_type_of,
                           BExp_ADD_WITH_CARRY_type_of,
                           BExp_word_reverse_type_of,
                           BExp_ror_exp_type_of]
    val prog_valid_conv = [bir_is_valid_program_def,
                           bir_program_is_empty_def,
                           bir_is_valid_labels_def,
                           bir_labels_of_program_def,
                           BL_Address_HC_def]
    val no_declare_conv = [bir_declare_free_prog_exec_def,
                           bir_isnot_declare_stmt_def]

    (* TODO: Create bir_is_bool_expSyntax for the below *)
    val post_bool_thm = SIMP_CONV (srw_ss()) (post_bool_conv@defs)
                                  ``bir_is_bool_exp ^post``
    val thm = MP thm (SIMP_RULE std_ss [] post_bool_thm)
    (* TODO: Make bir_typing_progSyntax *)
    val prog_typed_thm = SIMP_CONV (srw_ss()) (prog_typed_conv@defs)
      ``bir_is_well_typed_program ^program``
    val thm = MP thm (SIMP_RULE std_ss [] prog_typed_thm)
    (*val prog_valid_thm = SIMP_CONV (srw_ss()) (prog_valid_conv@defs) ``bir_is_valid_program ^program``;*)
    (* TODO: Make bir_program_valid_stateSyntax *)
    val prog_valid_thm = EVAL ``bir_is_valid_program ^program``
    val thm = MP thm (SIMP_RULE std_ss [] prog_valid_thm)
    (* TODO: Make bir_wpSyntax *)
    val no_declare_thm = SIMP_CONV (srw_ss()) (no_declare_conv@defs)
      ``bir_declare_free_prog_exec ^program``
    val thm = MP thm (SIMP_RULE std_ss [] no_declare_thm)

    val thm = GENL [var_l, var_wps, var_wps1] thm
  in
    thm
  end;

(* Include current label in reasoning *)
fun bir_wp_comp_wps_iter_step1 label prog_thm (program, post, ls)
                               defs =
  let
    val var_wps =
      mk_var("wps", finite_mapSyntax.mk_fmap_ty(bir_label_t_ty,
                                                bir_exp_t_ty)
            )
    val var_wps1 =
      mk_var("wps'", finite_mapSyntax.mk_fmap_ty(bir_label_t_ty,
                                                 bir_exp_t_ty)
            )
    val thm = SPECL [label, var_wps, var_wps1] prog_thm

    val label_in_prog_conv =
      [bir_labels_of_program_def, BL_Address_HC_def]
    val edges_blocks_in_prog_conv =
      [bir_edges_blocks_in_prog_exec_def,
       bir_targets_in_prog_exec_def,
       bir_get_program_block_info_by_label_def,
       listTheory.INDEX_FIND_def, BL_Address_HC_def]
    val l_not_in_ls_conv = [BL_Address_HC_def]

    (* val label_in_prog_thm =
     *   SIMP_CONV (srw_ss()) (label_in_prog_conv@defs)
     *   ``MEM ^label (bir_labels_of_program ^program)``; *)
    (* TODO: Use mk_mem in listSyntax, and add
     * bir_labels_of_program to syntax functions in
     * bir_programSyntax (bir_exec_blockLib has some redundant
     * functions which should be moved) *)
    val label_in_prog_thm =
      EVAL (
        listSyntax.mk_mem (label,
                           ``bir_labels_of_program ^program``
                          )
      )
    val thm = MP thm (SIMP_RULE std_ss [] label_in_prog_thm)
    (*val edges_blocks_in_prog_thm = SIMP_CONV (srw_ss()) (edges_blocks_in_prog_conv@defs) ``bir_edges_blocks_in_prog_exec ^program ^label``;*)
    (* TODO: Add to bir_wpSyntax. *)
    val edges_blocks_in_prog_thm =
      EVAL ``bir_edges_blocks_in_prog_exec ^program ^label``
    val thm = MP thm (SIMP_RULE std_ss [] edges_blocks_in_prog_thm)
    val l_not_in_ls_thm =
      SIMP_CONV (srw_ss()) (l_not_in_ls_conv@defs)
                (mk_neg (mk_IN (label, ls)))
    val thm = MP thm (SIMP_RULE std_ss [] l_not_in_ls_thm)

    val thm = GENL [var_wps, var_wps1] thm
  in
    thm
  end;

fun extract_new_wp fmterm =
  (snd o pairSyntax.dest_pair o snd o finite_mapSyntax.dest_fupdate)
    fmterm;
val lbl_strip_comment = (snd o dest_comb o concl o EVAL);

val bir_wp_comp_wps_iter_step2_defs = ref ([]:thm list);
val bir_wp_comp_wps_iter_step2_consts = ref ([]:term list);
val bir_wp_comp_wps_iter_step2_cntr = ref 0;

(* produce wps1 and reestablish bool_sound_thm for this one *)
fun bir_wp_comp_wps_iter_step2 (wps, wps_bool_sound_thm) prog_l_thm
                               ((program, post, ls), (label)) defs =
  let
(*
        val wps_id_idx = !bir_wp_comp_wps_iter_step2_cntr;
        val _ = (bir_wp_comp_wps_iter_step2_cntr :=
                  (!bir_wp_comp_wps_iter_step2_cntr) + 1);
        val wps_id_suffix = Int.toString wps_id_idx;
*)
    val wps_id_suffix =
      (term_to_string o snd o gen_dest_Imm o dest_BL_Address o
         lbl_strip_comment
      ) label

    (* TODO: Constant, move out of function. *)
    val var_wps1 =
      mk_var("wps'", finite_mapSyntax.mk_fmap_ty(bir_label_t_ty,
                                                 bir_exp_t_ty)
            )
    val thm = SPECL [wps, var_wps1] prog_l_thm

    (* this took a while, it should not have been?! *)
    val thm = MP thm wps_bool_sound_thm

    (* this takes a bit, not anymore? *)
    val wps_eval_restrict_consts =
      !bir_wp_comp_wps_iter_step2_consts;
    val wps1_thm =
      computeLib.RESTR_EVAL_CONV wps_eval_restrict_consts
        (list_mk_comb
          (* TODO: Add to bir_wpSyntax *)
          (``bir_wp_exec_of_block:'a bir_program_t ->
               bir_label_t ->
               (bir_label_t -> bool) ->
               bir_exp_t ->
               (bir_label_t |-> bir_exp_t) ->
               (bir_label_t |-> bir_exp_t) option``,
           [program, label, ls, post, wps]
          )
        )
    val wps1_thm = SIMP_RULE pure_ss [GSYM bir_exp_subst1_def,
                                      GSYM bir_exp_and_def]
                                     wps1_thm; (* normalize *)
    val wps1 = (snd o dest_comb o snd o dest_eq o concl) wps1_thm
    val new_wp_id = "bir_wp_comp_wps_iter_step2_wp_"^wps_id_suffix
    val new_wp_id_var = mk_var (new_wp_id, bir_exp_t_ty)
    val new_wp_def =
      Define `^new_wp_id_var = ^(extract_new_wp wps1)`
        (*
        val current_theory_s = current_theory();
        val new_wp_id_const = mk_const (new_wp_id, ``:bir_exp_t``);
        *)
    val new_wp_id_const = (fst o dest_eq o concl) new_wp_def
    val _ = (bir_wp_comp_wps_iter_step2_consts :=
               new_wp_id_const::wps_eval_restrict_consts
            );
    val wps1_thm2 = REWRITE_CONV [GSYM new_wp_def]
                                 ((snd o dest_eq o concl) wps1_thm)
    val wps1_thm = TRANS wps1_thm wps1_thm2
    val wps1 = (snd o dest_comb o snd o dest_eq o concl) wps1_thm

    val thm = SPEC wps1 (GEN var_wps1 thm)
    val wps1_bool_sound_thm = MP thm wps1_thm
  in
    (wps1, wps1_bool_sound_thm)
  end;

(*
(* helper for simple traversal in recursive procedure *)
fun is_lbl_in_wps wps label =
    (optionSyntax.is_some o snd o dest_eq o concl o EVAL)
    ``FLOOKUP ^wps ^label``;
*)

fun cmp_label lbla lblb =
  let
    val lbla1 = lbl_strip_comment lbla
    val lblb1 = lbl_strip_comment lblb
  in
    term_eq lbla1 lblb1
  end;

(*EVAL ``BL_Address_HC b hc``*)

fun bir_wp_fmap_to_dom_list fmap =
  if finite_mapSyntax.is_fempty fmap then [] else
  let
    val (fmap1, kv) = finite_mapSyntax.dest_fupdate fmap
    val k = (fst o pairSyntax.dest_pair) kv
  in
    (k)::(List.filter (fn k1 => not (cmp_label k1 k))
                      (bir_wp_fmap_to_dom_list fmap1)
         )
  end;

fun bir_wp_init_rec_proc_jobs prog_term wps_term =
  let
    val wpsdom = bir_wp_fmap_to_dom_list wps_term
    val blocks = (snd o dest_BirProgram_list) prog_term
    fun blstodofilter block =
      let
        val (label, _, _) = dest_bir_block block
      in
        not (List.exists (fn el => cmp_label el label) wpsdom)
      end;
    val blstodo = List.filter blstodofilter blocks
  in
    (wpsdom, blstodo)
  end;

(* Recursive procedure for traversing the control flow graph *)
fun bir_wp_comp_wps prog_thm ((wps, wps_bool_sound_thm),
                              (wpsdom, blstodo)
                             ) (program, post, ls) defs =
  let
    val block = List.find (fn block =>
      let
        val (label, _, end_statement) = dest_bir_block block
        (*val label = (snd o dest_eq o concl o EVAL) label;*)
        fun is_lbl_in_wps lbl =
          List.exists (fn el => cmp_label el lbl) wpsdom
      in
        (*(not (is_lbl_in_wps wps label))
          andalso*)
        (not (is_BStmt_Halt end_statement))
        andalso
        (
          (
            (is_BStmt_Jmp end_statement)
            andalso
            ((is_lbl_in_wps o dest_BLE_Label o dest_BStmt_Jmp)
               end_statement
            )
          )
          orelse
          (
            (is_BStmt_CJmp end_statement)
            andalso
            (
              (
                (
                  (is_lbl_in_wps o dest_BLE_Label o #2 o
                    dest_BStmt_CJmp
                  ) end_statement
                )
                andalso
                (
                  (is_lbl_in_wps o dest_BLE_Label o #3 o
                    dest_BStmt_CJmp
                  ) end_statement
                )
              )
            )
          )
        )
      end
    ) blstodo
  in
    case block of 
      SOME (bl) => 
        let
          val (label, _, _) = dest_bir_block bl

          val _ = if (!debug_trace > 1)
                  then print ("\n\r\nstarting with block: "^
                              (term_to_string label)^"\r\n")
                  else ();

          val time_start = Time.now ();

          val prog_l_thm =
            bir_wp_comp_wps_iter_step1 label prog_thm
                                       (program, post, ls) defs
          val (wps1, wps1_bool_sound_thm) =
            bir_wp_comp_wps_iter_step2 (wps, wps_bool_sound_thm)
                                       prog_l_thm
                                       ((program, post, ls),
                                        (label)
                                       ) defs
          val blstodo1 =
            List.filter (
              fn block =>
                let
                  val (label_el, _, _) = dest_bir_block block;
                in
                  not (cmp_label label label_el)
                end
            ) blstodo
          val wpsdom1 = label::wpsdom

          val _ = if (!debug_trace > 2)
                  then
                    let
                      val wp_exp_term =
                        (snd o dest_comb o concl o EVAL)
                          (finite_mapSyntax.mk_fapply
                            (wps1, label)
                          );
                      val _ = bir_exp_pretty_print wp_exp_term;
                    in
                      ()
                    end
                  else ();

          val _ = if (!debug_trace > 1)
                  then print ("It took "^
                              (LargeInt.toString (
                                Time.toSeconds ((Time.now ()) -
                                                time_start
                                               )
                               )
                              )^"s\r\n"
                             )
                  else ();

          val _ = if (!debug_trace > 0)
                  then print ("Remaining = "^
                              (Int.toString (List.length blstodo1))^
                              "  \r"
                             )
                  else ();
        in
          bir_wp_comp_wps prog_thm ((wps1, wps1_bool_sound_thm),
                                    (wpsdom1, blstodo1)
                                   ) (program, post, ls) defs
        end
    | _ =>
      let
        val _ = if (!debug_trace > 0)
                then print ("\n")
                else ();
      in
        (wps, wps_bool_sound_thm)
      end
  end;
end
