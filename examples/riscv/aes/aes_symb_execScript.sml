open HolKernel Parse boolLib bossLib;

open wordsTheory;

open bir_symbLib;

open aesTheory aes_specTheory;

val _ = new_theory "aes_symb_exec";

(* ------------------------------------------------------------------------- *)

Definition SPLIT_ELs_def:
  (SPLIT_ELs _ []      _ = T) /\
  (SPLIT_ELs l (h::t)  i = ((EL i l = h) /\ (SPLIT_ELs l t (i + 1))))
End

Theorem SPLIT_ELs_GEN_thm:
!i h x t.
  SPLIT_ELs t x i =
  SPLIT_ELs (h::t) x (i + 1)
Proof
  Induct_on ‘x’ >> (
    gs [SPLIT_ELs_def]
  ) >>
  rpt strip_tac >>
  POP_ASSUM ((fn t => REWRITE_TAC [Once t]) o Q.SPECL [‘i+1’, ‘h'’, ‘t’]) >>
  gs [] >>
  REWRITE_TAC [GSYM arithmeticTheory.ADD1, listTheory.EL, listTheory.TL]
QED

Theorem SPLIT_ELs_0_thm:
!l. SPLIT_ELs l l 0
Proof
  Induct >> (
    gs [SPLIT_ELs_def]
  ) >>
  ASM_REWRITE_TAC [(GSYM o EVAL_RULE o Q.SPEC ‘0’) SPLIT_ELs_GEN_thm]
QED

Definition bir_get_blocks_def:
  bir_get_blocks (BirProgram p) = p
End

Theorem bir_get_blocks_INV_thm:
!p. BirProgram (bir_get_blocks p) = p
Proof
  Cases >> rw [bir_get_blocks_def]
QED

Theorem bir_get_blocks_labels_length_thm:
!p. LENGTH (bir_labels_of_program p) = LENGTH (bir_get_blocks p)
Proof
  Cases >>
  gs [bir_get_blocks_def, bir_programTheory.bir_labels_of_program_def]
QED

Theorem bir_get_blocks_labels_EL_thm:
!p i.
  (i < LENGTH (bir_get_blocks p)) ==>
  EL i (bir_labels_of_program p) = (EL i (bir_get_blocks p)).bb_label
Proof
  Cases >>
  gs [bir_get_blocks_def, bir_programTheory.bir_labels_of_program_def, listTheory.EL_MAP]
QED

(*
val list_tm = bprog_l_tm;
val restr_consts = [bprog_tm];
*)
fun get_el_thms list_tm restr_consts =
  let
    val split_el_inst_thm = ISPEC list_tm SPLIT_ELs_0_thm;
    val split_conj_thm = CONV_RULE (RATOR_CONV (RAND_CONV EVAL) THENC computeLib.RESTR_EVAL_CONV (listSyntax.el_tm::restr_consts)) split_el_inst_thm;
  in
    (CONJUNCTS split_conj_thm,
     EVAL (listSyntax.mk_length list_tm))
  end;

(* ------------------------------------------------------------------------- *)

(*
open bir_block_collectionLib;

(* bir_is_valid_program - bir_program_valid_stateTheory.bir_is_valid_program_def *)
(* bir_is_valid_labels <- bir_inst_liftingTheory.bir_is_lifted_prog_def *)
val valid_prog_thm = bir_exec_typingLib.bir_exec_valid_prog prog_l_def;

fun gen_block_thm_map prog_l_def valid_prog_thm = gen_MEM_thm_block_dict prog_l_def valid_prog_thm;

val n = (Arbnum.toInt o numSyntax.dest_numeral o snd o dest_eq o concl o EVAL) (listSyntax.mk_length prog_l_tm);
fun mk_EL_tm i =
  listSyntax.mk_el (numSyntax.term_of_int i, prog_l_tm);

fun dothisnow () =
  let
val abc = EVAL (mk_EL_tm (n-1));
  in () end;

List.tabulate(n, fn i => dothisnow ())

boolTheory.EQ_CLAUSES
*)

(*
val valid_prog_thm = prove(“
  bir_is_valid_program ^bprog_tm
”,
(*
bir_is_valid_labels p + NOT (bir_program_is_empty p)
== bir_program_valid_stateTheory.bir_is_valid_program_def
*)
  REWRITE_TAC [bir_program_valid_stateTheory.bir_is_valid_program_def] >>
  REWRITE_TAC [REWRITE_RULE [bir_inst_liftingTheory.bir_is_lifted_prog_def] bir_lift_thm] >>
  EVAL_TAC
);
*)

(*
val block_thm = hd block_thms;
*)

fun dest_block_thm block_thm =
  let
    val block_thm_tm = concl block_thm;
    val i_tm = (fst o listSyntax.dest_el o fst o dest_eq) block_thm_tm;
    val block_tm = (snd o dest_eq) block_thm_tm;
    val (l_tm,stmts_tm,_) = bir_programSyntax.dest_bir_block block_tm;
  in
    (i_tm, block_tm, l_tm, stmts_tm)
  end;

val bir_get_program_block_info_by_label_tm = “bir_get_program_block_info_by_label”;
fun gen_stmt_thms bprog_tm prog_length_thm bir_get_block_GEN_thm block_thm =
  let
    val (i_tm, block_tm, l_tm, stmts_tm) = dest_block_thm block_thm;
    val n_stmts = ((length o fst o listSyntax.dest_list) stmts_tm) + 1;
    val inst_thm1 = SPECL [l_tm, i_tm, block_tm] bir_get_block_GEN_thm;
    val inst_thm2 = CONV_RULE (RAND_CONV (REWRITE_CONV [block_thm, prog_length_thm] THENC EVAL)) inst_thm1;
    val inst_thm3 = REWRITE_RULE [] inst_thm2;

    val pc_tms = List.tabulate(n_stmts, fn i => bir_programSyntax.mk_bir_programcounter (l_tm, numSyntax.term_of_int i));
    (* val pc_tm = hd pc_tms; *)
    fun gen_stmt_thm pc_tm =
      let
        val inst_s_thm0 = ISPECL [bprog_tm, pc_tm] bir_programTheory.bir_get_current_statement_def;
        val inst_s_thm1 = CONV_RULE (RAND_CONV (computeLib.RESTR_EVAL_CONV [bprog_tm, bir_get_program_block_info_by_label_tm] THENC REWRITE_CONV [inst_thm3] THENC EVAL)) inst_s_thm0;
      in
        (pc_tm, inst_s_thm1)
      end;
  in
    map gen_stmt_thm pc_tms
  end;

fun gen_exec_prep_thms bprog_tm valid_labels_thm =
let
  val bprog_l_tm = “bir_get_blocks ^bprog_tm”;

  val (block_thms, prog_length_thm) = get_el_thms bprog_l_tm [bprog_tm];

  val bir_get_block_GEN_thm =
    REWRITE_RULE [bir_get_blocks_INV_thm]
      (MATCH_MP
        (CONJUNCT2 bir_program_valid_stateTheory.bir_get_program_block_info_by_label_valid_THM)
        valid_labels_thm);

  val stmt_thms = List.concat (map (gen_stmt_thms bprog_tm prog_length_thm bir_get_block_GEN_thm) block_thms);

  val label_idx_tms = List.map ((fn (i_tm, _, l_tm, _) => (l_tm, i_tm)) o dest_block_thm) block_thms;
    
  val label_tms = List.map fst label_idx_tms;
  (*val l_tm = last label_tms;*)
  fun gen_label_mem_thm l_tm =
    let
      val block_idx_tm = case List.find (identical l_tm o fst) label_idx_tms of SOME x => snd x | _ => raise Feedback.mk_HOL_ERR "" "gen_exec_prep_thms::gen_label_mem_thm" "this should not happen";
      val labels_tm = bir_programSyntax.mk_bir_labels_of_program bprog_tm;
      val length_thm = (REWRITE_CONV [bir_get_blocks_labels_length_thm, prog_length_thm] THENC EVAL) (numSyntax.mk_less (block_idx_tm, listSyntax.mk_length labels_tm));
      val helper_thm = REWRITE_RULE [GSYM bir_get_blocks_labels_length_thm, length_thm] (ISPECL [bprog_tm, block_idx_tm] bir_get_blocks_labels_EL_thm);

      val eval_tm = listSyntax.mk_mem (l_tm, labels_tm);
      val mem_el_thm = REWRITE_CONV [listTheory.MEM_EL] eval_tm;
      val exists_tm = (snd o dest_eq o concl) mem_el_thm;
      val exists_inst_tm = ((subst [``n:num`` |-> block_idx_tm] o snd o dest_exists) exists_tm);
      val inst_idx_thm = (REWRITE_CONV (length_thm::helper_thm::block_thms) THENC EVAL) exists_inst_tm;
      val gen_thm = EXISTS (exists_tm, block_idx_tm) (REWRITE_RULE [] inst_idx_thm);
      val label_mem_thm = REWRITE_RULE [gen_thm] mem_el_thm;
    in
      (l_tm, label_mem_thm)
    end;
  val label_mem_thms = List.map gen_label_mem_thm label_tms;
in
  (stmt_thms, label_mem_thms)
end;

fun gen_exec_prep_thms_from_lift_thm bir_lift_thm =
let
  val bprog_tm = (snd o dest_comb o concl) bir_lift_thm;
  val bprog_l_tm = “bir_get_blocks ^bprog_tm”;
  val valid_labels_thm = prove(“
      bir_is_valid_labels (BirProgram ^bprog_l_tm)
    ”,
      REWRITE_TAC [bir_get_blocks_INV_thm] >>
      REWRITE_TAC [REWRITE_RULE [bir_inst_liftingTheory.bir_is_lifted_prog_def] bir_lift_thm]
    );
in
  gen_exec_prep_thms bprog_tm valid_labels_thm
end;

(*
val (stmt_thms, label_mem_thms) = prep_structure;
*)
fun gen_lookup_functions (stmt_thms, label_mem_thms) =
  let
    val stmt_map = Redblackmap.insertList (Redblackmap.mkDict Term.compare, stmt_thms);
    val l_mem_map = Redblackmap.insertList (Redblackmap.mkDict Term.compare, label_mem_thms);
    fun lookup_fun m k = 
      SOME (Redblackmap.find (m, k))
      handle NotFound => NONE;
  in
    (lookup_fun stmt_map, lookup_fun l_mem_map)
  end;

(* ------------------------------------------------------------------------- *)

(* patch for lifter theorem *)
val bir_lift_thm = (REWRITE_RULE [] o CONV_RULE (RATOR_CONV (RAND_CONV EVAL)) o DISCH_ALL) bir_aes_riscv_lift_THM;
(*val bprog_tm = (fst o dest_eq o concl) bir_aes_prog_def;*)

val prep_structure = Profile.profile "gen_exec_prep_thms" gen_exec_prep_thms_from_lift_thm bir_lift_thm;
val (stmt_lookup_fun, l_mem_lookup_fun) = gen_lookup_functions prep_structure;
val _ = birs_stepLib.cur_stmt_lookup_fun := stmt_lookup_fun;
val _ = birs_stepLib.cur_l_mem_lookup_fun := l_mem_lookup_fun;

(*
Profile.profile "mkELtm" 
val _ = Profile.reset_all ();
val _ = Profile.print_profile_results (Profile.results ());
*)


(* --------------------------- *)
(* Symbolic analysis execution *)
(* --------------------------- *)

val (bsysprecond_thm, symb_analysis_thm) =
 bir_symb_analysis_thm
  bir_aes_prog_def
  aes_init_addr_def [aes_end_addr_def]
(*  aes_init_addr_def [aes_end1_addr_def,aes_end2_addr_def]*)
(*  aes_init_addr_def [aes_end1_addr_def]*)
  bspec_aes_pre_def aes_birenvtyl_def;

val _ = show_tags := true;

val _ = Portable.pprint Tag.pp_tag (tag bsysprecond_thm);

Theorem aes_bsysprecond_thm = bsysprecond_thm

val _ = Portable.pprint Tag.pp_tag (tag symb_analysis_thm);

Theorem aes_symb_analysis_thm = symb_analysis_thm

val _ = export_theory ();
