structure birs_auxLib =
struct

local

open HolKernel Parse boolLib bossLib;

open birs_auxTheory;

  (* error handling *)
  val libname = "birs_auxLib"
  val ERR = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname

in

(* ============================================================================ *)

  (* TODO: this is stolen from exec tool, better unify them later: bir_exec_auxLib *)
  fun GEN_match_conv is_tm_fun conv tm =
    if is_tm_fun tm then
      conv tm
    else if is_comb tm then
        ((RAND_CONV  (GEN_match_conv is_tm_fun conv)) THENC
         (RATOR_CONV (GEN_match_conv is_tm_fun conv))) tm
    else if is_abs tm then
        TRY_CONV (ABS_CONV (GEN_match_conv is_tm_fun conv)) tm
    else
      raise UNCHANGED
    ;

  (* TODO: this is a modified version of the above function, better unify them later *)
  fun GEN_match_extract is_tm_fun acc [] = acc
    | GEN_match_extract is_tm_fun acc (tm::l) =
    if is_tm_fun tm then
      GEN_match_extract is_tm_fun (tm::acc) l
    else if is_comb tm then
      let
        val (rator_tm, rand_tm) = dest_comb tm;
      in
        GEN_match_extract is_tm_fun acc (rand_tm::rator_tm::l)
      end
    else if is_abs tm then
        GEN_match_extract is_tm_fun acc (((snd o dest_abs) tm)::l)
    else
      GEN_match_extract is_tm_fun acc l (* raise ERR "GEN_match_extract" "unknown" *)
    ;

(* ============================================================================ *)

fun gen_prog_vars_set_thm bir_prog_def =
 let
  val prog_tm = (fst o dest_eq o concl) bir_prog_def;
  val _ = print "\ncollecting program variables";
  val timer = holba_miscLib.timer_start 0;
  val var_set_thm = 
    (REWRITE_CONV [bir_typing_progTheory.bir_vars_of_program_ALT_thm] THENC
     EVAL)
    ``bir_vars_of_program ^prog_tm``;
  val _ = holba_miscLib.timer_stop
    (fn delta_s => print (" - " ^ delta_s ^ "\n")) timer;
 in
   var_set_thm
 end;

fun gen_prog_vars_list_def_thm progname prog_vars_set_thm =
 let
  val prog_vars = (pred_setSyntax.strip_set o snd o dest_eq o concl) prog_vars_set_thm;
  (*
  List.filter ((fn s => s <> "MEM8") o (stringSyntax.fromHOLstring o fst o bir_envSyntax.dest_BVar)) prog_vars;
  *)
  val prog_vars_list_tm = listSyntax.mk_list (prog_vars, (type_of o hd) prog_vars);
  val prog_vars_list_var = mk_var(progname ^ "_prog_vars_list", type_of prog_vars_list_tm);
  val prog_vars_list_def = Define `^prog_vars_list_var = ^prog_vars_list_tm`;
  val prog_vars_thm_goal = ``set ^((fst o dest_eq o concl) prog_vars_list_def) = ^((fst o dest_eq o concl) prog_vars_set_thm)``;
 in
  prove(prog_vars_thm_goal,
    REWRITE_TAC [prog_vars_set_thm, prog_vars_list_def] >>
    SIMP_TAC (std_ss++HolBASimps.VARS_OF_PROG_ss++pred_setLib.PRED_SET_ss)
     [] >>
    EVAL_TAC)
 end;

fun gen_prog_vars_defthms progname bir_prog_def =
 let
  val prog_vars_set_thm_name = progname ^ "_prog_vars_set_thm";
  val prog_vars_set_thm = save_thm (prog_vars_set_thm_name, gen_prog_vars_set_thm bir_prog_def);
  val prog_vars_thm_name = progname ^ "_prog_vars_thm";
  val prog_vars_thm = save_thm (prog_vars_thm_name, gen_prog_vars_list_def_thm progname prog_vars_set_thm);
 in
  ()
 end;

fun gen_birenvtyl_def progname =
 let
  val prog_vars_list_tm = Parse.Term [QUOTE (progname ^ "_prog_vars_list")];
  val birenvtyl_tm = ``MAP BVarToPair ^prog_vars_list_tm``;
  val birenvtyl_var = mk_var(progname ^ "_birenvtyl", type_of birenvtyl_tm);
  val _ = Define `^birenvtyl_var = ^birenvtyl_tm`;
 in
  ()
 end;

(* val gen_prog_vars_birenvtyl_defthms : string -> thm -> unit; *)

fun gen_prog_vars_birenvtyl_defthms progname bir_prog_def =
 (gen_prog_vars_defthms progname bir_prog_def;
  gen_birenvtyl_def progname);


end (* local *)

(* ============================================================================ *)
local
  open HolKernel Parse boolLib bossLib;

  open holba_auxiliaryTheory;
  open bir_programTheory;

in
  val cur_stmt_lookup_fun = ref ((K (NONE)) : term -> thm option);
  val cur_l_mem_lookup_fun = ref ((K (NONE)) : term -> thm option);


(* ------------------------------------------------------------------------- *)

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

fun prepare_program_lookups bir_lift_thm =
let
  val _ = print "\npreparing program lookups";
  val timer = holba_miscLib.timer_start 0;
  val prep_structure = gen_exec_prep_thms_from_lift_thm bir_lift_thm;
  val (stmt_lookup_fun, l_mem_lookup_fun) = gen_lookup_functions prep_structure;
  val _ = cur_stmt_lookup_fun := stmt_lookup_fun;
  val _ = cur_l_mem_lookup_fun := l_mem_lookup_fun;
  val _ = holba_miscLib.timer_stop
    (fn delta_s => print (" - " ^ delta_s ^ "\n")) timer;
in
  ()
end;

end
(* ============================================================================ *)


end (* struct *)
