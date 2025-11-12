structure birs_armcm0_supportLib =
struct

local

  open HolKernel Parse boolLib bossLib;

  open birsSyntax;

  open birs_utilsLib;

  (* error handling *)
  val libname = "birs_armcm0_supportLib"
  val ERR = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname

in (* local *)

  val bir_countw_bvar_tm = ``BExp_Den (BVar "countw" (BType_Imm Bit64))``;
  val bir_sp_bvar_tm = ``BExp_Den (BVar "SP_process" (BType_Imm Bit32))``;

  fun bir_const64 v = ``BExp_Const (Imm64 ^(wordsSyntax.mk_wordii(v, 64)))``;
  fun bir_const32 v = ``BExp_Const (Imm32 ^(wordsSyntax.mk_wordii(v, 32)))``;
  fun mk_countw_plus tm v = bslSyntax.bplus (tm, bir_const64 v);

  val bir_countw_hvar_tm = ``BExp_Const (Imm64 pre_countw)``;
  val bir_hvar_cond = bslSyntax.beq (bir_countw_bvar_tm, bir_countw_hvar_tm);

(* -------------------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)

  (* TODO: how much space do we actually have? we should "enforce" this with the linker... *)
  val mem_ram_start = 0x20000000;
  val mem_ram_size  = 0x2000;
  val mem_ram_stack_sz = 0x200;
  val stack_start = mem_ram_start + mem_ram_size - 16;
  val stack_end   = mem_ram_start + mem_ram_size - mem_ram_stack_sz;

  (* TODO: need to fix this to handlermode -> needs change of the used lifter machine *)
  val pred_not_handlermode =
  ``BExp_UnaryExp BIExp_Not (BExp_Den (BVar "ModeHandler" BType_Bool))``;

  val alt_sp_bvar_tm = ref (NONE:term option);
  fun get_bir_sp_bvar_tm () =
    let
      val bv_tm_o = !alt_sp_bvar_tm;
    in
      if isSome bv_tm_o then
        valOf bv_tm_o
      else
        bir_sp_bvar_tm
    end;

  fun pred_sp_aligned () =
  ``BExp_BinPred BIExp_Equal
      (BExp_BinExp BIExp_And
          (^(get_bir_sp_bvar_tm()))
          (BExp_Const (Imm32 3w)))
      (BExp_Const (Imm32 0w))``;

  fun pred_sp_space_req (sp_offset, stack_space_req) =
  let
    val bv_tm = get_bir_sp_bvar_tm();
    val sp_exp_tm =
      if sp_offset = 0 then
        bv_tm
      else
        bslSyntax.bplus(bv_tm, bir_const32 (~sp_offset));
  in
    ``BExp_BinExp BIExp_And
              (BExp_BinPred BIExp_LessOrEqual
                ^(bir_const32 (stack_end + stack_space_req))
                ^sp_exp_tm)
              (BExp_BinPred BIExp_LessOrEqual
                ^sp_exp_tm
                ^(bir_const32 (stack_start)))``
  end;

  fun pred_countw_space_req countw_space_req =
  ``BExp_BinPred BIExp_LessOrEqual
       ^bir_countw_bvar_tm
       ^(bir_const64 (0x10000000 - countw_space_req))``;

  val pred_conjs_extra_tm = ref (NONE:term option)
  fun pred_conjs ((sp_offset, stack_space_req), countw_space_req) =
    [pred_not_handlermode, (* needed for bx lr instructions *)
     pred_sp_aligned ()]@
    (if stack_space_req = 0 then [] else
       [pred_sp_space_req (sp_offset, stack_space_req)])@
    [pred_countw_space_req countw_space_req]@
    (let
       val extra_tm_o = !pred_conjs_extra_tm;
     in
       if isSome extra_tm_o then [valOf extra_tm_o] else []
     end);

(* -------------------------------------------------------------------------- *)

local
  open bir_immSyntax;
  fun mk_word_addr v = wordsSyntax.mk_wordii(v, 32);
  fun mk_bir_lbl x = ``bir_block_pc (BL_Address ^(gen_mk_Imm x))``;
in
  val bir_lbl_from_addr = snd o dest_eq o concl o EVAL o mk_bir_lbl o mk_word_addr;
end



  val _ = birs_simp_instancesLib.simp_thms_tuple_subexp_extra :=
    [bir_symb_simpTheory.birs_simplification_Store_mem_thm,
    bir_symb_simpTheory.birs_simplification_Store_val_thm,
    bir_symb_simpTheory.birs_simplification_Store_addr_thm];
  val birs_simp_default_core_exp_multistoreelim_plus_cm0_simp =
    let
      val include_64 = true;
      val include_32 = true;
      val mem_64 = false;
      val mem_32 = true;
      val riscv = false;
      val cm0 = true;
    in
      birs_simp_instancesLib.birs_simp_gen
        birs_simpLib.birs_simp_ID_fun
        []
        (birs_simp_instancesLib.simp_thms_tuple include_64 include_32 mem_64 mem_32 riscv cm0 [])
        (birs_simp_instancesLib.load_thms_tuple mem_64 mem_32)
        (SOME true)
    end;

(* need to cleanup environment after instantiation *)
fun cleanup_environment_thoroughly thm =
  let
    val bprog_tm = (birsSyntax.get_birs_prog o concl) thm;
    val birs_rule_SUBST_thm = birs_execLib.birs_rule_SUBST_prog_fun bprog_tm;
    val birs_simp_RULE_gen = birs_execLib.birs_rule_SUBST_trysimp_fun birs_rule_SUBST_thm;
    val birs_simp_select = birs_simp_default_core_exp_multistoreelim_plus_cm0_simp;

    val _ = print "post instantiation code runs now\n";
    (* turn on before simplification, turn off afterwards *)
    val _ = birs_simp_instancesLib.birs_simp_regular_recurse_mode := true;
    val _ = birs_simp_instancesLib.birs_simp_regular_recurse_depth := 10;
    (* go through the first Pi state (only one for summaries, could generalize here even to all Pi states) and cleanup by simplification *)
    (* only MEM, or the whole environment (all mappings) *)
    val env_varnames = ["MEM"];
    val env_varnames = (birs_utilsLib.birs_env_varnames o birsSyntax.get_birs_Pi_first o concl) thm;
    val thm_new = List.foldl (fn (vn,thm_) => (birs_simp_RULE_gen birs_simp_select o CONV_RULE (birs_utilsLib.birs_Pi_first_CONV (birs_utilsLib.birs_env_var_top_CONV vn))) thm_) thm env_varnames;
    val _ = birs_simp_instancesLib.birs_simp_regular_recurse_mode := false;

    val get_top_map = (birsSyntax.get_env_top_mapping o birsSyntax.dest_birs_state_env);
    val (mem_exp) = (snd o birsSyntax.get_birs_Pi_first_env_top_mapping o concl) thm_new;
    val _ = birs_mergeLib.print_mem_exp 500 mem_exp;
  in
    thm_new
  end;

val birs_basic_from_sums_simplify_env = ref true;
val birs_basic_from_sums_extra_postproc_fun = ref (NONE:(thm->thm) option);
fun birs_basic_from_sums bprog_tm birs_rule_SUBST_thm sums st_tm =
  let
    open birs_intervalLib;
    val birs_simp_select = birs_simp_instancesLib.birs_simp_default_core_exp_simp;
    val birs_simp_RULE_gen = birs_execLib.birs_rule_SUBST_trysimp_fun birs_rule_SUBST_thm;
    val simplify_sp =
      (birs_simp_RULE_gen birs_simp_select) o
      (birs_Pi_each_RULE (CONV_RULE (birs_Pi_first_CONV (birs_env_var_top_CONV "SP_process"))));
    val cleanup_postproc_fun =
      if !birs_basic_from_sums_simplify_env then
        cleanup_environment_thoroughly
      else
        I;
    val extra_postproc_fun_o = !birs_basic_from_sums_extra_postproc_fun;
    val extra_postproc_fun =
      if isSome extra_postproc_fun_o then
        valOf extra_postproc_fun_o
      else
        I;
    val postproc_fun = extra_postproc_fun o cleanup_postproc_fun o simplify_sp o birs_intervals_Pi_unify_RULE "countw";
  in
      birs_strategiesLib.birs_from_summaries postproc_fun sums st_tm
  end;
val birs_basic_from_sums = fn x => fn y => fn z => Profile.profile "birs_basic_from_sums" (birs_basic_from_sums x y z);


fun birs_basic_init_state prog_birenvtyl_def reqs init_addr =
  let
    open birs_driveLib;

    val init_lbl = bir_lbl_from_addr init_addr;
    val precond = mk_bandl (pred_conjs reqs);
    val init_state =
    birs_analysis_init prog_birenvtyl_def precond init_lbl;
  in
    init_state
  end;

val birs_basic_execute_concretization_resolver = ref NONE;
fun birs_basic_execute bprog_tm pre_simp extra_thms sums end_addrs init_state =
  let
    open birs_intervalLib;
    open birs_driveLib;
    val birs_rule_SUBST_thm = birs_execLib.birs_rule_SUBST_prog_fun bprog_tm;

    val concr_o = !birs_basic_execute_concretization_resolver;
    val _ = if not (isSome concr_o) then () else
      birs_stepLib.birs_symbval_concretizations_oracle_ext_CONV := valOf concr_o;

    val end_lbls = List.map bir_lbl_from_addr end_addrs;
    val symb_exec_thm =
    birs_exec_to
      bprog_tm
      (birs_strategiesLib.birs_post_step_armcm0_default pre_simp extra_thms)
      (birs_basic_from_sums bprog_tm birs_rule_SUBST_thm sums)
      (birs_strategiesLib.not_at_lbls end_lbls)
      init_state;
    val interval_thm = birs_intervals_Pi_unify_RULE "countw" symb_exec_thm;
  in
    interval_thm
  end;
val birs_basic_execute = fn x => fn pre_simp => fn extra_thms => fn y => fn z => Profile.profile "birs_basic_execute" (birs_basic_execute x pre_simp extra_thms y z);


(*
val _ = print "\n\n";
val _ = raise Fail "done";
val init_state = birs_basic_init_state birs_prog_config (200, 200) 0x100013b4;
val thm = birs_basic_execute birs_prog_config [0x100013BE, 0x100013C2] init_state;
*)

val birs_basic_merge =
  let
    open birs_mergeLib;
    open birs_intervalLib;
  in
    (birs_Pi_merge_RULE o birs_intervals_Pi_bounds_RULE "countw" o birs_intervals_Pi_unify_name_RULE "countw")
  end;
val birs_basic_merge = Profile.profile "birs_basic_merge" birs_basic_merge;

(*
fun birs_basic_instantiate (bprog_tm, prog_birenvtyl_def) =
  let
    open birs_composeLib;
    open birs_instantiationLib;
    open birs_intervalLib;
    val birs_rule_SEQ_thm = birs_rule_SEQ_prog_fun bprog_tm;
    val inst_SEQ_fun = birs_sound_inst_SEQ_RULE birs_rule_SEQ_thm birs_driveLib.pcond_gen_symb;
  in
    fn A_thm => (birs_intervals_Pi_unify_RULE "countw" o inst_SEQ_fun A_thm)
  end;
  val birs_basic_instantiate = fn x => fn y => Profile.profile "birs_basic_instantiate" (birs_basic_instantiate x y);
*)

(* ========================================================================================== *)

  val print_theorem_before_merging = ref false;
  fun birs_summary_gen pre_simp extra_thms (bprog_tm, prog_birenvtyl_def) sums reqs (init_addr, end_addrs) =
    let
      val init_state = birs_basic_init_state prog_birenvtyl_def reqs init_addr;
      val symb_exec_thm = birs_basic_execute bprog_tm pre_simp extra_thms sums end_addrs init_state;

      (* need to handle intervals correctly: in symbolic execution driver
           (also need this together with the indirectjump handling and previous summaries) and also before merging *)
      
      val _ = if not (!print_theorem_before_merging) then () else
        let
          val _ = print "\n=============== before merging ========\n";
          val _ = print_thm symb_exec_thm;
          val _ = print "\n=============== before merging end ========\n";
        in () end;
      val merged_thm = birs_basic_merge symb_exec_thm;
    in
      merged_thm
  end;
  val birs_summary_gen = fn pre_simp => fn extra_thms => fn x => fn y => fn z => Profile.profile "birs_summary_gen" (birs_summary_gen pre_simp extra_thms x y z);

  val birs_summary = birs_summary_gen birs_simpLib.birs_simp_ID_fun [];

  fun birs_find_countw_stack_usage thm =
    let
      fun mem_on_top tm =
        (rhs o concl o birs_env_set_order_CONV ["MEM"]) tm
        handle UNCHANGED => tm;
      val sys = (mem_on_top o get_birs_Pi_first o concl) thm;

      val pcond = dest_birs_state_pcond sys;
      val pcondl = dest_bandl pcond;
      val interval_tm =
        case List.filter (bir_extra_expsSyntax.is_BExp_IntervalPred) pcondl of
            [x] => x
          | _   => raise ERR "birs_find_countw_stack_usage" "something wrong with the interval subterm";
      val _ = print_term interval_tm;

      val env = dest_birs_state_env sys;
      val (_,mem_exp_tm) = get_env_top_mapping env;
      val (mexp1, stores1) = birs_simp_instancesLib.dest_BExp_Store_list mem_exp_tm [];
      val _ = if bir_expSyntax.is_BExp_Den mexp1 then () else
        raise ERR "birs_find_countw_stack_usage" "something wrong with the memory";
      (* TODO: add code that goes through the store operations and checks the addresses for stack accesses *)
    in
      ()
    end;
  
  fun print_tags thm =
    let
      val show_tags_prev = !Globals.show_tags;
      val _ = Globals.show_tags := true;
      val _ = Portable.pprint Tag.pp_tag (tag thm);
      val _ = Globals.show_tags := show_tags_prev;
    in () end;

  fun print_result thm (ret_addr_s, ret_instr, ret_instr_clocks) =
    let
      val _ = print "\n\n!!! RESULT !!!\n";
      val _ = print_tags thm;
      val _ = print "\n";
      val _ = birs_find_countw_stack_usage thm;
      val _ = print ("cycles for returning from this function at "^ret_addr_s^" ("^ret_instr^") are: "^ret_instr_clocks^"\n");
    in () end;
  
  val cancelled_z3_queries = ref ([]:string list);
  fun add_cancelled_z3_query filename =
    cancelled_z3_queries := filename::(!cancelled_z3_queries);
  fun set_default_cheat_setting () =
    let
      val _ = holba_z3Lib.querysmt_raw_timeout_override := SOME (1 * 60 * 1000); (*SOME 3*)
      val _ = holba_z3Lib.querysmt_raw_retries := 0;
      val _ = holba_z3Lib.querysmt_raw_query_times := SOME []; (*SOME[]*)
      val _ = holba_z3Lib.querysmt_raw_unknown_as_timeout := true;

      val _ = birs_mergeLib.birs_sound_symb_freesymbintro_RULE_smt_timeout_handler := NONE (*SOME add_cancelled_z3_query*);
      (*
 val birsmt_check_unsat_write_query_to_disk = ref false;
 fun birsmt_check_unsat bexp =
  let
    val exst = export_bexp bexp exst_empty;
    val q = querysmt_mk_q (exst_to_querysmt exst);
    val _ = if not (!birsmt_check_unsat_write_query_to_disk) then () else
      let
        val filename = holba_fileLib.get_tempfile "birsmt_query" ".txt";
        val _ = holba_fileLib.write_to_file filename q;
        val _ = print ("wrote birsmt query to disk: "^filename^"\n");
      in
        ()
      end;
    val result = querysmt_checksat NONE q;
      *)

      val _ = birs_strategiesLib.birs_from_summaries_exceptions := true;
      val _ = birs_strategiesLib.birs_from_summaries_fail_inst := true;
      val _ = birs_basic_from_sums_simplify_env := true;
      val _ = birs_execLib.step_L_approximate := true;
      val all_speedcheats_on = false;

      val _ = birs_composeLib.compose_L_speedcheat := (all_speedcheats_on orelse false);

      val _ = birs_simp_instancesLib.birs_storeelim_oracle_speed := (all_speedcheats_on orelse false);
      val _ = birs_mergeLib.birs_mem_shuffle_oracle_speed := (all_speedcheats_on orelse false);

      val _ = birs_conseqLib.rule_CONSEQ_oracle_speed := (all_speedcheats_on orelse false);
      val _ = birs_utilsLib.birs_env_order_oracle_speed := (all_speedcheats_on orelse false);

      val _ = birs_mergeLib.birs_freesymb_oracle_speed := (all_speedcheats_on orelse false);

      val _ = birs_instantiationLib.birs_subst1_oracle_speed := (all_speedcheats_on orelse false);
      val _ = birs_instantiationLib.rule_RENAME_oracle_speed := (all_speedcheats_on orelse false);
      val _ = birs_instantiationLib.rule_INST_oracle_speed := (all_speedcheats_on orelse false);

      (* (this file) BIRS_INDIRJMP_MEM + BIRS_CONST_LOAD *)
    in
      ()
    end;
  
  fun run_default_postproc () =
    let val times_o = !holba_z3Lib.querysmt_raw_query_times in
      if not (isSome times_o) then () else
      if List.null (valOf times_o) then print "\n\nno smt query times recorded\n\n" else
      let
        val times = valOf times_o;
        val num = List.length times;
        val (min, max) = List.foldl (fn (t,(min,max)) => (Int.min(min,t), Int.max(max,t))) (hd times, hd times) (tl times);
        val sum = List.foldl (fn (t,s) => Real.+(s,Real.fromInt t)) (Real.fromInt 0) times;
        val avg = Real./(sum, Real.fromInt num);
        val sum_int = Real.toInt IEEEReal.TO_NEAREST sum;
        val avg_int = Real.toInt IEEEReal.TO_NEAREST (Real./(Real.realRound(Real.*(avg, Real.fromInt 10)), Real.fromInt 10));
        val _ = print ("\n\nsmt query times = num: "^Int.toString num^"; sum:"^Int.toString sum_int^"; avg:"^Int.toString avg_int^"; range:[" ^Int.toString min^ ", " ^Int.toString max^ "] ms\n\n");
        val _ = print "cancelled smt queries:\n";
        val _ = List.app (print o (fn x => "- "^x^"\n")) (!cancelled_z3_queries);
        val _ = print "\n";
      in
        ()
      end
    end;
  
  (*
  NOTES:
    conseq with checks overhead not too bad
      - can probably be improved a bit

    store elimination and memory shuffling with z3 seem okay
      - no issues with application last time i ran
      - execution time not too bad
      - improvement here probably would mean to not use simple reduction to z3, then probably messy to implement

    L approximation: ok until ftop, which takes 612s instead of 58s, seems to be taking forever for SEQ
      - probably because of lots of union operations on gigantic L sets, i.e. 1600-1700 for ftop.
      - top not toooo bad. "just" 18m instead of 3m. maybe because not so many paths? anyhow, 1900 labels
      - not approximating makes it run for almost 4h
    
    best if RENAME and INST could be always run with checking, only subst might be cheated
      - RENAME does not need to be cheated, checks can always run
      - subst needs to be optimized, must be terrible performance
      - INST and RENAME together run in about 25 minutes
      - multisubst should be able to save the performance from the many single substitutions, but that's a high effort to fix...
      - TODO: make up oracled multisubst theorems at bir level
    
    not ok: freesymb
      - !!! is the problem maybe the substitution to find the new expression? replace by subterm causes problems?
      - runs ok for about 12 min, goes up to balrob_ftop, where it hangs at freesymboling(merging) after about 2 minutes, z3 suddenly runs for 2.6h, then when it ran for hours again, i stopped it
      - actually, also gets quite stuck in fmul I noticed, more than 10 minutes at some point. whatever the problem, it seems to be growing
      - seems like the query gets too big for z3, where it applies a different strategy that is running badly
      - in the meantime improved some other checks a bit, but it won't fix the z3 issue
      - could export the simplification checks and run them offline
        - add timeout to z3 exporter, catch the exception in freesymb function, which then writes the bir expressions that have that problem into a file and assumes it was successful

    lifted memory in precondition?
      - this is an annoying one. maybe need to introduce bir expression type save lifted memory array.
        - as equivalent to a bunch of store operations?
        - or better as explicit semantics like memory constant?
        - no other way that is easy and crude?

    env mapping shuffle?

    indirect jump from lifted memory in precondition?
  *)

end (* local *)

end (* struct *)
