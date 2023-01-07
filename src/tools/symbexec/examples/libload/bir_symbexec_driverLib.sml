structure bir_symbexec_driverLib =
struct

local

  open HolKernel Parse;

  open bir_miscLib;

  open binariesLib;
  open binariesCfgLib;
  open binariesMemLib;

  open bir_symbexec_stateLib;
  open bir_symbexec_coreLib;
  open bir_symbexec_stepLib;
  open bir_symbexec_sumLib;
  open bir_countw_simplificationLib;

  val ERR      = Feedback.mk_HOL_ERR "bir_symbexec_driverLib"
  val wrap_exn = Feedback.wrap_exn   "bir_symbexec_driverLib"
in (* outermost local *)

  (* helpers for dealing with functions in the binary *)
  (* ================================================================== *)
  fun find_func_lbl_tm entry_label =
    let
      val name   = entry_label;
      val _ = print ("\n\nfunname = " ^ (name) ^ "\n\n");
      val lbl_tm = (mk_lbl_tm o valOf o mem_find_symbol_addr_) name;
    in
      lbl_tm
    end;

  fun find_func_ends n_dict entry_label =
    let
      open bir_cfgLib;

      val stop_lbl_tms = (List.map #CFGN_lbl_tm o
                          List.filter (fn n => cfg_node_type_eq (#CFGN_type n, CFGNT_Return))
                         ) (List.map snd (Redblackmap.listItems n_dict));

      val _ = print "stop detection:\n";
      val _ = List.map (print_term) stop_lbl_tms;
      val _ = print "stop detection finished.\n";
    in
      stop_lbl_tms
    end;


  (* helper for progress output *)
  (* ================================================================== *)
  fun filter_with_progress filtfun l =
    let
      val print_again_t = ref (Time.now());
      val llenr = Real.fromInt (length l);
      val iref = ref 0;
      fun filter_spec x =
        let
          val _ = iref := !iref + 1;
          val frac = Real./(Real.fromInt (!iref), llenr);
          val frac1000 = Real.*(frac, Real.fromInt 1000);
          val frac1000i = Real.round frac1000;

          val _ = if Time.<(Time.now(), !print_again_t) then () else (
            print_again_t := (Time.fromReal o LargeReal.+) (Time.toReal(Time.now()), LargeReal.fromInt 5);
            print ((Int.toString (frac1000i div 10)) ^ "." ^ (Int.toString (frac1000i mod 10)) ^ "%\n")
           );
        in
          filtfun x
        end;

      val result = List.filter filter_spec l;
    in
      print "filtering done\n";
      result
    end;

  val symbexecdriver_checkfeasibility = false;


  (* driving and book keeping of symbolic execution *)
  (* ================================================================== *)
  fun drive_to_raw n_dict bl_dict_ systs_start stop_lbl_tms =
    let
      val cfb = symbexecdriver_checkfeasibility;

      open commonBalrobScriptLib;

      val systs = symb_exec_to_stop (abpfun cfb) n_dict bl_dict_ systs_start stop_lbl_tms [];
      val _ = print "finished exploration of all paths.\n";
      val _ = print ("number of paths found: " ^ (Int.toString (length systs)));
      val _ = print "\n\n";
    in
      systs
    end;

  fun check_feasible_and_tidyup systs =
    let
      val (systs_noassertfailed, systs_assertfailed) =
        List.partition (fn syst => not (identical (SYST_get_status syst) BST_AssertionViolated_tm)) systs;
      val _ = print ("number of \"no assert failed\" paths found: " ^ (Int.toString (length systs_noassertfailed)));
      val _ = print "\n";

      val systs_assertfailed_feasible =
       (if symbexecdriver_checkfeasibility then filter_with_progress check_feasible else I) systs_assertfailed;
      val _ = print ("number of" ^ (if symbexecdriver_checkfeasibility then " feasible" else "") ^ " \"assert failed\" paths found: " ^ (Int.toString (length systs_assertfailed_feasible)));
      val _ = print "\n";

      val _ =
        if not symbexecdriver_checkfeasibility then [] else
        List.map (fn syst =>
          let
            val vals = SYST_get_vals syst;
            val pred = hd (SYST_get_pred syst)
                       handle _ => raise Fail "oh no! no preds?!";
            val _ = print_term pred;
            val symbv = find_bv_val "check_feasible_and_tidyup" vals pred;
            val _ = print (symbv_to_string symbv);
          in () end
        ) systs_assertfailed_feasible;

      val systs_feasible = filter_with_progress check_feasible systs_noassertfailed;
      val _ = print ("number of feasible paths found: " ^ (Int.toString (length systs_feasible)));
      val _ = print "\n\n";

      val systs_tidiedup = List.map tidyup_state_vals systs_feasible;
      val _ = print "finished tidying up all paths.\n\n";
    in
      systs_tidiedup
    end;

  (* only keeps running paths and then checks feasibility *)
  fun drive_to n_dict bl_dict_ systs_start stop_lbl_tms =
    let
      val systs = drive_to_raw n_dict bl_dict_ systs_start stop_lbl_tms;
      val systs_tidiedup = check_feasible_and_tidyup systs;
    in
      systs_tidiedup
    end;


  (* merging symbolic state list (assuming that all states have same pc) *)
  (* ================================================================== *)
  (* TODO: restructure this to capture summaries better *)
  fun merge_to_summary lbl_tm systs_tidiedup =
    let
      val _ = if not (List.null systs_tidiedup) then () else
              raise ERR "merge_to_summary" "cannot merge an emptry list of states, expecting at least one";

      val systs_wlbl = List.map (fn syst => (SYST_get_pc syst, syst)) systs_tidiedup;
      fun group_by_fst lbl_tm [] acc = acc
	| group_by_fst lbl_tm sywlbs acc =
            let
              val (sywlbs_grp, sywlbs_new) = List.partition (identical lbl_tm o fst) sywlbs;
              val acc_new = sywlbs_grp::acc;
              val lbl_tm_new = if List.null sywlbs_new then lbl_tm else (fst o hd) sywlbs_new;
            in
              group_by_fst lbl_tm_new sywlbs_new acc_new
            end;
      val systs_grps = List.map (List.map snd) (group_by_fst ((fst o hd) systs_wlbl) systs_wlbl []);

      val systs_merged =
        List.map
        (fn x => List.foldr
                  (merge_states_vartointerval bv_countw bv_mem bv_sp)
                  (hd x)
                  (tl x)
        ) systs_grps;

      val _ = List.map (fn syst_merged =>
        let
          val _ = print_term (SYST_get_pc syst_merged);
          (* print sp and mem *)
          val _ =
            let
              val syst_merged_sp_symbv  = get_state_symbv "merge_to_summary" bv_sp syst_merged;
              val _ = print ("\nSP  = " ^ (symbv_to_string_raw true syst_merged_sp_symbv) ^ "\n\n");
            in () end
            handle _ => print "\nSP  = n/a\n\n";
          val _ =
            let
              val syst_merged_mem_symbv = get_state_symbv "merge_to_summary" bv_mem syst_merged;
              val _ = print ("\nMEM = " ^ (symbv_to_string_raw true syst_merged_mem_symbv) ^ "\n\n");
            in () end
            handle _ => print "\nMEM  = n/a\n\n";

          val syst_merged_countw = get_state_symbv "merge_to_summary" bv_countw syst_merged;

          (*
          val _ = print (symbv_to_string syst_merged_countw);
          *)

          val (count_min, count_max) =
            case syst_merged_countw of
               SymbValInterval ((min, max), _) =>
                  (term_to_string min, term_to_string max)
             | _ => raise ERR "merge_to_summary" "should be an interval";

          val _ = print "\n\n\n";
          val _ = print ("min = " ^ count_min ^ "\n");
          val _ = print ("max = " ^ count_max ^ "\n");
        in () end) systs_merged;

      val sum = (lbl_tm, "path predicate goes here", systs_merged);
    in
      sum
    end;


  (* creation of summaries (semi-recursively uses summaries!) *)
  (* ================================================================== *)

  (* TODO: include stack usage and wcet estimation -> preconditions *)
  (* TODO: carry through preconditions *)

  fun init_summary lbl_tm usage =
    let
      val use_countw_const_only = false;
      val use_mem_symbolic = true;

      val syst = init_state lbl_tm prog_vars;
      val _ = print "initial state at: ";
      val _ = print_term lbl_tm;

      val syst =
        if use_countw_const_only then
          state_assign_bv bv_countw ``BExp_Const (Imm64 0w)`` syst
        else
          state_make_interval bv_countw syst;

      open commonBalrobScriptLib;

      val syst = if not use_mem_symbolic then syst else
           state_make_mem bv_mem
             (Arbnum.fromInt mem_sz_const, Arbnum.fromInt mem_sz_globl, Arbnum.fromInt mem_sz_stack)
                 (mem_read_byte binary_mem)
                 bv_sp
                 syst;

      val syst = state_add_preds
                   "init_pred"
                   (pred_conjs usage)
                   syst;

      (* hotfix to make SP appear in vals *)
      val syst =
        let
          val bv = “BVar "SP_process" (BType_Imm Bit32)”;
          val env    = SYST_get_env syst;
          val bv_val = find_bv_val "hotfix_sp_in_vals" env bv;
          val _ = if is_bvar_init bv_val then () else
                  raise ERR "hotfix_sp_in_vals" "need sp as initial variable";

          val exp   = ``
        BExp_BinExp BIExp_Minus
          ^(bir_expSyntax.mk_BExp_Den bv_val)
          (BExp_Const (Imm32 0w))``;

          val deps  = Redblackset.add (symbvalbe_dep_empty, bv_val);
          val symbv = SymbValBE (exp, deps);

          val bv_fresh = (get_bvar_fresh) bv;
        in
          (update_envvar bv bv_fresh o
           insert_symbval bv_fresh symbv
          ) syst
        end;

      val _ = if check_feasible syst then () else
              raise ERR "init_summary" "initial state infeasible, check path condition";

      val _ = print "initial state created.\n\n";
    in
      syst
    end;

  (* TODO: needs to be somewhere else, and this here is a copy from bir_symbexec_hypoLib *)
  fun mem_eq eq x [] = false
    | mem_eq eq x (y::ys) =
        eq (x,y) orelse
        mem_eq eq x ys;

  fun drive_through_summaries n_dict bl_dict sums []    end_lbl_tms acc = acc
    | drive_through_summaries n_dict bl_dict sums systs end_lbl_tms acc =
    let
      val stop_lbl_tms = end_lbl_tms@(List.map (fn (x,_,_) => x) sums);
      val systs_after = drive_to n_dict bl_dict systs stop_lbl_tms;

      (* filter out ended states *)
      val (systs_noassertfailed, systs_assertfailed) =
        List.partition
          (fn syst => not (identical (SYST_get_status syst) BST_AssertionViolated_tm))
          systs_after;

      val (systs_ended, systs_continue) =
        List.partition
          (fn syst_ => mem_eq (fn (x,y) => identical x y) (SYST_get_pc syst_) end_lbl_tms)
          systs_noassertfailed;

      (* instantiation and recursion with what is not yet in end_lbl_tms *)
      val _ = bir_symbexec_step_execcallsnum := (!bir_symbexec_step_execcallsnum)+(List.length systs_continue);
      val systs_new = instantiate_summaries sums systs_continue;

      (* append ended states *)
      val acc_new = (systs_ended@systs_assertfailed@acc);
    in
      drive_through_summaries n_dict bl_dict sums systs_new end_lbl_tms acc_new
    end;

  fun obtain_summary n_dict bl_dict sums usage lbl_tm end_lbl_tms =
    let
      val syst_start = init_summary lbl_tm usage;
      val systs = [syst_start];

      (*
      (* TODO: this needs to be patched to account for summary "jumps" *)
(*
    fun sum_to_sumjumps (lbl_tm_, _, systs_) =
      List.map (fn syst_ => (lbl_tm_, SYST_get_pc syst_)) systs_;
    val sumjump_list = flatten (List.map sum_to_sumjumps sums);
*)
      val timer_meas = timer_start 1;
      val (num_nodetravs, num_pahts, num_paths_wasserts) =
	bir_symbexec_hypoLib.collect_trav_info bl_dict n_dict [lbl_tm] end_lbl_tms;
      val _ = print ("number of cfg nodes to traverse: " ^ (Int.toString (num_nodetravs)) ^ "\n");
      val _ = print ("number of paths to traverse: " ^ (Int.toString (num_pahts)) ^ "\n");
      val _ = print ("number of paths with assert: " ^ (Int.toString (num_paths_wasserts)) ^ "\n");
      val _ = timer_stop (fn s => print("time to collect traversal info: " ^ s ^ "\n")) timer_meas;
      *)

      val _ = bir_symbexec_step_reset_counters ();
      val timer_meas = timer_start 1;
      val systs_after = drive_through_summaries n_dict bl_dict sums systs end_lbl_tms [];
      val _ = timer_stop (fn s => print("time to drive symbolic execution: " ^ s ^ "\n")) timer_meas;
      val _ = bir_symbexec_step_print_counters ();

      val sum = merge_to_summary lbl_tm systs_after;
    in
      sum
    end;


  (* print usage info of summaries *)
  (* ================================================================== *)
  fun print_summary_info sum entry_label =
    let
      (* print max stack usage and max clock cycle usgae *)
      val _ = print ("\n\n>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>\n");
      val _ = print ("Summary info for " ^ entry_label ^ "\n");
      val _ = print (">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>\n");
      val (_, _, sum_systs) = sum;
      val _ = print ("Have " ^ (Int.toString (length sum_systs)) ^ " states in summary.\n");
      val _ = List.map (fn syst_merged =>
        let
          val syst_merged_mem_symbv = get_state_symbv "obtain_summary" bv_mem syst_merged;
          val (mem_sp, mem_stack) =
            case syst_merged_mem_symbv of
               SymbValMem (_, _, (_,_, m), _) => m
	     | _ => raise ERR "obtain_summary" "should be a symbolic memory";
          val mem_stack_max =
            let
              val addrs = (List.map fst o Redblackmap.listItems) mem_stack;
              val max_r = List.foldr (fn (a,max_) => if Arbnum.< (max_, a) then a else max_) Arbnum.zero addrs;
              val max   = if List.null addrs
                          then Arbnum.zero
                          else Arbnum.+ (max_r, Arbnum.fromInt 0);
            in
              Arbnum.toString max
            end;
          val _ = print ("\nstack  max = " ^ (mem_stack_max) ^ "\n");
          val syst_merged_countw = get_state_symbv "obtain_summary" bv_countw syst_merged;
          val countw_max_tm =
            case syst_merged_countw of
               SymbValInterval ((_, max), _) => max
             | _ => raise ERR "obtain_summary" "should be an interval";
          val countw_inc = ((fn add_tm =>
            let
              val match_tm = ``BExp_BinExp BIExp_Plus
                               (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
                               (BExp_Const (Imm64 x))``;
              val (vs, _) = hol88Lib.match match_tm add_tm;
              val inc_val = fst (List.nth (vs, 0));
            in term_to_string inc_val end
            ) countw_max_tm)
            handle _ => raise ERR "obtain_summary" ("countw max expression not as expected" ^ (term_to_string countw_max_tm))
          val _ = print ("countw max = " ^ countw_inc ^ "\n");
        in () end) sum_systs;
      val _ = print ("\n<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<\n\n");
    in
      ()
    end;


  (* creation of summaries for functions *)
  (* ================================================================== *)
  fun create_func_summary n_dict bl_dict sums entry_label =
    let
      val lbl_tm      = find_func_lbl_tm entry_label;
      val end_lbl_tms = find_func_ends n_dict entry_label;

      val usage = commonBalrobScriptLib.get_fun_usage entry_label;

      val sum = obtain_summary n_dict bl_dict sums usage lbl_tm end_lbl_tms;

      val _ = print_summary_info sum entry_label;
    in
      sum
    end;

end (* outermost local *)

end (* struct *)
