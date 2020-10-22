structure bir_symbexec_driverLib =
struct

local
  open bir_miscLib;

  open binariesLib;
  open binariesCfgLib;
  open binariesMemLib;

  open bir_symbexec_stateLib;
  open bir_symbexec_coreLib;
  open bir_symbexec_stepLib;
  open bir_symbexec_sumLib;
  open bir_countw_simplificationLib;

  open commonBalrobScriptLib;

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
                          List.filter (fn n => node_to_rel_symbol n = entry_label andalso
                                               cfg_node_type_eq (#CFGN_type n, CFGNT_Return))
                         ) (List.map snd (Redblackmap.listItems n_dict));
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


  (* driving and book keeping of symbolic execution *)
  (* ================================================================== *)
  fun drive_to_raw n_dict bl_dict_ systs_start stop_lbl_tms =
    let
      val cfb = false;

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
      val _ = print "\n\n";

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
  (* TODO: restructure this to capture fuction summaries better *)
  fun merge_func lbl_tm systs_tidiedup =
    let
      val _ = if not (List.null systs_tidiedup) then () else
              raise ERR "merge_func" "cannot merge an emptry list of states, expecting at least one";

      val syst_merged =
        (fn x => List.foldr
                  (merge_states_vartointerval bv_countw bv_mem bv_sp)
                  (hd x)
                  (tl x)
        ) systs_tidiedup;

      (* print sp and mem *)
      val _ =
        let
          val syst_merged_sp_symbv  = get_state_symbv "script" bv_sp syst_merged;
          val _ = print ("\nSP  = " ^ (symbv_to_string_raw true syst_merged_sp_symbv) ^ "\n\n");
        in () end
        handle _ => print "\nSP  = n/a\n\n";
      val _ =
        let
          val syst_merged_mem_symbv = get_state_symbv "script" bv_mem syst_merged;
          val _ = print ("\nMEM = " ^ (symbv_to_string_raw true syst_merged_mem_symbv) ^ "\n\n");
        in () end
        handle _ => print "\nSP  = n/a\n\n";

      val syst_summary = (lbl_tm, "path predicate goes here", [syst_merged]);

      val syst_merged_countw = get_state_symbv "script" bv_countw syst_merged;

      (*
      val _ = print (symbv_to_string syst_merged_countw);
      *)

      val (count_min, count_max) =
        case syst_merged_countw of
           SymbValInterval ((min, max), _) =>
              (term_to_string min, term_to_string max)
         | _ => raise ERR "balrob-test" "should be an interval";

      val _ = print "\n\n\n";
      val _ = print ("min = " ^ count_min ^ "\n");
      val _ = print ("max = " ^ count_max ^ "\n");
    in
      syst_summary
    end;


  (* creation of summaries (semi-recursively uses summaries!) *)
  (* ================================================================== *)

  (* TODO: include stack usage and wcet estimation -> preconditions *)
  (* TODO: carry through preconditions *)

  fun init_summary lbl_tm =
    let
      val use_countw_const_only = false;
      val use_mem_symbolic = true;

      val syst = init_state lbl_tm prog_vars;

      val syst =
        if use_countw_const_only then
          state_assign_bv bv_countw ``BExp_Const (Imm64 0w)`` syst
        else
          state_make_interval bv_countw syst;

      val syst = if not use_mem_symbolic then syst else
           state_make_mem bv_mem
             (Arbnum.fromInt mem_sz_const, Arbnum.fromInt mem_sz_globl, Arbnum.fromInt mem_sz_stack)
                 (mem_read_byte binary_mem)
                 bv_sp
                 syst;

      val syst = state_add_preds "init_pred" pred_conjs syst;

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
      val systs_new = instantiate_summaries sums systs_continue;

      (* append ended states *)
      val acc_new = (systs_ended@systs_assertfailed@acc);
    in
      drive_through_summaries n_dict bl_dict sums systs_new end_lbl_tms acc_new
    end;

  fun obtain_summary n_dict bl_dict sums lbl_tm end_lbl_tms =
    let
      val syst_start = init_summary lbl_tm;
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

      val timer_meas = timer_start 1;
      val systs_after = drive_through_summaries n_dict bl_dict sums systs end_lbl_tms [];
      val _ = timer_stop (fn s => print("time to drive symbolic execution: " ^ s ^ "\n")) timer_meas;

      val syst_summary = merge_func lbl_tm systs_after;
    in
      syst_summary
    end;


  (* creation of summaries for functions *)
  (* ================================================================== *)
  fun create_func_summary n_dict bl_dict sums entry_label =
    let
      val lbl_tm      = find_func_lbl_tm entry_label;
      val end_lbl_tms = find_func_ends n_dict entry_label;

      val syst_summary = obtain_summary n_dict bl_dict sums lbl_tm end_lbl_tms;
    in
      syst_summary
    end;

end (* outermost local *)

end (* struct *)
