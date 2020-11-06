open HolKernel Parse

open binariesLib;
open binariesCfgLib;
open binariesMemLib;

open bir_symbexec_stateLib;
open bir_symbexec_coreLib;
open bir_symbexec_stepLib;
open bir_symbexec_sumLib;
open bir_countw_simplificationLib;

val entry_labels = ["motor_prep_input",
                    "__lesf2",
                    "__clzsi2",
                    "__aeabi_f2iz",
                    (*"pid_msg_write",*)
                    "timer_read"];


val _ = List.map (fn entry_label => let
  val name   = entry_label;

  val _ = print "\n\n>>>>>>>>>>>>>>>>>>>>>>>>>\n";
  val _ = print ("funname = " ^ (name) ^ "\n");

  val lbl_tm = (mk_lbl_tm o valOf o mem_find_symbol_addr_) name;

  local
    open bir_cfgLib;
  in
    val stop_lbl_tms = (List.map #CFGN_lbl_tm o
                        List.filter (fn n => node_to_rel_symbol n = name andalso
                                             cfg_node_type_eq (#CFGN_type n, CFGNT_Return))
                       ) (List.map snd (Redblackmap.listItems n_dict));
  end

  val syst = init_state lbl_tm prog_vars;

  val syst = state_make_interval bv_countw syst;

  local
    open commonBalrobScriptLib;
  in
  val syst = state_make_mem bv_mem
                            (Arbnum.fromInt mem_sz_const, Arbnum.fromInt mem_sz_globl, Arbnum.fromInt mem_sz_stack)
                            (mem_read_byte binary_mem)
                            bv_sp
                            syst;

  val syst = state_add_preds "init_pred" (pred_conjs (get_fun_usage entry_label)) syst;
  end

  val _ = print "initial state created.\n";

  (* -------------------------------------------------------------- *)
  val cfb = false;

  val systs = symb_exec_to_stop (commonBalrobScriptLib.abpfun cfb) n_dict bl_dict_ [syst] stop_lbl_tms [];
  val _ = print ("finished exploration of all paths. number = " ^ (Int.toString (length systs)));
  val _ = print "\n";

  (* -------------------------------------------------------------- *)
  val (systs_noassertfailed, systs_assertfailed) =
    List.partition (fn syst => not (identical (SYST_get_status syst) BST_AssertionViolated_tm)) systs;
  val _ = print ("number of \"no assert failed\" paths found: " ^ (Int.toString (length systs_noassertfailed)));
  val _ = print "\n";

  (* -------------------------------------------------------------- *)
  val systs_feasible = List.filter check_feasible systs_noassertfailed;
  val _ = print ("number of feasible paths found: " ^ (Int.toString (length systs_feasible)));
  val _ = print "\n";

  (* -------------------------------------------------------------- *)
  val systs_tidiedup = List.map tidyup_state_vals systs_feasible;
  val _ = print "finished tidying up all paths.\n";

  (* -------------------------------------------------------------- *)
  val syst_merged =
    (fn x => List.foldr (merge_states_vartointerval bv_countw bv_mem bv_sp)
                        (hd x)
                        (tl x)
    ) systs_tidiedup;

  (* -------------------------------------------------------------- *)
  val syst_merged_countw = get_state_symbv "script" bv_countw syst_merged;

  (* -------------------------------------------------------------- *)
  val (count_min, count_max) =
    case syst_merged_countw of
       SymbValInterval ((min, max), _) =>
          (term_to_string min, term_to_string max)
     | _ => raise ERR "balrob-test" "should be an interval";

  (* -------------------------------------------------------------- *)
  val _ = print ("min = " ^ count_min ^ "\n");
  val _ = print ("max = " ^ count_max ^ "\n");


in () end) entry_labels;

