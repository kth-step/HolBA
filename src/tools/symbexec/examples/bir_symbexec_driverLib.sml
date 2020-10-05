structure bir_symbexec_driverLib =
struct

local
  open binariesLib;
  open binariesCfgLib;
  open binariesMemLib;

  open bir_symbexec_stateLib;
  open bir_symbexec_coreLib;
  open bir_symbexec_stepLib;
  open bir_symbexec_funcLib;
  open bir_countw_simplificationLib;

  open commonBalrobScriptLib;

  val ERR      = Feedback.mk_HOL_ERR "bir_symbexec_driverLib"
  val wrap_exn = Feedback.wrap_exn   "bir_symbexec_driverLib"
in (* outermost local *)

(* TODO: include stack usage and wcet estimation -> preconditions *)
(* TODO: carry through preconditions *)

fun init_func entry_label =
let
val name   = entry_label;

val _ = print ("\n\nfunname = " ^ (name) ^ "\n\n");

val lbl_tm = (mk_lbl_tm o valOf o mem_find_symbol_addr_) name;

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
  (lbl_tm, syst)
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

fun drive_to n_dict bl_dict_ systs_start stop_lbl_tms =
let
val cfb = false;

val systs = symb_exec_to_stop (abpfun cfb) n_dict bl_dict_ systs_start stop_lbl_tms [];
val _ = print "finished exploration of all paths.\n";
val _ = print ("number of paths found: " ^ (Int.toString (length systs)));
val _ = print "\n\n";

val (systs_noassertfailed, systs_assertfailed) =
  List.partition (fn syst => not (identical (SYST_get_status syst) BST_AssertionViolated_tm)) systs;
val _ = print ("number of \"no assert failed\" paths found: " ^ (Int.toString (length systs_noassertfailed)));
val _ = print "\n\n";

val systs_feasible = List.filter check_feasible systs_noassertfailed;
val _ = print ("number of feasible paths found: " ^ (Int.toString (length systs_feasible)));
val _ = print "\n\n";

val systs_tidiedup = List.map tidyup_state_vals systs_feasible;
val _ = print "finished tidying up all paths.\n\n";
in
  systs_tidiedup
end;

(* TODO: restructure this to capture fuction summaries better *)
fun merge_func lbl_tm systs_tidiedup =
let
val syst_merged =
  (fn x => List.foldr (merge_states_vartointerval bv_countw bv_mem bv_sp)
                      (hd x)
                      (tl x)
  ) systs_tidiedup;

(* print sp and mem *)
val syst_merged_sp_symbv  = get_state_symbv "script" bv_sp syst_merged;
val _ = print ("\nSP  = " ^ (symbv_to_string_raw true syst_merged_sp_symbv) ^ "\n\n");
val syst_merged_mem_symbv = get_state_symbv "script" bv_mem syst_merged;
val _ = print ("\nMEM = " ^ (symbv_to_string_raw true syst_merged_mem_symbv) ^ "\n\n");

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

(* TODO: find precondition representation for instantiation and use it in instantiation *)
(* TODO: adapt for multiple states *)
fun instantiate_func systs syst_summary =
let
val systs_noassertfailed = systs;
val syst = if length systs_noassertfailed = 1 then hd systs_noassertfailed else
           raise ERR "script" "more than one symbolic state in current path/state";

val syst_inst = instantiate_function_summary syst_summary syst;

(*
val envl = (Redblackmap.listItems o SYST_get_env) syst_inst;
val valsl = (Redblackmap.listItems o SYST_get_vals) syst_inst;
*)

(* ... and continuation up to the return of the function *)
val _ = print "\n========================\n";
val _ = print "continue after instantiation...\n\n";
in
  [syst_inst]
end;

end (* outermost local *)

end (* struct *)
