open HolKernel Parse

open binariesDefsLib;
open binariesLib;
open binariesCfgLib;
open binariesCfgVizLib;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = set_trace "bir_inst_lifting.DEBUG_LEVEL" 2;

val entry_label = "imu_handler_pid_entry";

(*
fun print_option pf NONE     = print "NONE"
  | print_option pf (SOME x) = (print "SOME ("; pf x; print ")");
*)

(*
=================================================================================================
*)

(*
val _ = show_call_graph ();

val _ = show_cfg_fun true  ns entry_label;
val _ = show_cfg_fun true  ns "__aeabi_fmul";
val _ = show_cfg_fun false ns "__aeabi_fmul";
val _ = show_cfg_fun false ns "__aeabi_fdiv";
*)

(*
val ns_c  = build_fun_cfg ns entry_label;
val ns_f = List.filter ((fn s => s = entry_label) o node_to_rel_symbol) ns;
val dead_code = (List.filter (fn x => not (List.exists (fn y => x = y) (#CFGG_nodes ns_c))) ns_f);
val _ = List.map (fn n => (print_term (#CFGN_lbl_tm n); print ((#CFGN_descr n) ^ "\n"))) dead_code;
*)

(*
val ns_c2 = build_fun_cfg ns "__aeabi_fmul";
val ns_f3 = List.filter ((fn s => s = "__aeabi_fmul") o node_to_rel_symbol) ns;
val ns_f4 = List.filter ((fn s => s = "__aeabi_fdiv") o node_to_rel_symbol) ns;

val ns_1 = #CFGG_nodes ns_c;
val ns_2 = #CFGG_nodes ns_c2;
val ns_3 = ns_f3;
val ns_4 = ns_f4;

val _ = display_graph_cfg_ns ns_4;
*)

val (n_paths, sum_calls) = count_paths_to_ret false ns [] (mem_symbol_to_prog_lbl entry_label);

val name = "motor_set";
val return_lbl_tms = (
   (List.map (#CFGN_lbl_tm)) o
   (List.filter (fn n => (#CFGN_type n) = CFGNT_Return)) o
   (List.filter ((fn s => s = name) o node_to_rel_symbol))
  ) ns;
(* cannot follow calls like this *)
val (n_paths, sum_calls) = count_paths_to_ret false ns (return_lbl_tms) (mem_symbol_to_prog_lbl name);

val n_calls = length sum_calls;
val histo_calls = to_histogram sum_calls;


val _ = print "^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n";

fun print_fun_pathstats ns name =
  let
    val (n_paths, sum_calls) = count_paths_to_ret false ns [] (mem_symbol_to_prog_lbl name);
    val _ = print ("fun " ^ name ^ " : " ^ (Int.toString n_paths) ^ ", calls " ^ (Int.toString (length sum_calls)) ^ "\n");
  in
    ()
  end;

val _ = List.map (print_fun_pathstats ns) (List.filter (fn x => x <> "__aeabi_fdiv") symbs_sec_text);


(*

TODO: tidy up graph handling and printing functions, and others

*)


