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

val _ = List.map (print_fun_pathstats false ns)
                 (List.filter (fn x => x <> "__aeabi_fdiv") symbs_sec_text);

val _ = print_dead_code ns entry_label;
*)

