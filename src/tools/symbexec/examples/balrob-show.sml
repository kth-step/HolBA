open HolKernel Parse

open binariesLib;
open binariesCfgLib;
open binariesMemLib;

val entry_labels = ["motor_prep_input",
                    "__lesf2",
                    "__clzsi2",
                    "__aeabi_f2iz",
                    "pid_msg_write",
                    "timer_read"];

open binariesCfgVizLib;
open binariesDefsLib;

val _ = show_call_graph ();

(*
val entry_label = List.nth (entry_labels, 0);
val _ = show_cfg_fun true  bl_dict_ n_dict entry_label;
*)

val _ = show_cfg_fun false  bl_dict_ n_dict "imu_handler_pid_entry";

(*
fun print_option pf NONE     = print "NONE"
  | print_option pf (SOME x) = (print "SOME ("; pf x; print ")");
*)

(*
=================================================================================================
*)

(*
val _ = show_cfg_fun false  bl_dict_ n_dict "__aeabi_fadd";

val _ = show_cfg_fun true  bl_dict_ n_dict "__aeabi_fmul";
val _ = show_cfg_fun false bl_dict_ n_dict "__aeabi_fmul";
val _ = show_cfg_fun false bl_dict_ n_dict "__aeabi_fdiv";

val _ = List.map (print_fun_pathstats false n_dict)
                 (List.filter (fn x => x <> "__aeabi_fdiv") symbs_sec_text);

val _ = print_dead_code bl_dict_ n_dict entry_label;
*)


(*
=================================================================================================
*)

(*
val names = symbs_sec_text;

val name = List.nth(names, 0);
fun name_to_instrsnum name =
  List.length (List.filter ((fn s => s = name) o lbl_tm_to_rel_symbol) (List.map fst (Redblackmap.listItems n_dict)));
val szmap = List.map (fn n => (n, name_to_instrsnum n)) names;

val _ = print "\ninstructions per function: \n";
val _ = List.app (fn (n,sz) => (
  print ("- " ^ n ^ "\n");
  print ("  size: " ^ (Int.toString sz) ^ "\n"))) szmap;

val _ = print ("\ntotal number of instructions: " ^ (Int.toString (List.foldr (+) (0) (List.map snd szmap))) ^ "\n");
*)

