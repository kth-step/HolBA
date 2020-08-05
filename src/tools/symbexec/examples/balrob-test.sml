open HolKernel Parse

open binariesLib;
open binariesCfgLib;

open bir_symbexecLib;
open bir_countw_simplificationLib;

val entry_label = "motor_prep_input";

(*
fun print_option pf NONE     = print "NONE"
  | print_option pf (SOME x) = (print "SOME ("; pf x; print ")");
*)

(*
=================================================================================================
*)

(*
open binariesCfgVizLib;
open binariesDefsLib;

val _ = show_call_graph ();

val _ = show_cfg_fun true  bl_dict_ n_dict entry_label;
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

val name   = entry_label;
val lbl_tm = (mk_lbl_tm o valOf o mem_find_symbol_addr_) name;

local
  open bir_cfgLib;
in
  val stop_lbl_tms = (List.map #CFGN_lbl_tm o
                      List.filter (fn n => node_to_rel_symbol n = name andalso
                                           #CFGN_type n = CFGNT_Return)
                     ) (List.map snd (Redblackmap.listItems n_dict));
end

(*
FOR DEBUGGING:
(* stop at first branch *)
val lbl_tm = ``BL_Address (Imm32 0xb08w)``;
val stop_lbl_tms = [``BL_Address (Imm32 0xb22w)``];
(* just check first branch *)
val lbl_tm = ``BL_Address (Imm32 0xb22w)``;
val stop_lbl_tms = [``BL_Address (Imm32 0xb24w)``, ``BL_Address (Imm32 0xb2aw)``];
*)
(* stop after first branch *)
(*
val lbl_tm = ``BL_Address (Imm32 0xb08w)``;
val stop_lbl_tms = [``BL_Address (Imm32 0xb24w)``, ``BL_Address (Imm32 0xb2aw)``];

open bir_block_collectionLib;
val lbl_tm = ``BL_Address (Imm32 0xb22w)``;
lookup_block_dict bl_dict_ lbl_tm
*)

val pred_conjs = [];
val syst  = init_state lbl_tm pred_conjs prog_vars;
(*
val systs_new = symb_exec_block bl_dict_ syst;
val [syst] = systs_new;

val [syst,syst2] = systs_new;
val [syst2,syst] = systs_new;
val syst = syst2;

val envl = (Redblackmap.listItems o SYST_get_env) syst;
val valsl = (Redblackmap.listItems o SYST_get_vals) syst;

Redblackmap.peek (SYST_get_vals syst, ``BVar "fr_175_countw" (BType_Imm Bit64)``)
*)

val systs = symb_exec_to_stop bl_dict_ [syst] stop_lbl_tms [];
(*
length systs
val syst = hd systs
length(SYST_get_env syst)
*)

val systs_feasible = List.filter check_feasible systs;

val countws = List.map eval_countw_in_syst systs_feasible;
val counts = List.map (wordsSyntax.dest_word_literal o
                       bir_valuesSyntax.dest_BVal_Imm64 o
                       optionSyntax.dest_some) countws;

fun find_bound comp l =
  List.foldr (fn (x,m) => if comp (x, m) then x else m) (hd l) l;

val count_max = find_bound (Arbnum.>) counts;
val count_min = find_bound (Arbnum.<) counts;

val _ = print "\n\n\n";
val _ = print ("funname = " ^ (name) ^ "\n");
val _ = print ("max = " ^ (Arbnum.toString count_max) ^ "\n");
val _ = print ("min = " ^ (Arbnum.toString count_min) ^ "\n");


(*
check_feasible (syst)
*)


(* TODO: introduce abstraction as possible value,
           the current values are concrete values (special sort),
           "top" is fresh variable,
           model unknown stack space as memory interval,
           need interval-abstraction for cycle counter to enable merging of states,
           we can start with considering max only *)

