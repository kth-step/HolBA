open HolKernel Parse

open binariesLib;
open binariesCfgLib;

open bir_symbexec_stateLib;
open bir_symbexec_coreLib;
open bir_symbexec_stepLib;
open bir_countw_simplificationLib;

val entry_labels = ["motor_prep_input",
                    "__lesf2",
                    "__clzsi2",
                    "__aeabi_f2iz",
                    "pid_msg_write",
                    "timer_read"];
val entry_label = List.nth (entry_labels, 0);

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
                                           cfg_node_type_eq (#CFGN_type n, CFGNT_Return))
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

(* TODO: how much space do we actually have? we should "enforce" this with the linker... *)
val stack_size  = 0x100;
val stack_start = 0x10000000 + 0x2000 -16;
val stack_end   = stack_start - stack_size;

val stack_space_req = 0x80;

val pred_conjs = [
``BExp_BinPred BIExp_Equal
    (BExp_BinExp BIExp_And
        (BExp_Den (BVar "SP_process" (BType_Imm Bit32)))
        (BExp_Const (Imm32 3w)))
    (BExp_Const (Imm32 0w))``,
``BExp_BinExp BIExp_And
          (BExp_BinPred BIExp_LessOrEqual
             (BExp_Den (BVar "SP_process" (BType_Imm Bit32)))
             (BExp_Const (Imm32 ^(wordsSyntax.mk_wordii(stack_start, 32)))))
          (BExp_BinPred BIExp_LessThan
             (BExp_Const (Imm32 ^(wordsSyntax.mk_wordii(stack_end + stack_space_req, 32))))
             (BExp_Den (BVar "SP_process" (BType_Imm Bit32))))``
];

val syst = init_state lbl_tm prog_vars;
val syst = state_assign_bv ``BVar "countw" (BType_Imm Bit64)`` ``BExp_Const (Imm64 0w)`` syst;
(*
val syst = state_make_interval ``BVar "countw" (BType_Imm Bit64)`` syst;
*)
val syst = state_add_preds "init_pred" pred_conjs syst;

val _ = print "initial state created.\n\n";
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

val systs = symb_exec_to_stop false n_dict bl_dict_ [syst] stop_lbl_tms [];
val _ = print "finished exploration of all paths.\n";
val _ = print ("number of paths found: " ^ (Int.toString (length systs)));
val _ = print "\n\n";
(*
length systs
val syst = hd systs
length(SYST_get_env syst)
*)
val (systs_noassertfailed, systs_assertfailed) =
  List.partition (fn syst => not (identical (SYST_get_status syst) BST_AssertionViolated_tm)) systs;
val _ = print ("number of \"no assert failed\" paths found: " ^ (Int.toString (length systs_noassertfailed)));
val _ = print "\n\n";

(*
val syst = hd systs_assertfailed;
*)

val systs_feasible = List.filter check_feasible systs_noassertfailed;
val _ = print ("number of feasible paths found: " ^ (Int.toString (length systs_feasible)));
val _ = print "\n\n";

val systs_tidiedup = List.map tidyup_state_vals systs_feasible;
val _ = print "finished tidying up all paths.\n\n";

val countw_symbvs = List.map get_countw_in_syst systs_tidiedup;

val countws = List.map eval_countw_in_syst systs_tidiedup;
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


(* TODO:   model unknown stack space as memory interval,
           need interval-abstraction for cycle counter to enable merging of states *)

    (* - derive constants from the state predicate (update both places to not loose information) *)
    (* - constant propagation in expressions *)

