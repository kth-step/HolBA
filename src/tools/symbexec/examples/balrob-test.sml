open HolKernel Parse

open binariesLib;
open binariesCfgLib;
open binariesMemLib;

open bir_symbexec_stateLib;
open bir_symbexec_coreLib;
open bir_symbexec_stepLib;
open bir_symbexec_sumLib;
open bir_countw_simplificationLib;

open commonBalrobScriptLib;

val entry_labels = ["motor_prep_input",
                    "__lesf2",
                    "__clzsi2",
                    "__aeabi_f2iz",
                    "pid_msg_write",
                    "timer_read"];
val entry_label = List.nth (entry_labels, 0);


val name   = entry_label;

val _ = print ("\n\nfunname = " ^ (name) ^ "\n\n");

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

val cfb = false;

val systs = symb_exec_to_stop (abpfun cfb) n_dict bl_dict_ [syst] stop_lbl_tms [];
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
val syst = hd systs_noassertfailed;
*)

val systs_feasible = List.filter check_feasible systs_noassertfailed;
val _ = print ("number of feasible paths found: " ^ (Int.toString (length systs_feasible)));
val _ = print "\n\n";

val systs_tidiedup = List.map tidyup_state_vals systs_feasible;
val _ = print "finished tidying up all paths.\n\n";


(*
val countw_symbvs = List.map (symbv_to_string o get_state_symbv "script" bv_countw) systs_tidiedup;

val syst1 = List.nth (systs_tidiedup, 1);
val syst2 = List.nth (systs_tidiedup, 2);

val syst = merge_states_vartointerval bv_countw (syst1, syst2);

val syst = List.nth (systs_tidiedup, 0);
val syst = List.nth (systs_tidiedup, 1);
val syst = List.nth (systs_tidiedup, 2);
val syst = List.nth (systs_tidiedup, 3);

val envl = (Redblackmap.listItems o SYST_get_env) syst;
val valsl = (Redblackmap.listItems o SYST_get_vals) syst;
*)

(*
val syst = hd systs_tidiedup;
val syst = List.nth (systs_feasible, 0);

val bv_fr = ``BVar "fr_10_tmp_SP_process" (BType_Imm Bit32)``;
val bv_fr = ``(BVar "fr_15_SP_process" (BType_Imm Bit32))``;

val bv_fr = ``(BVar "fr_57_R3" (BType_Imm Bit32))``;

val bv_fr = ``BVar "fr_82_PSR_Z" BType_Bool``;
val bv_fr = ``BVar "fr_75_R3" (BType_Imm Bit32)``;
val bv_fr = ``BVar "fr_43_R2" (BType_Imm Bit32)``;

val bv_fr = ``BVar "fr_353_MEM" (BType_Mem Bit32 Bit8)``;

find_bv_val "script" (SYST_get_vals syst) bv_fr;
(Redblackset.listItems o deps_of_symbval "script") (find_bv_val "script" (SYST_get_vals syst) bv_fr);

expand_bv_fr_in_syst bv_fr syst
*)

val _ = print ("num preds: " ^ ((Int.toString o length o SYST_get_pred o List.nth) (systs_tidiedup, 0)) ^ "\n");

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


(*
check_feasible (syst)
*)


(* TODO:   model unknown stack space as memory interval,
           need interval-abstraction for cycle counter to enable merging of states *)

    (* - derive constants from the state predicate (update both places to not loose information) *)
    (* - constant propagation in expressions *)






(*
val envl = (Redblackmap.listItems o SYST_get_env) func_syst;
val valsl = (Redblackmap.listItems o SYST_get_vals) func_syst;
*)


val (func_lbl_tm, func_precond, func_systs) = syst_summary;

val entry_label = "motor_set_l";
(*
"c1c" call
"c20" return
*)

val name   = entry_label;

val _ = print ("\n\nfunname = " ^ (name) ^ "\n\n");

val lbl_tm = (mk_lbl_tm o valOf o mem_find_symbol_addr_) name;

val stop_lbl_tms = [func_lbl_tm]; (*``BL_Address (Imm32 0xc1cw)``];*)

val syst = init_state lbl_tm prog_vars;
val syst = state_make_interval bv_countw syst;
val syst = state_make_mem bv_mem
                          (Arbnum.fromInt mem_sz_const, Arbnum.fromInt mem_sz_globl, Arbnum.fromInt mem_sz_stack)
                          (mem_read_byte binary_mem)
                          bv_sp
                          syst;

val syst = state_add_preds "init_pred" pred_conjs syst;

val _ = print "initial state created.\n\n";

val cfb = false;

val systs = symb_exec_to_stop (abpfun cfb) n_dict bl_dict_ [syst] stop_lbl_tms [];
val _ = print "finished exploration of all paths.\n";
val _ = print ("number of paths found: " ^ (Int.toString (length systs)));
val _ = print "\n\n";

val (systs_noassertfailed, systs_assertfailed) =
  List.partition (fn syst => not (identical (SYST_get_status syst) BST_AssertionViolated_tm)) systs;
val _ = print ("number of \"no assert failed\" paths found: " ^ (Int.toString (length systs_noassertfailed)));
val _ = print "\n\n";



(* now instanciation ... *)
val syst = if length systs_noassertfailed = 1 then hd systs_noassertfailed else
           raise ERR "script" "more than one symbolic state in current path/state";

val systs_inst = instantiate_summaries [syst_summary] [syst];

(*
val syst_inst = hd systs_inst;
val envl = (Redblackmap.listItems o SYST_get_env) syst_inst;
val valsl = (Redblackmap.listItems o SYST_get_vals) syst_inst;
*)

(* ... and continuation up to the return of the function *)
val _ = print "\n========================\n";
val _ = print "continue after instantiation...\n\n";

(*
open bir_block_collectionLib;
val lbl_tm = SYST_get_pc syst_inst;
lookup_block_dict bl_dict_ lbl_tm
 *)

val stop_lbl_tms = [``BL_Address (Imm32 0xc74w)``];

val systs = symb_exec_to_stop (abpfun cfb) n_dict bl_dict_ systs_inst stop_lbl_tms [];

val (systs_noassertfailed, systs_assertfailed) =
  List.partition (fn syst => not (identical (SYST_get_status syst) BST_AssertionViolated_tm)) systs;
val _ = print ("number of \"no assert failed\" paths found: " ^ (Int.toString (length systs_noassertfailed)));
val _ = print "\n\n";

(*
val syst = hd systs_assertfailed;
val syst = hd systs_noassertfailed;
*)

val systs_feasible = List.filter check_feasible systs_noassertfailed;
val _ = print ("number of feasible paths found: " ^ (Int.toString (length systs_feasible)));
val _ = print "\n\n";

val systs_tidiedup = List.map tidyup_state_vals systs_feasible;
val _ = print "finished tidying up all paths.\n\n";

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
