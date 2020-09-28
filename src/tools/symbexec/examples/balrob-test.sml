open HolKernel Parse

open binariesLib;
open binariesCfgLib;
open binariesMemLib;

open bir_symbexec_stateLib;
open bir_symbexec_coreLib;
open bir_symbexec_stepLib;
open bir_countw_simplificationLib;

open commonBalrobScriptLib;

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

val envl = (Redblackmap.listItems o SYST_get_env) syst;
val valsl = (Redblackmap.listItems o SYST_get_vals) syst;
*)

(*
val syst = hd systs_tidiedup;
val syst = List.nth (systs_feasible, 0);


val bv_fr = ``BVar "fr_10_tmp_SP_process" (BType_Imm Bit32)``;
val bv_fr = ``(BVar "fr_15_SP_process" (BType_Imm Bit32))``;

val bv_fr = ````;
val bv_fr = ``(BVar "fr_57_R3" (BType_Imm Bit32))``;


val bv_fr = ``BVar "fr_82_PSR_Z" BType_Bool``;
val bv_fr = ``BVar "fr_75_R3" (BType_Imm Bit32)``;
val bv_fr = ``BVar "fr_43_R2" (BType_Imm Bit32)``;

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





(* find correct function summary *)
val (func_lbl_tm, func_precond, func_systs) = syst_summary;
val func_syst =
        if length func_systs = 1 then hd func_systs else
        raise ERR "script" "more than one symbolic state in function summary";

(*
val envl = (Redblackmap.listItems o SYST_get_env) func_syst;
val valsl = (Redblackmap.listItems o SYST_get_vals) func_syst;
*)




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

(*
Redblackset.listItems (freevars_of_vals vals_func)
Redblackset.listItems (freevars_of_vals vals_strt)
*)
fun freevars_of_vals vals =
  Redblackmap.foldr
    (fn (_, symbv, freevars) =>
      Redblackset.union (
        Redblackset.filter (is_bvar_free vals) (deps_of_symbval "freevars_of_vals" symbv)
        , freevars))
    symbvalbe_dep_empty
    vals;

(*
Redblackmap.listItems vals_1
Redblackmap.listItems varsubstmap_2
Redblackmap.listItems vals_func

val prfrvars = ;
val (vals, varsubstmap) = (vals_1, varsubstmap_2);
val prvall = (Redblackmap.listItems vals_func);
*)
fun subst_vals_and_append prfrvars (vals, varsubstmap) [] = (vals, varsubstmap)
  | subst_vals_and_append prfrvars (vals, varsubstmap) prvall =
     let
       val (prvall_r, prvall_l) = List.partition (fn (_,symbv) =>
         List.all
           (fn bv =>
              isSome (Redblackmap.peek (varsubstmap, bv)) orelse
              Redblackset.member (prfrvars, bv))
         (Redblackset.listItems (deps_of_symbval "subst_vals_and_append" symbv))
        ) prvall;

       val _ = if not (List.null prvall_r) then () else
               raise ERR "subst_vals_and_append" "cannot continue substitution: loop?";

       val (vals', varsubstmap') = List.foldl
         (fn ((bv, symbv), (vals_, varsubstmap_)) =>
           let
             val bv_fr = get_bvar_fresh bv;
             (* TODO: subst, gen fresh vars if not mapped
                     (i.e. must be in prfrvars then) *)
             val symbv_subst = symbv;
           in
             (Redblackmap.insert (vals_, bv_fr, symbv_subst),
              Redblackmap.insert (varsubstmap_, bv, bv_fr))
           end)
         (vals, varsubstmap)
         prvall_r;
     in
       subst_vals_and_append prfrvars (vals', varsubstmap') prvall_l
     end;

(*
    val (vals_3, varsubstmap_3) =
      subst_vals_and_append
        (vals_1, varsubstmap_2)
        (Redblackmap.listItems vals_func);
    val varsubstmap = varsubstmap_3;
    val env = env_func;

Redblackmap.listItems env
Redblackmap.listItems varsubstmap
Redblackmap.listItems (subst_in_env varsubstmap env)
*)
fun subst_in_env varsubstmap env =
  Redblackmap.map
    (fn (_, bv_val) =>
     Redblackmap.find (varsubstmap, bv_val)
     handle _ => bv_val)
     (* raise ERR "subst_in_env" ("didn't find mapping for " ^ (term_to_string bv_val)) *)
    env;

val syst_inst =
  let
    val syst_strt = syst;

    val lbl_tm_func = func_lbl_tm;
    val syst_func = func_syst;

    (* pc: take after func pc *)
    val pc_strt = SYST_get_pc syst_strt;
    val _ = if identical lbl_tm_func pc_strt then () else
        raise ERR "script_syst_instanciate" "starting label doesn't match";
    val pc_inst = SYST_get_pc syst_func;

    (* starting syst needs to be running *)
    val status_strt = SYST_get_status syst_strt;
    val _ = if identical BST_Running_tm status_strt then () else
            raise ERR "script_syst_instanciate" "starting status needs to be running";
    val status_inst = SYST_get_status syst_func;

    (* for now we don't deal with observations here *)
    val obss_strt = SYST_get_obss syst_strt;
    val obss_func = SYST_get_obss syst_func;
    val _ = if List.null obss_strt andalso
               List.null obss_func then () else
            raise ERR "script_syst_instanciate" "cannot handle observations for now";
    val obss_inst = [];

    (* prep: vals and env *)
    val vals_strt = SYST_get_vals syst_strt;
    val vals_func = SYST_get_vals syst_func;
    val env_strt  = SYST_get_env  syst_strt;
    val env_func  = SYST_get_env  syst_func;

    (* pred: take starting path predicate *)
    val pred_strt = SYST_get_pred syst_strt;
    (* TODO: check precondition entailment *)
    val pred_inst = pred_strt;

    (* vals and env *)
    (* 1. initialize new vals with starting vals *)
    val vals_1 = vals_strt;

    (* 2. initialize var substitute map from starting env *)
    val varsubstmap_2 =
      List.foldl
        (fn ((bv, bv_val), map) =>
          Redblackmap.insert (map, get_bvar_init bv, bv_val))
        (Redblackmap.mkDict Term.compare)
        (Redblackmap.listItems env_strt);

    (* 3. incrementally substitute vars in func vals(&deps), and add to vals_1 and varsubstmap *)
    val prfrvars = freevars_of_vals vals_func;
    val (vals_3, varsubstmap_3) =
      subst_vals_and_append
        prfrvars
        (vals_1, varsubstmap_2)
        (Redblackmap.listItems vals_func);
    val vals_inst = vals_3;

    (* 4. apply substitution to func env *)
    val env_inst  = subst_in_env varsubstmap_3 env_func;
  in
    SYST_mk pc_inst
            env_inst
            status_inst
            obss_inst
            pred_inst
            vals_inst
  end;

(*
Redblackmap.listItems env_func;
Redblackmap.listItems env_inst;

val envl = (Redblackmap.listItems o SYST_get_env) syst_inst;
val valsl = (Redblackmap.listItems o SYST_get_vals) syst_inst;
*)

val systs_inst_tidiedup = tidyup_state_vals syst_inst;

(* ... and continuation *)

