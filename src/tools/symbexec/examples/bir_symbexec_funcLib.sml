structure bir_symbexec_funcLib =
struct

local
  open bir_symbexec_stateLib;

  val ERR      = Feedback.mk_HOL_ERR "bir_symbexec_funcLib"
  val wrap_exn = Feedback.wrap_exn   "bir_symbexec_funcLib"
in (* outermost local *)

local
  open bslSyntax;
  open bir_immSyntax;
  open bir_expSyntax;

  fun bconst_gt_try exp1 exp2 =
    if not (is_BExp_Const exp1 andalso is_BExp_Const exp2) then NONE else
    let
      val imm1 = dest_BExp_Const exp1;
      val imm2 = dest_BExp_Const exp2;

      val (i1,w1) = gen_dest_Imm imm1;
      val (i2,w2) = gen_dest_Imm imm2;

      val _ = if i1 = i2 then () else
              raise ERR "bconst_order_try" "constants must match in immtype";
    in
      SOME (Arbnum.> ((wordsSyntax.dest_word_literal w1),
                      (wordsSyntax.dest_word_literal w2)))
    end;

  (* TODO: notice that this comparison is only true under the assumption that the variable is not assigned with too high values! i.e. has space for the const in max *)
  val var_add_match_tm = bplus (bden ``x:bir_var_t``, ``y:bir_exp_t``);
  fun bvar_add_const_gt_try exp1 exp2 =
    let
      val (vs, _) = hol88Lib.match var_add_match_tm exp1;
      val bv1     = fst (List.nth (vs, 0));
      val bconst1 = fst (List.nth (vs, 1));

      val (vs, _) = hol88Lib.match var_add_match_tm exp2;
      val bv2     = fst (List.nth (vs, 0));
      val bconst2 = fst (List.nth (vs, 1));

      val _ = if identical bv1 bv2 then () else
              raise ERR "bvar_add_const_gt_try" "the variables have to match";
    in
      bconst_gt_try bconst1 bconst2
    end
    handle HOL_ERR _ => NONE;

  fun spec_gt_plus_const exp1 exp2 =
    case bconst_gt_try exp1 exp2 of
            SOME b => b
          | NONE => (
    case bvar_add_const_gt_try exp1 exp2 of
            SOME b => b
          | NONE => (  
      raise ERR "spec_gt_plus_const"
                ("don't know how to handle: " ^
                 (term_to_string exp1) ^
                 " and " ^
                 (term_to_string exp2))));

  fun merge_to_interval (SymbValInterval ((min1, max1), deps1))
                        (SymbValInterval ((min2, max2), deps2)) =
        SymbValInterval ((if spec_gt_plus_const min2 min1
                          then min1 else min2,
                          if spec_gt_plus_const max1 max2
                          then max1 else max2),
                         Redblackset.union (deps1, deps2))

    | merge_to_interval symbv1
                        (SymbValBE (exp2, deps2)) =
      merge_to_interval symbv1
                        (SymbValInterval ((exp2, exp2), deps2))

    | merge_to_interval (SymbValBE (exp1, deps1))
                        symbv2 =
      merge_to_interval (SymbValInterval ((exp1, exp1), deps1))
                        symbv2

    | merge_to_interval _ _ = raise ERR "merge_to_interval" "cannot handle symb value type";

in (* local *)

  (* TODO: - should bv be list of variables? (keep if equal in both, otherwise based on type:
                 interval merge/memory merge/ensure equality) *)
  fun merge_states_vartointerval bv bv_mem bv_sp (syst1, syst2) =
    let
      val lbl_tm = SYST_get_pc     syst1;
      val status = SYST_get_status syst1;

      val _ = if identical lbl_tm (SYST_get_pc     syst2) then () else
              raise ERR "merge_states_by_intervalvar"
                        "lbl_tm must be the same";
      val _ = if identical status (SYST_get_status syst2) then () else
              raise ERR "merge_states_by_intervalvar"
                        "status must be the same";
      (* TODO: validate that env uses the same
               set of state variables (keys) *)

      val env    = SYST_get_env  syst1;
      val vals   = SYST_get_vals syst1;
      val env2   = SYST_get_env  syst2;
      val vals2  = SYST_get_vals syst2;

      fun find_symbv_bexp vals_ bv_ =
        case find_bv_val "merge_states_vartointerval" vals_ bv_ of
           SymbValBE (e, _) => e
         | _ => raise ERR "merge_states_vartointerval" "ooops, nooo bexp";

      fun is_symbv_bexp_appfun f env_ vals_ bv_ =
        let val bv_val = find_bv_val "merge_states_vartointerval" env_ bv_; in
        if is_bvar_init bv_val then f (bden bv_val) else
        let val symbvo = SOME (find_bv_val "merge_states_vartointerval" vals_ bv_val)
                         handle _ => NONE; in
        
        case symbvo of
           SOME (SymbValBE (e, _)) => (*(print_term e; f e)*) f e
         | _ => false
        end end;

      (* create list of env vars with identical expressions in vals in both states *)
      (* keep the ones from syst1 *)
      val env_idents = Redblackset.fromList Term.compare (
        List.filter
          (fn bv_ =>
             is_symbv_bexp_appfun (fn e1 =>
                 is_symbv_bexp_appfun (identical e1) env2 vals2 bv_
             ) env vals bv_)
          (List.map fst (Redblackmap.listItems env))
        );

      (* check that SPs match *)
      val _ = if Redblackset.member (env_idents, bv_sp) then () else (
        print "........................\n\n";
        is_symbv_bexp_appfun (fn e => (print_term e; false)) env  vals  ``BVar "SP_process" (BType_Imm Bit32)``;
        is_symbv_bexp_appfun (fn e => (print_term e; false)) env2 vals2 ``BVar "SP_process" (BType_Imm Bit32)``;
        print "\n........................\n";
        raise ERR "merge_states_vartointerval" "stack pointers are not equal!"
       );

      (* merge MEM properly *)
      fun find_symbv_mem syst_ bv_ =
        case get_state_symbv "merge_states_vartointerval::getmem" bv_ syst_ of
           SymbValMem m => m
         | _ => raise ERR "merge_states_vartointerval" "ooops, nooo mem";

      val symbv_mem =
       let
        val (basem1_bv,
             mem1_layout,
             (mem1_const, mem1_globl, (bv_sp1, mem1_stack)),
             mem_deps1) = find_symbv_mem syst1 bv_mem;
        val (basem2_bv,
             mem2_layout,
             (_, mem2_globl, (bv_sp2, mem2_stack)),
             mem_deps2) = find_symbv_mem syst2 bv_mem;

        (* check that base memory variable, memory layout, and initial stack pointer variable are identical *)
        val _ = if identical basem1_bv basem2_bv then () else
                raise ERR "merge_states_vartointerval" "base memory variables are not the same";
        val _ = if mem1_layout = mem2_layout then () else
                raise ERR "merge_states_vartointerval" "memory layouts are not the same";
        val _ = if identical bv_sp1 bv_sp2 then () else
                raise ERR "merge_states_vartointerval" "initial stack pointer variables are not the same";

        (* merge the global memory *)
        val mem_globl_ads = Redblackset.fromList Arbnum.compare
              (List.map (fst) ((Redblackmap.listItems mem1_globl)@(Redblackmap.listItems mem2_globl)));
        val mem_globl = Redblackset.foldr (fn (a,m) =>
               Redblackmap.insert (m, a,
                   case (Redblackmap.peek (mem1_globl, a), Redblackmap.peek (mem2_globl, a)) of
                       (SOME (e1,deps1), SOME (e2,_)) =>
                         if identical e1 e2 then (e1, deps1) else
                         get_symbv_bexp_free_sz "memgmerge_forget" 32
                     | _ => get_symbv_bexp_free_sz "memgmerge_forget" 32)
            ) (Redblackmap.mkDict Arbnum.compare)
              mem_globl_ads;
        (* merge the stack *)
        val mem_stack_ads = Redblackset.fromList Arbnum.compare
              (List.map (fst) ((Redblackmap.listItems mem1_stack)@(Redblackmap.listItems mem2_stack)));
        val mem_stack = Redblackset.foldr (fn (a,m) =>
               Redblackmap.insert (m, a,
                   case (Redblackmap.peek (mem1_stack, a), Redblackmap.peek (mem2_stack, a)) of
                       (SOME (e1,deps1), SOME (e2,_)) =>
                         if identical e1 e2 then (e1, deps1) else
                         get_symbv_bexp_free_sz "memgmerge_forget" 32
                     | _ => get_symbv_bexp_free_sz "memgmerge_forget" 32)
            ) (Redblackmap.mkDict Arbnum.compare)
              mem_stack_ads;
        (* compute deps *)
        val mem_deps =
             List.foldr (fn ((_,(_,d)),s) =>
                Redblackset.union (d, s)
              )
              (Redblackset.fromList Term.compare [basem1_bv, bv_sp1])
              ((Redblackmap.listItems mem_globl)@(Redblackmap.listItems mem_stack));
       in
         SymbValMem (basem1_bv,
             mem1_layout,
             (mem1_const, mem_globl, (bv_sp1, mem_stack)),
             mem_deps)
       end;
      val bv_fresh_mem = get_bvar_fresh bv;

      (* merge BIR variable bv to interval *)
      val symbv1  = get_state_symbv "merge_states_vartointerval" bv syst1;
      val symbv2  = get_state_symbv "merge_states_vartointerval" bv syst2;

      val bv_fresh = get_bvar_fresh bv;
      val symbv    = merge_to_interval symbv1 symbv2;

      (* find pred_bvs "prefix" *)
      (* TODO: bad, "quick" and dirty implementation... improve it *)
      fun identical_prefix (x::xs) (y::ys) acc =
            if identical (find_symbv_bexp vals x)
                         (find_symbv_bexp vals2 y) then
              identical_prefix xs ys (x::acc)
            else ((*
              (print ( ((symbv_to_string o find_bv_val "merge_states_vartointerval" vals) x) ^ "\n"));
              (print ( ((symbv_to_string o find_bv_val "merge_states_vartointerval" vals2) y) ^ "\n"));*)
              List.rev acc)
	| identical_prefix _ _ acc = List.rev acc
      (* take exactly two for now *)
      (* notice that in pred the list head is the lastly added pred *)
      val pred_bvs_prefix_len = length (identical_prefix (List.rev (SYST_get_pred syst1)) (List.rev (SYST_get_pred syst2)) []);
      val _ = if pred_bvs_prefix_len = 3 then () else
              print ("pred prefix length : " ^ (Int.toString pred_bvs_prefix_len) ^ "\n");
      val pred_bvs = List.rev (List.take (List.rev (SYST_get_pred syst1), pred_bvs_prefix_len));
      val _ = if list_eq identical
                   pred_bvs
                   (List.rev (List.take (List.rev (SYST_get_pred syst2), pred_bvs_prefix_len)))
              then () else
                raise ERR "merge_states_by_intervalvar" "pred prefix must be the equal";

      (* for our application, merging needs to preserve
         at least: pred "prefix", SP, something about MEM *)
      (* for now, scatch env completely, and use fresh variables *)
      val env_vars = List.map I (Redblackmap.listItems env);
      val env' = Redblackmap.fromList Term.compare (
        List.map (fn (bv, bv_val_) =>
         (bv, if Redblackset.member (env_idents, bv) then
                bv_val_
              else
                get_bvar_fresh bv)
        ) env_vars);

      (* TODO: collect vals for pred_bvs *)
      (* for now, this can be conveniently done with the function to tidy up states *)

      val syst_merged =
      (update_envvar bv_mem bv_fresh_mem o
       insert_symbval bv_fresh_mem symbv_mem o
       update_envvar bv bv_fresh o
       insert_symbval bv_fresh symbv)
      (SYST_mk lbl_tm
               env'
               status
               []
               pred_bvs
               vals);
      val syst_new = tidyup_state_vals syst_merged;
    in
      syst_new
    end;
end (* local *)

end (* outermost local *)

end (* struct *)
