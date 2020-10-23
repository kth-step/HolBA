structure bir_symbexec_sumLib =
struct

local
  open bir_symbexec_stateLib;

  val ERR      = Feedback.mk_HOL_ERR "bir_symbexec_sumLib"
  val wrap_exn = Feedback.wrap_exn   "bir_symbexec_sumLib"
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


local
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

fun subst_in_symbv_bexp (vals, varsubstmap) (be,_) =
  let
    open bir_expSyntax;
    open bir_constpropLib;
    open bir_exp_helperLib;

    val debugOn = false;

    val _ = if not debugOn then () else (
            print ("\n==============\n");
            print_term be);

    val be_vars = get_birexp_vars be;

    fun subst_fun2 map (bev, (e, vars)) =
      let
        val bv_ofvals = find_bv_val "subst_fun2" map bev;
        val (exp, vars') = (mk_BExp_Den bv_ofvals, bv_ofvals::vars);
      in
        (subst_exp (bev, exp, e), vars')
      end;

    val besubst_with_vars = List.foldr (subst_fun2 varsubstmap) (be, []) be_vars;

    val symbv = bir_symbexec_coreLib.compute_val_and_resolve_deps [] vals besubst_with_vars;

    val _ = if not debugOn then () else
            print ("-------\n" ^ (symbv_to_string symbv) ^ "\n");
  in
    symbv
  end;

fun subst_in_symbv_interval (vals, varsubstmap) ((be1, be2), deps) =
  let
    open bir_expSyntax;

    val debugOn = false;

    val _ = if not debugOn then () else (
            print ("\n==============\n");
            print_term be1;
            print_term be2);

    val symbv_min = subst_in_symbv_bexp (vals, varsubstmap) (be1,deps);
    val symbv_max = subst_in_symbv_bexp (vals, varsubstmap) (be2,deps);

    val _ = if not debugOn then () else
            print ("------min-\n" ^ (symbv_to_string symbv_min) ^ "\n");
    val _ = if not debugOn then () else
            print ("------max-\n" ^ (symbv_to_string symbv_max) ^ "\n");

    val (be_min, deps_min) =
      case symbv_min of
         SymbValInterval ((bemin, _), deps) => (bemin, deps)
       | _ => raise ERR "subst_in_symbv_interval" "min did not result in interval";

    val (be_max, deps_max) =
      case symbv_max of
         SymbValInterval ((_, bemax), deps) => (bemax, deps)
       | _ => raise ERR "subst_in_symbv_interval" "max did not result in interval";

    val _ = if Redblackset.equal (deps_min, deps_max) then () else
            raise ERR "subst_in_symbv_interval" "dependency set is not equal";

    val symbv = SymbValInterval ((be_min, be_max), deps_min);

    val _ = if not debugOn then () else
            print ("-------\n" ^ (symbv_to_string symbv) ^ "\n");
  in
    symbv
  end;

val sy_sp_var = ``BVar "sy_SP_process" (BType_Imm Bit32)``;
val sy_sp_minus_zero_exp =
  ``BExp_BinExp BIExp_Minus (BExp_Den ^sy_sp_var)
          (BExp_Const (Imm32 0w))``;
fun subst_in_symbv_mem (vals, varsubstmap) mem =
  let
    val debugOn = false;

    val (basem_bv,
         layout,
         (_, mem_globl, (bv_sp, mem_stack)),
         deps) = mem;

    val _ = if not debugOn then () else (
            print ("\n==============\n");
            print_term basem_bv;
            print ("deps: " ^ (Int.toString (Redblackset.numItems deps)) ^ "\n"));

    (* get base memory *)
    val basemem = case Redblackmap.peek (varsubstmap, basem_bv) of
                     NONE => raise ERR "subst_in_symbv_mem" "couldn't find base memory"
                   | SOME basemem_bv => (
                  case find_bv_val "subst_in_symbv_mem::variablenotfound_mem" vals basemem_bv of
                     SymbValMem m => m
                   | _ => raise ERR "subst_in_symbv_mem" "wrong value type mem");

    val (b_basem_bv,
         b_layout,
         (b_mem_const, b_mem_globl, (b_bv_sp, b_mem_stack)),
         b_deps) = basemem;

    val _ = if layout = b_layout then () else
            raise ERR "subst_in_symbv_mem" "memory layouts are not the same";

    (* get base relative sp *)
    val be_sp   = case Redblackmap.peek (varsubstmap, bv_sp) of
                     NONE => raise ERR "subst_in_symbv_mem" "couldn't find sp"
                   | SOME bv_sp_ofvals => (
                  (* need this to ensure shape of formula for extracting the offset value,
                     like this it's not very general but works for our cases now *)
                  if identical bv_sp_ofvals sy_sp_var then
                    sy_sp_minus_zero_exp
                  else
                  case find_bv_val "subst_in_symbv_mem::variablenotfound_sp" vals bv_sp_ofvals of
                     SymbValBE (be,_) => be
                   | _ => raise ERR "subst_in_symbv_mem" "wrong value type sp");

    val _ = if not debugOn then () else (
            print ("-------\n");
            print_term be_sp);

    val sp_offset =
     let
      val match_tm = ``
        BExp_BinExp BIExp_Minus (BExp_Den x)
          (BExp_Const (Imm32 y))``;
      val (vs, _) = hol88Lib.match match_tm be_sp
                    handle _ => raise ERR "subst_in_symbv_mem" "unable to match sp expression";
      val sp_offset_bv = fst (List.nth (vs, 0));
      val imm_val = fst (List.nth (vs, 1));

      val _ = if identical sp_offset_bv b_bv_sp then () else
              raise ERR "subst_in_symbv_mem" "sp variable not identical";
     in
       wordsLib.dest_word_literal imm_val
     end;

    val _ = if not debugOn then () else (
            print ("-------\n");
            print ((Arbnum.toString sp_offset) ^ "\n"));

    (* update expressions in all memory locations *)
    fun update_mem_entry (_,(be_,deps_)) =
      let
        val symbv_ = subst_in_symbv_bexp (vals, varsubstmap) (be_,deps_);
      in
        case symbv_ of
           SymbValBE v_ => v_
         | _ => raise ERR "subst_in_symbv_mem" "a memory location didn't evaluate to symb val be"
      end;

    val mem_globl_ = Redblackmap.map update_mem_entry mem_globl;
    val mem_stack_ = Redblackmap.map update_mem_entry mem_stack;

    (* merge the global memory *)
    val mem_globl_new =
      Redblackmap.foldr (fn (a, v, m) =>
          Redblackmap.insert (m, a, v)
        )
        b_mem_globl
        mem_globl_;

    (* merge the stack memory, with stack pointer displacement *)
    val mem_stack_new =
      Redblackmap.foldr (fn (a, v, m) =>
          Redblackmap.insert (m, Arbnum.+(sp_offset, a), v)
        )
        b_mem_stack
        mem_stack_;

    (* compute deps *)
    val deps_new =
         List.foldr (fn ((_,(_,d)),s) =>
            Redblackset.union (d, s)
          )
          (Redblackset.fromList Term.compare [b_basem_bv, b_bv_sp])
          ((Redblackmap.listItems mem_globl_new)@(Redblackmap.listItems mem_stack_new));

    val symbv =
      SymbValMem
       (b_basem_bv,
         b_layout,
         (b_mem_const, mem_globl_new, (b_bv_sp, mem_stack_new)),
         deps_new);

    val _ = if not debugOn then () else
            print ("-------\n" ^ (symbv_to_string_raw true symbv) ^ "\n");
  in
    symbv
  end;

fun subst_in_symbv (vals, varsubstmap) (SymbValBE symbvbe) =
      subst_in_symbv_bexp (vals, varsubstmap) symbvbe
  | subst_in_symbv (vals, varsubstmap) (SymbValInterval symbvint) =
      subst_in_symbv_interval (vals, varsubstmap) symbvint
  | subst_in_symbv (vals, varsubstmap) (SymbValMem symbvmem) =
      subst_in_symbv_mem (vals, varsubstmap) symbvmem;
(*
  | subst_in_symbv (vals, varsubstmap) symbv =
      raise ERR "subst_in_symbv" ("cannot handle symbolic value type: " ^ (symbv_to_string symbv));
*)

(*
Redblackmap.listItems vals_1
Redblackmap.listItems varsubstmap_2
Redblackmap.listItems vals_func

val (vals, varsubstmap) = (vals_1, varsubstmap_2);
val prvall = (Redblackmap.listItems vals_func);
*)
fun subst_vals_and_append (vals, varsubstmap) [] = (vals, varsubstmap)
  | subst_vals_and_append (vals, varsubstmap) prvall =
     let
       val (prvall_r, prvall_l) = List.partition (fn (_,symbv) =>
         List.all
           (fn bv => isSome (Redblackmap.peek (varsubstmap, bv)))
         (Redblackset.listItems (deps_of_symbval "subst_vals_and_append" symbv))
        ) prvall;

       val _ = if not (List.null prvall_r) then () else
               raise ERR "subst_vals_and_append" "cannot continue substitution: loop?";

       val (vals', varsubstmap') = List.foldl
         (fn ((bv, symbv), (vals_, varsubstmap_)) =>
           let
             val bv_fr = get_bvar_fresh bv;
             val symbv_subst = subst_in_symbv (vals, varsubstmap) symbv;
           in
             (Redblackmap.insert (vals_, bv_fr, symbv_subst),
              Redblackmap.insert (varsubstmap_, bv, bv_fr))
           end)
         (vals, varsubstmap)
         prvall_r;
     in
       subst_vals_and_append (vals', varsubstmap') prvall_l
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

in (* local *)

fun instantiate_summary_single syst_summary syst =
  let
    val (func_lbl_tm, func_precond, func_syst) = syst_summary;

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

    (* 3. insert mappings for all free variables in func vals -> fresh variables *)
    val varsubstmap_3 =
      Redblackset.foldr
        (fn (bv_free, map) =>
          if is_bvar_init bv_free then map else
          Redblackmap.insert(map, bv_free, get_bvar_fresh bv_free))
        varsubstmap_2
        (freevars_of_vals vals_func);

    (* 4. incrementally substitute vars in func vals(&deps), and add to vals_1 and varsubstmap_3 *)
    val (vals_4, varsubstmap_4) =
      subst_vals_and_append
        (vals_1, varsubstmap_3)
        (Redblackmap.listItems vals_func);
    val vals_inst = vals_4;

    (* 5. apply substitution to func env *)
    val env_inst  = subst_in_env varsubstmap_4 env_func;

    (* 6. create state and tidy up *)
    val syst_after_raw =
      SYST_mk pc_inst
              env_inst
              status_inst
              obss_inst
              pred_inst
              vals_inst;
    val syst_after = tidyup_state_vals syst_after_raw;
  in
    syst_after
  end;

fun instantiate_summary sum syst =
  let
    val (sum_lbl_tm, sum_precond, sum_systs) = sum;

    fun instantiate sum_syst =
      instantiate_summary_single (sum_lbl_tm, sum_precond, sum_syst) syst;
  in
    List.map instantiate sum_systs
  end;

fun instantiate_summaries sums systs =
  flatten (List.map (fn syst =>
  let
    val lbl_tm = SYST_get_pc syst;

    val sums_select = List.filter (fn (x,_,_) => identical lbl_tm x) sums;
  in
    if length sums_select = 0 then
      [syst]
    else if length sums_select = 1 then
      instantiate_summary (hd sums_select) syst
    else
      raise ERR "instantiate_sumaries"
                "need that not multiple summaries match"
  end) systs);

end (* local *)


end (* outermost local *)

end (* struct *)
