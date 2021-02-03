structure bir_obs_modelLib :> bir_obs_modelLib =
struct

open HolKernel boolLib liteLib simpLib Parse bossLib;

  (* error handling *)
  val libname  = "bir_obs_modelLib"
  val ERR      = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname

local
    open bir_obs_modelTheory;
in

structure bir_pc_model : OBS_MODEL =
struct
val obs_hol_type = ``bir_val_t``;
fun add_obs mb t = rand (concl (EVAL ``add_obs_pc ^mb ^t``));
end

structure bir_arm8_mem_addr_model : OBS_MODEL =
struct
val obs_hol_type = ``bir_val_t``;
fun add_obs mb t = rand (concl (EVAL ``add_obs_mem_addr_armv8 ^mb ^t``));
end

structure bir_arm8_mem_addr_pc_model : OBS_MODEL =
struct
val obs_hol_type = ``bir_val_t``;
fun add_obs mb t = rand (concl (EVAL ``add_obs_mem_addr_pc_armv8 ^mb ^t``));
end

structure bir_arm8_cache_line_model : OBS_MODEL =
struct
val obs_hol_type = ``bir_val_t``;
fun add_obs mb t = rand (concl (EVAL ``add_obs_cache_line_tag_index_armv8 ^mb ^t``));
end

structure bir_arm8_cache_line_tag_model : OBS_MODEL =
struct
val obs_hol_type = ``bir_val_t``;
fun add_obs mb t = rand (concl (EVAL ``add_obs_cache_line_tag_armv8 ^mb ^t``));
end

structure bir_arm8_cache_line_index_model : OBS_MODEL =
struct
val obs_hol_type = ``bir_val_t``;
fun add_obs mb t = rand (concl (EVAL ``add_obs_cache_line_index_armv8 ^mb ^t``));
end

structure bir_arm8_cache_line_subset_model : OBS_MODEL =
struct
val obs_hol_type = ``bir_val_t``;
fun add_obs mb t = rand (concl (EVAL ``add_obs_cache_line_subset_armv8 ^mb ^t``));
end

structure bir_arm8_cache_line_subset_page_model : OBS_MODEL =
struct
val obs_hol_type = ``bir_val_t``;
fun add_obs mb t = rand (concl (EVAL ``add_obs_cache_line_subset_page_armv8 ^mb ^t``));
end

end (* local *)

local

(* ================================================ *)
open bir_programSyntax
open bir_program_labelsTheory
open bir_expSyntax
open bir_block_collectionLib;
open bir_cfgLib;
(* ================================================ *)

    val Obs_dict =  Redblackmap.insert (Redblackmap.mkDict Term.compare, ``dummy``, ([]:term list));
    fun mk_key_from_address64 i addr = (mk_BL_Address o bir_immSyntax.mk_Imm64 o wordsSyntax.mk_word) (addr, Arbnum.fromInt i);

    (* single entry recursion, stop at first revisit or exit *)
    fun traverse_graph (g:cfg_graph) entry visited acc =
	let
	    val n = lookup_block_dict_value (#CFGG_node_dict g) entry "traverse_graph" "n";
	    val targets = #CFGN_targets n;
	    val descr_o = #CFGN_hc_descr n;
	    val n_type  = #CFGN_type n;
		
	    val acc_new = (if cfg_node_type_eq (n_type, CFGNT_CondJump) then [entry] else [])@acc;
	    val targets_to_visit = List.filter (fn x => List.all (fn y => not (identical x y)) visited) targets;
	    
	in
	    List.foldr (fn (entry',(visited',acc')) => traverse_graph g entry' visited' acc') 
		       (entry::visited, acc_new) 
		       targets_to_visit
	end;

    fun traverse_graph_branch (g:cfg_graph) depth  entry visited acc =
	let
	    val n = lookup_block_dict_value (#CFGG_node_dict g) entry "traverse_graph" "n";
	    val targets = #CFGN_targets n;
	    val descr_o = #CFGN_hc_descr n;
	    val n_type  = #CFGN_type n;

	    val (targets_to_visit, acc_new) = 
		if (cfg_node_type_eq (n_type, CFGNT_CondJump)) orelse (depth = 0) 
		then ([], (if cfg_node_type_eq (n_type, CFGNT_CondJump) then [entry] else [])@acc)
		else (List.filter (fn x => List.all (fn y => not (identical x y)) visited) targets,
		      (if cfg_node_type_eq (n_type, CFGNT_CondJump) then [entry] else [])@acc)
	in

	    List.foldr (fn(entry',(visited',acc')) => traverse_graph_branch g (depth-1) entry' visited' acc') 
		       (entry::visited, acc_new) 
		       targets_to_visit
	end;
    (* TODO ensure the lists of obs in the result are in program order *)
    fun extract_branch_obs targets g depth bl_dict =
	let  
	    val f =  (fn l => Redblackmap.find (bl_dict, l)
                           |> bir_programSyntax.dest_bir_block
			   |> not o listSyntax.is_nil o #2)
	    fun extract_obs labels = 
		List.map (fn label => 
			     let val block = Redblackmap.find (bl_dict, label)
				 val (_, statements, _) = bir_programSyntax.dest_bir_block block
				 val obs = find_terms is_BStmt_Observe statements (* TODO this should be manual traversal to ensure preservation of program order *)
			     in
				 filter (fn obs => (#3 o dest_BStmt_Observe) obs 
						|> listSyntax.mk_hd 
						|> (rhs o concl o EVAL) 
						|> (not o is_BExp_Const)) obs
			     end) (rev (filter f labels)) (* TODO sort by program order *)
		 |> flatten

	    val bn1::bn2::_ = List.map (fn t => fst (traverse_graph_branch g depth (t) [] [])) targets;
	    val b1_nodes = List.filter (fn x => (List.all (fn y => not (identical x y)) bn1)) bn2;
	    val b2_nodes = List.filter (fn x => (List.all (fn y => not (identical x y)) bn2)) bn1;
      (* val _ = List.app print_term (extract_obs b1_nodes); *)
	    val Obs_dict = Redblackmap.insert(Obs_dict, hd targets, extract_obs b1_nodes);
	    val Obs_dict = Redblackmap.insert(Obs_dict, last targets, extract_obs b2_nodes);
	in
	    Obs_dict
	end

    fun nub_with eq [] = []
      | nub_with eq (x::xs) = x::(nub_with eq (List.filter (fn y => not (eq (y, x))) xs))

    fun bir_free_vars exp =
	let
	    open stringSyntax;
	    fun var_to_str v =
		let val (name,_) = dest_var v
		in
		    fromMLstring name
		end
	    val fvs =
	        if is_comb exp then
		    let val (con,args) = strip_comb exp
		    in
		        if identical con ``BExp_MemConst``
		        then [var_to_str (List.nth(args, 2))]
		        else if identical con ``BExp_Den``
		        then
		            let val v = case strip_comb (hd args) of
				            (_,v::_) => v
				          | _ => raise ERR "bir_free_vars" "not expected"
		            in
			        [v]
		            end
		        else
		            List.concat (map bir_free_vars args)
		    end
	        else []
	in
	    nub_with (fn (x,y) => identical x y) fvs
	end;

    fun Obs_prime xs = 
	let open stringSyntax numSyntax;
	    fun primed_subst exp =
		List.map (fn v =>
			     let val vp = lift_string string_ty (fromHOLstring v ^ "*")
			     in ``^v`` |-> ``^vp`` end)
			 (bir_free_vars exp) 
	    fun Obs_prime_single x =
		      let val obs = x |> dest_BStmt_Observe |> #3
              val (id, a, b, c) = dest_BStmt_Observe x
              val new_x = mk_BStmt_Observe (term_of_int 1, a, b, c)
		in
		    List.foldl (fn (record, tm) => subst[#redex record |-> #residue record] tm) new_x (primed_subst obs)
		end
	in
	    map Obs_prime_single xs
	end;

    fun Obs_prime_base xs = 
	      let open stringSyntax numSyntax;
	          fun primed_subst exp =
		            List.map (fn v =>
			                       let val vp = lift_string string_ty (fromHOLstring v ^ "*")
			                       in ``^v`` |-> ``^vp`` end)
			                   (bir_free_vars exp) 
	          fun Obs_prime_single proj_id x =
		            let val obs = x |> dest_BStmt_Observe |> #3
                    val (id, a, b, c) = dest_BStmt_Observe x
                    val new_x = mk_BStmt_Observe (term_of_int proj_id, a, b, c)
		            in
		              List.foldl (fn (record, tm) => subst[#redex record |-> #residue record] tm) new_x (primed_subst obs)
		            end
	      in
          case xs of
              [] => []
	          | y::ys => Obs_prime_single 0 y :: map (Obs_prime_single 1) ys
	      end

(*
  reside in bir_obs_modelScript.sml. cannot be here, otherwise this creates unfinished scratch theory
  constrain_spec_obs_vars_def
  append_list_def
*)

    fun mk_assign_mem_assert e =
	let 
	    open stringSyntax;
	    val mem_bounds =
		let
		    open wordsSyntax
		    fun bir_embexp_params_cacheable x = Arbnum.+ (Arbnum.fromInt 0x80000000, x);
		    val (mem_base, mem_len) = (Arbnum.fromHexString "0x100000", Arbnum.fromHexString  "0x40000")
		    val mem_end = (Arbnum.- (Arbnum.+ (mem_base, mem_len), Arbnum.fromInt 128));
		in
		    pairSyntax.mk_pair
			(mk_wordi (bir_embexp_params_cacheable mem_base, 64),
			 mk_wordi (bir_embexp_params_cacheable mem_end, 64))
		end;
	    fun remove_prime str =
		if String.isSuffix "*" str then
		    (String.extract(str, 0, SOME((String.size str) - 1)))
		else
		    raise ERR "remove_prime" "there was no prime where there should be one"
	    val p_fv  = bir_free_vars e;
	    val np_fv = map (fn x => (remove_prime (fromHOLstring x)) |> (fn y => lift_string string_ty y)) p_fv;
	    val p_exp = map (fn x => subst [``"template"``|-> x] ``(BVar "template" (BType_Imm Bit64))``) 
			     p_fv;
	    val np_exp= map (fn x => subst[``"template"``|-> x]``(BExp_Den (BVar "template" (BType_Imm Bit64)))``) 
			     np_fv;
	    val comb_p_np = zip p_exp np_exp;
	    val eq_assign =  map (fn (a,b) => (rhs o concl o EVAL)``constrain_spec_obs_vars (^a,^b)``) comb_p_np  

      (* gets list of observation statements
         NB. we assume e is of the form produced in add_obs_speculative_exec
       *)
	    val (obslist,_)  = (listSyntax.dest_list o #2 o pairSyntax.dest_pair) e
                         handle _ => raise ERR "mk_assign_mem_assert"
                                           ("ill-formed argument: " ^ term_to_string e ^ ", expected pair");
  in
    case obslist of
        [] => []
      | obs::_ =>
        let
          (* extract observed expression from first obs. stmt
             NB. if add_obs code is well-behaved, this should never fail at dest_cons
             because the list in a BStmt_Observe should always be nonempty
           *)
          val (obstm,_) = ((listSyntax.dest_cons o #3 o dest_BStmt_Observe) obs)
                          handle _ => raise ERR "mk_assign_mem_assert"
                                            ("ill-formed subexpression in arg: "
                                             ^ term_to_string obs ^ ", expected obs. stmt"
                                             ^ " with nonempty obs. list");
	        val memcnst  = (rhs o concl o EVAL)``(constrain_mem ^(mem_bounds) ^obstm): bir_val_t bir_stmt_basic_t``;
	      in
	        rev(memcnst::eq_assign) (* eq_assign @ [memcnst] *)
	      end
  end

    fun add_obs_speculative_exec obs_fun prog targets g depth dict = 
	let
	    open listSyntax
	    open pairSyntax
	    val Obs_dict = extract_branch_obs targets g depth dict
					      |> (fst o (fn d => Redblackmap.remove (d, ``dummy``)))
	    val Obs_dict_primed = Redblackmap.map (fn (k,v) => obs_fun v) Obs_dict;
	    val Obs_lst_primed  = map (fn tm => mk_pair(fst tm, mk_list(snd tm, ``:bir_val_t bir_stmt_basic_t``))) 
				      (Redblackmap.listItems Obs_dict_primed)
	    val asserted_obs = map (fn e => mk_list((mk_assign_mem_assert e), ``:bir_val_t bir_stmt_basic_t``)) 
				      Obs_lst_primed;
	    val zip_assertedObs_primed = zip Obs_lst_primed asserted_obs;
	    val Obs_lst = map (fn (a, b) => (rhs o concl o EVAL)``append_list ^a ^b`` ) zip_assertedObs_primed;
	in
	    foldl (fn(itm, p) => (rhs o concl o EVAL)``prepend_obs_in_bir_prog_block ^itm ^p``) 
		  prog 
		  Obs_lst
	end

 fun branch_instrumentation_obs obs_fun prog depth = 	
    let (* build the dictionaries using the library under test *)
	val bl_dict = gen_block_dict prog;
	val lbl_tms = get_block_dict_keys bl_dict;
	(* build the cfg and update the basic blocks *)
	val n_dict = cfg_build_node_dict bl_dict lbl_tms;
	    
	val entries = [mk_key_from_address64 64 (Arbnum.fromHexString "0")];
	val g1 = cfg_create "specExec" entries n_dict bl_dict;
	    
	val (visited_nodes,cjmp_nodes) = traverse_graph g1 (hd (#CFGG_entries g1)) [] [];
	val targets = map (fn i => #CFGN_targets (lookup_block_dict_value (#CFGG_node_dict g1) i "_" "_")) cjmp_nodes;
    in
	foldl (fn(ts, p) => add_obs_speculative_exec obs_fun p ts g1 depth bl_dict) prog targets
    end
in

  (* Exmaple usage: inputs are lifted program with intial observation and depth of execution      *)
  (* branch_instrumentation_obs lifted_prog_w_obs 3; *)

  structure bir_arm8_cache_speculation_model : OBS_MODEL =
    struct
      val obs_hol_type = ``bir_val_t``;
      val pipeline_depth = 3;
      fun add_obs mb t =
        branch_instrumentation_obs Obs_prime (bir_arm8_mem_addr_pc_model.add_obs mb t) pipeline_depth;
    end;

  structure bir_arm8_cache_speculation_first_model : OBS_MODEL =
  struct
  val obs_hol_type = ``bir_val_t``;
  val pipeline_depth = 3;
  fun add_obs mb t =
      branch_instrumentation_obs Obs_prime_base (bir_arm8_mem_addr_pc_model.add_obs mb t) pipeline_depth;
  end;

end (* local *)


fun get_obs_model id =
  let
    val obs_hol_type =
             if id = "mem_address_pc" then
	  bir_arm8_mem_addr_pc_model.obs_hol_type
        else if id = "cache_tag_index" then
          bir_arm8_cache_line_model.obs_hol_type
        else if id = "cache_tag_only" then
          bir_arm8_cache_line_tag_model.obs_hol_type
        else if id = "cache_index_only" then
          bir_arm8_cache_line_index_model.obs_hol_type
        else if id = "cache_tag_index_part" then
          bir_arm8_cache_line_subset_model.obs_hol_type
        else if id = "cache_tag_index_part_page" then
          bir_arm8_cache_line_subset_page_model.obs_hol_type
        else if id = "cache_speculation" then
               bir_arm8_cache_speculation_model.obs_hol_type
        else if id = "cache_speculation_first" then
               bir_arm8_cache_speculation_first_model.obs_hol_type
        else
            raise ERR "get_obs_model" ("unknown obs_model selected: " ^ id);

    val add_obs =
             if id = "mem_address_pc" then
          bir_arm8_mem_addr_pc_model.add_obs
        else if id = "cache_tag_index" then
          bir_arm8_cache_line_model.add_obs
        else if id = "cache_tag_only" then
          bir_arm8_cache_line_tag_model.add_obs
        else if id = "cache_index_only" then
          bir_arm8_cache_line_index_model.add_obs
        else if id = "cache_tag_index_part" then
          bir_arm8_cache_line_subset_model.add_obs
        else if id = "cache_tag_index_part_page" then
          bir_arm8_cache_line_subset_page_model.add_obs
        else if id = "cache_speculation" then
               bir_arm8_cache_speculation_model.add_obs
        else if id = "cache_speculation_first" then
               bir_arm8_cache_speculation_first_model.add_obs
        else
          raise ERR "get_obs_model" ("unknown obs_model selected: " ^ id);
  in
    { id = id,
      obs_hol_type = obs_hol_type,
      add_obs = add_obs }
  end;

end (* struct *)
