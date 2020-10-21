structure bir_obs_modelLib :> bir_obs_modelLib =
struct

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
    open bir_block_collectionLib;
    open bir_cfgLib;

    val Obs_dict =  Redblackmap.insert (Redblackmap.mkDict Term.compare, ``dummy``, ([]:term list));
    fun mk_key_from_address64 i addr = (mk_BL_Address o bir_immSyntax.mk_Imm64 o wordsSyntax.mk_word) (addr, Arbnum.fromInt i);

    (* traversal example, single entry recursion, stop at first revisit or exit *)
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

    fun extract_branch_obs targets g depth bl_dict =
	let  
	    val f =  (fn l => Redblackmap.find (bl_dict, l)|> bir_programSyntax.dest_bir_block|> not o listSyntax.is_nil o #2)
	    fun extratc_obs labels = 
		List.map (fn label => 
			     let val block = Redblackmap.find (bl_dict, label)
				 val (_, statements, _) = bir_programSyntax.dest_bir_block block
			     in
				 find_term is_BStmt_Observe statements
			     end) (filter f labels)

	    val bn1::bn2::_ = List.map (fn t => fst (traverse_graph_branch g depth (t) [] [])) targets;
	    val b1_nodes = List.filter (fn x => (List.all (fn y => not (identical x y)) bn1)) bn2;
	    val b2_nodes = List.filter (fn x => (List.all (fn y => not (identical x y)) bn2)) bn1;
	    val Obs_dict = Redblackmap.insert(Obs_dict, hd targets (* hd b2_nodes *), extratc_obs b1_nodes);
	    val Obs_dict = Redblackmap.insert(Obs_dict, last targets (* hd b1_nodes *), extratc_obs b2_nodes);
	in
	    Obs_dict
	end

    fun bir_free_vars exp =
	let 
	    val fvs =
		if is_comb exp then
		    let val (con,args) = strip_comb exp
		    in
			if identical con ``BExp_MemConst``
			then [``"MEM"``]
			else if identical con ``BExp_Den``
			then
			    let val v = case strip_comb (hd args) of
					    (_,v::_) => v
					  | _ => raise ERR "bir_free_vars" "not expected"
			    in
				[v]
			    end
			else
			    List.concat (List.map bir_free_vars args)
		    end
		else []
	in
	    fvs
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
	end

    val constrain_spec_obs_vars_def = Define`
        constrain_spec_obs_vars (e1, e2) =
        BStmt_Assign  (e1) (e2) :bir_val_t bir_stmt_basic_t
        `;

    val append_list_def = Define`
        append_list (lbl, (l1:  bir_val_t bir_stmt_basic_t list)) l2 =
        let combLst = APPEND l2 l1 in (lbl, combLst)
        `;

    fun mk_eq_assert e =
	let 
	    open stringSyntax;
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
	in
	    map (fn (a,b) => (rhs o concl o EVAL)``constrain_spec_obs_vars (^a,^b)``) comb_p_np  
	end

    fun add_obs_speculative_exec prog targets g depth dict = 
	let
	    open listSyntax
	    open pairSyntax
	    val Obs_dict = extract_branch_obs targets g depth dict
					      |> (fst o (fn d => Redblackmap.remove (d, ``dummy``)))
	    val Obs_dict_primed = Redblackmap.map (fn (k,v) => Obs_prime v) Obs_dict;
	    val Obs_lst_primed  = map (fn tm => mk_pair(fst tm, mk_list(snd tm, ``:bir_val_t bir_stmt_basic_t``))) 
				      (Redblackmap.listItems Obs_dict_primed)
	    val asserted_obs = map (fn e => mk_list((mk_eq_assert e), ``:bir_val_t bir_stmt_basic_t``)) 
				      Obs_lst_primed;
	    val zip_assertedObs_primed = zip Obs_lst_primed asserted_obs;
	    val Obs_lst = map (fn (a, b) => (rhs o concl o EVAL)``append_list ^a ^b`` ) zip_assertedObs_primed;
	in
	    foldl (fn(itm, p) => (rhs o concl o EVAL)``prepend_obs_in_bir_prog_block ^itm ^p``) 
		  prog 
		  Obs_lst
	end

 fun branch_instrumentation_obs prog depth = 	
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
	foldl (fn(ts, p) => add_obs_speculative_exec p ts g1 depth bl_dict) prog targets
    end
in

  (* Exmaple usage: inputs are lifted program with intial observation and depth of execution      *)
  (* branch_instrumentation_obs lifted_prog_w_obs 3; *)

  structure bir_arm8_cache_speculation_model : OBS_MODEL =
    struct
      val obs_hol_type = ``bir_val_t``;
      val pipeline_depth = 3;
      fun add_obs mb t =
        (* TODO: we don't want to augment with the pc here, or am I wrong?
                 this could be the reason for unsatisfiable... *)
        branch_instrumentation_obs (bir_arm8_mem_addr_model.add_obs mb t) pipeline_depth;
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
        else
          raise ERR "get_obs_model" ("unknown obs_model selected: " ^ id);
  in
    { id = id,
      obs_hol_type = obs_hol_type,
      add_obs = add_obs }
  end;

end (* struct *)
