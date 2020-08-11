structure bir_obs_modelLib :> bir_obs_modelLib =
struct

local
    open bir_obs_modelTheory;
in

structure bir_pc_model : OBS_MODEL =
struct
val obs_hol_type = ``bir_val_t``;
fun add_obs t = rand (concl (EVAL ``add_obs_pc ^t``));
end

structure bir_arm8_mem_addr_pc_model : OBS_MODEL =
struct
val obs_hol_type = ``bir_val_t``;
fun add_obs t = rand (concl (EVAL ``add_obs_mem_addr_pc_armv8 ^t``));
end

structure bir_arm8_cache_line_model : OBS_MODEL =
struct
val obs_hol_type = ``bir_val_t``;
fun add_obs t = rand (concl (EVAL ``add_obs_cache_line_armv8 ^t``));
end

structure bir_arm8_cache_line_tag_model : OBS_MODEL =
struct
val obs_hol_type = ``bir_val_t``;
fun add_obs t = rand (concl (EVAL ``add_obs_cache_line_tag_armv8 ^t``));
end

structure bir_arm8_cache_line_index_model : OBS_MODEL =
struct
val obs_hol_type = ``bir_val_t``;
fun add_obs t = rand (concl (EVAL ``add_obs_cache_line_index_armv8 ^t``));
end

structure bir_arm8_cache_line_subset_model : OBS_MODEL =
struct
val obs_hol_type = ``bir_val_t``;
fun add_obs t = rand (concl (EVAL ``add_obs_cache_line_subset_armv8 ^t``));
end

structure bir_arm8_cache_line_subset_page_model : OBS_MODEL =
struct
val obs_hol_type = ``bir_val_t``;
fun add_obs t = rand (concl (EVAL ``add_obs_cache_line_subset_page_armv8 ^t``));
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
		
	    val acc_new = (if n_type = CFGNT_CondJump then [entry] else [])@acc;
	    val targets_to_visit = List.filter (fn x => List.all (fn y => x <> y) visited) targets;
	    
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
		if (n_type = CFGNT_CondJump) orelse (depth = 0) 
		then ([], (if n_type = CFGNT_CondJump then [entry] else [])@acc)
		else (List.filter (fn x => List.all (fn y => x <> y) visited) targets,
		      (if n_type = CFGNT_CondJump then [entry] else [])@acc)
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
	    val b1_nodes = List.filter (fn x => (List.all (fn y => x <> y) bn1)) bn2;
	    val b2_nodes = List.filter (fn x => (List.all (fn y => x <> y) bn2)) bn1;
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
			if con = ``BExp_MemConst``
			then [``"MEM"``]
			else if con = ``BExp_Den``
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
	let open stringSyntax;
	    fun primed_subst exp =
		List.map (fn v =>
			     let val vp = lift_string string_ty (fromHOLstring v ^ "*")
			     in ``^v`` |-> ``^vp`` end)
			 (bir_free_vars exp) 
	    fun Obs_prime_single x =
		let val obs = x |> dest_BStmt_Observe |> #3 
		in
		   List.foldl (fn (record, tm) => subst[#redex record |-> #residue record] tm) x (primed_subst obs)
		end
	in
	    map Obs_prime_single xs
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
	in
	    foldl (fn(itm, p) => (rhs o concl o EVAL)``add_obs_speculative_exec_armv8 ^p ^itm``) 
		  prog 
		  Obs_lst_primed
	end

in
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

(* Exmaple usage: inputs are lifted program with intial observation and depth of execution      *)
(* branch_instrumentation_obs lifted_prog_w_obs 3; *)

structure bir_arm8_cache_speculation_model : OBS_MODEL =
 struct
 val obs_hol_type = ``bir_val_t``;
 val pipeline_depth = 3;
 fun add_obs t =
     branch_instrumentation_obs (bir_arm8_cache_line_model.add_obs t) pipeline_depth;
 end;


fun get_obs_model id =
  let
    val obs_hol_type =
	      if id = "mem_address_pc_trace" then
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
	      if id = "mem_address_pc_trace" then
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

end
end (* local *)
