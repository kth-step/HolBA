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

    (* given a branch, extract the statements of that branch as a list *)
    fun extract_branch_stmts g depth branch bl_dict =
        let
          open listSyntax
          val dest_list_ignore_type = fst o dest_list;
          fun extract_stmts_from_lbl lbl =
              let open bir_programSyntax;
                  val block = Redblackmap.find (bl_dict, lbl)
                  val (_, statements, _) = dest_bir_block block;
                  (* statements is a HOL list of BIR statements *)
              in statements end;

          val (branch_labels,_) = traverse_graph_branch g depth branch [] [];
          (* stmts is a (SML) list of BIR statements (HOL terms) *)
          val stmts = List.map (dest_list_ignore_type o extract_stmts_from_lbl) (rev branch_labels);
        in
          List.concat stmts
        end;

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

    fun bir_free_vars_stmt_b stmt_b =
	      let
	        open stringSyntax;
          open bir_envSyntax;
          open bir_programSyntax;
          val fvs =
		          if is_BStmt_Assign stmt_b
              then
                let val (var,exp) = dest_BStmt_Assign stmt_b
		            in
                  (fst (dest_BVar var))::(bir_free_vars exp)
                end
              else
                bir_free_vars stmt_b;
        in
          nub_with (fn (x,y) => identical x y) fvs
        end;

    fun primed_term t =
	      let open stringSyntax numSyntax;
	          fun primed_subst tm =
		            List.map (fn v =>
			                       let val vp = lift_string string_ty (fromHOLstring v ^ "*")
			                       in ``^v`` |-> ``^vp`` end)
			                   (bir_free_vars_stmt_b tm)
        in
          List.foldl (fn (record, tm) => subst[#redex record |-> #residue record] tm) t (primed_subst t)
        end

    fun const_obs t =
        if is_BStmt_Observe t
        then let open listSyntax;
                 val (_,_,obs_list_tm,_) = dest_BStmt_Observe t;
                 val (obs_list,_) = dest_list obs_list_tm;
             in
               length obs_list = 1 andalso is_BExp_Const (hd obs_list)
             end
        else false

    fun mk_preamble stmts =
        let open stringSyntax;
            val free_vars = nub_with (uncurry identical)
                                     (List.concat (map bir_free_vars_stmt_b stmts));
            fun star_string str =
                  lift_string string_ty (fromHOLstring str ^ "*")
            fun mk_assignment var =
                let val var_type =
                        if fromHOLstring var = "MEM"
                        then “BType_Mem Bit64 Bit8”
                        else “BType_Imm Bit64”
                    val var_star_tm = “BVar ^(star_string var) ^var_type”
                in inst [Type.alpha |-> Type`:bir_val_t`]
                        (mk_BStmt_Assign (var_star_tm, “BExp_Den (BVar ^var ^var_type)”))
                end;
        in
          List.map mk_assignment free_vars
        end;

    (* generate shadow branch for a given branch (to be inserted in the other) *)
    fun gen_shadow_branch obs_fun g depth dict branch =
        let
          open listSyntax
          open pairSyntax
          val stmts = extract_branch_stmts g depth branch dict;
          val preamble = mk_preamble stmts;
          (* add stars to every free variable *)
          val stmts_starred = map primed_term stmts;
          (* remove constant observations (pc observations) *)
          val stmts_without_pc = filter (not o const_obs) stmts_starred;
          (* tag observations as refinements, as per obs_fun
             NB. Refinement will not work unless obs_fun tags
                 some observations with 1 *)
          val stmts_obs_tagged = obs_fun stmts_without_pc
        in
          preamble @ stmts_obs_tagged
        end

    (* generate shadow branches for a given cjmp *)
    fun add_shadow_branches obs_fun g depth dict (left_branch, right_branch) prog =
	let
	    open listSyntax
	    open pairSyntax
      fun to_stmt_list xs = mk_list(xs, “:bir_val_t bir_stmt_basic_t”);
      val gen_shadow = gen_shadow_branch obs_fun g depth dict;
      val left_shadow =  to_stmt_list (gen_shadow left_branch)
      val right_shadow = to_stmt_list (gen_shadow right_branch);
      fun prepend_block (itm, p) =
          (rhs o concl o EVAL)``prepend_obs_in_bir_prog_block ^itm ^p``
	in
	    foldl prepend_block prog
		  [“(^left_branch, ^right_shadow)”, “(^right_branch, ^left_shadow)”]
	end

    fun obs_refined n stm =
        if is_BStmt_Observe stm
        then let open numSyntax;
                 val (obs_id,cond,obs_list_tm,f) = dest_BStmt_Observe stm;
             in
               mk_BStmt_Observe (term_of_int n, cond, obs_list_tm, f)
             end
        else stm

    val obs_all_refined = List.map (obs_refined 1);
    fun obs_all_refined_but_first stmts =
        let fun go [] = []
              | go (stmt::stmts) =
                if is_BStmt_Observe stmt
                then obs_refined 0 stmt :: obs_all_refined stmts
                else stmt :: go stmts
        in
          go stmts
        end

 fun branch_instrumentation obs_fun prog depth = 	
    let (* build the dictionaries using the library under test *)
	val bl_dict = gen_block_dict prog;
	val lbl_tms = get_block_dict_keys bl_dict;
	(* build the cfg and update the basic blocks *)
	val n_dict = cfg_build_node_dict bl_dict lbl_tms;
	    
	val entries = [mk_key_from_address64 64 (Arbnum.fromHexString "0")];
	val g1 = cfg_create "specExec" entries n_dict bl_dict;
	    
	val (visited_nodes,cjmp_nodes) = traverse_graph g1 (hd (#CFGG_entries g1)) [] [];
  (* targets: each element in this list is a two-element list of branch targets
     there is one such element for each cjmp in the program *)
	val targets = map (fn i => #CFGN_targets (lookup_block_dict_value (#CFGG_node_dict g1) i "_" "_")) cjmp_nodes;
  fun unpack_targets ts =
      case ts of
          left::right::_ => (left,right)
        | _ => raise ERR "branch_instrumentation" "CJMP node without two targets"
    in
	    foldl (fn (ts, p) =>
                add_shadow_branches obs_fun g1 depth bl_dict (unpack_targets ts) p)
            prog
            targets
    end
in

  (* Exmaple usage: inputs are lifted program with intial observation and depth of execution      *)
  (* branch_instrumentation_obs lifted_prog_w_obs 3; *)

  structure bir_arm8_cache_speculation_model : OBS_MODEL =
    struct
      val obs_hol_type = ``bir_val_t``;
      val pipeline_depth = 3;
      fun add_obs mb t =
        branch_instrumentation obs_all_refined (bir_arm8_mem_addr_pc_model.add_obs mb t) pipeline_depth;
    end;

  structure bir_arm8_cache_speculation_first_model : OBS_MODEL =
  struct
  val obs_hol_type = ``bir_val_t``;
  val pipeline_depth = 3;
  fun add_obs mb t =
      branch_instrumentation obs_all_refined_but_first (bir_arm8_mem_addr_pc_model.add_obs mb t) pipeline_depth;
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
