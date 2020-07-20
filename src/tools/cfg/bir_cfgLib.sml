structure bir_cfgLib =
struct
local

open bir_program_labelsSyntax;
open bir_block_collectionLib;

in

  (* pass 1: Jump, CondJump, Halt will be determined from BIR code.
             for jumps/condjumps, fill with direct jump targets where applicable,
             otherwise empty list *)
  (* pass 2: look at Jump nodes with one direct target and update
             if they appear to be Basic (determinded from disassembly metadata) *)
  datatype cfg_node_type =
      (* Core BIR types *)
      CFGNT_Jump
    | CFGNT_CondJump
    | CFGNT_Halt
      (* Special purpose types: used for visualization or higher level abstraction *)
    | CFGNT_Basic
    | CFGNT_Call of (term list) (* direct labels for continuation after the call,
                                   used for resolution of return targets *)
    | CFGNT_Return;

  fun cfg_node_type_eq (CFGNT_Jump,
                        CFGNT_Jump)     = true
    | cfg_node_type_eq (CFGNT_CondJump,
                        CFGNT_CondJump) = true
    | cfg_node_type_eq (CFGNT_Halt,
                        CFGNT_Halt)     = true
    | cfg_node_type_eq (CFGNT_Basic,
                        CFGNT_Basic)    = true
    | cfg_node_type_eq (CFGNT_Call c1,
                        CFGNT_Call c2)  = Portable.list_eq identical c1 c2
    | cfg_node_type_eq (CFGNT_Return,
                        CFGNT_Return)   = true
    | cfg_node_type_eq (_,
                        _)              = false;

  (* cfg nodes correspond to BIR blocks, lbl_tm is normalized label of block and represents its id *)
  type cfg_node = {
    (* id: BIR label term of BIR block *)
    CFGN_lbl_tm   : term,
    (* meta information from disassembled and lifted binary *)
    CFGN_hc_descr : string option,
    (* flow information. statically exported from BIR blocks, or fixed semi-automatically *)
    CFGN_targets  : term list,
    (* type is initialized from BIR blocks, but may be updated by later passes *)
    CFGN_type     : cfg_node_type
  };

  (* a graph structure as list of relevant nodes with entry points *)
  type cfg_graph = {
    CFGG_name       : string,
    (* node key lists *)
    CFGG_entries    : term list,
    CFGG_exits      : term list,
    CFGG_nodes      : term list,
    (* block data *)
    CFGG_node_dict  : (term, cfg_node) Redblackmap.dict,
    CFGG_block_dict : (term, term)     Redblackmap.dict
  };

  fun cfg_nodetype_is_call nt =
    case nt of
       CFGNT_Call _ => true
     | _            => false;


  (* pass 1 - extract all directly available information from the blocks *)
  (* =================================== *)
  fun cfg_BLEs_to_targets bles =
    let
      fun BLE_to_target ble =
        if is_BLE_Label ble then
          (true, dest_BLE_Label ble)
        else
          (* it's possibile to handle other simple cases here *)
          (false, ble)

      val target_list = List.map BLE_to_target bles;

      val is_all_direct = List.all fst target_list;
      val targets = List.map snd target_list;
    in
      if is_all_direct then targets else []
    end;

  fun cfg_block_to_node bl =
    let
      val (lbl, _, bbes) = dest_bir_block bl;

      val lbl_tm = (snd o dest_eq o concl o EVAL) lbl;

      val descr = if not (is_BL_Address_HC lbl) then
                    NONE
                  else
                    SOME ((stringSyntax.fromHOLstring o snd o dest_BL_Address_HC) lbl);

      val (cfgn_type, cfg_t_l) =
          if is_BStmt_Jmp bbes then
            (CFGNT_Jump,
             cfg_BLEs_to_targets [dest_BStmt_Jmp bbes])
          else if is_BStmt_CJmp bbes then
            (CFGNT_CondJump,
             cfg_BLEs_to_targets ((fn (_, a, b) => [a, b]) (dest_BStmt_CJmp bbes)))
          else if is_BStmt_Halt bbes then
            (CFGNT_Halt, [])
          else
            raise ERR "cfg_block_to_node"
                      ("unknown BStmt end stmt type: " ^
                       (term_to_string bbes))

      val n = { CFGN_lbl_tm   = lbl_tm,
		CFGN_hc_descr = descr,
		CFGN_targets  = cfg_t_l,
		CFGN_type     = cfgn_type
	      } : cfg_node;

    in n end;

  fun cfg_build_node_dict bl_dict lbl_tms =
    let
      fun lbl_to_lblnode lbl_tm =
        (lbl_tm, cfg_block_to_node (
                   case lookup_block_dict bl_dict lbl_tm of
                      SOME x => x
                    | NONE => raise ERR "cfg_build_node_dict" ("cannot find label " ^ (term_to_string lbl_tm))));
      val lbl_node_list = List.map lbl_to_lblnode lbl_tms;
    in
      Redblackmap.insertList (Redblackmap.mkDict Term.compare, lbl_node_list)
    end;


  (* build a cfg *)
  (* =================================== *)
  fun cfg_collect_nodes n_dict [] acc_ns acc_ex = (acc_ns, acc_ex)
    | cfg_collect_nodes n_dict ((lbl_tm)::todo) acc_ns acc_ex =
        let
          val n = case lookup_block_dict n_dict lbl_tm of
                     SOME x => x
                   | NONE => raise ERR "cfg_collect_nodes" ("cannot find label " ^ (term_to_string lbl_tm));
          val targets = #CFGN_targets (n:cfg_node);

          val exclude_list = (lbl_tm::acc_ns)@acc_ex@todo;
          val new_todo = List.filter (fn x => List.all (fn y => not (identical x y)) exclude_list) targets;

          val (acc_ns', acc_ex') =
            if not (List.null targets) then
              (lbl_tm::acc_ns, acc_ex)
            else
              (lbl_tm::acc_ns, lbl_tm::acc_ex)
        in
          cfg_collect_nodes n_dict (new_todo@todo) (acc_ns') (acc_ex')
        end;

  fun cfg_create name entries n_dict bl_dict =
    let
      val (nodes,exits) = cfg_collect_nodes n_dict entries [] [];

      val g = { CFGG_name       = name,
		CFGG_entries    = entries,
		CFGG_exits      = exits,
		CFGG_nodes      = nodes,
		CFGG_node_dict  = n_dict,
		CFGG_block_dict = bl_dict
	      } : cfg_graph;
    in g end;

  fun cfg_update (g:cfg_graph) n_dict =
    let
      val name    = #CFGG_name g;
      val entries = #CFGG_entries g;
      val bl_dict = #CFGG_block_dict g;
    in
      cfg_create name entries n_dict bl_dict
    end;

  (* subsequent passes - with generic update function *)
  (* =================================== *)
  fun cfg_update_nodes_gen err_src_str update_fun lbl_tms_in n_dict_in =
      let
	fun update_n_dict (lbl_tm, n_dict) =
	  let
	    val n:cfg_node =
		    case lookup_block_dict n_dict lbl_tm of
		       SOME x => x
		     | NONE => raise ERR ("cfg_update_nodes_gen::" ^ err_src_str)
                                         ("cannot find label " ^ (term_to_string lbl_tm));

	    val n_o = update_fun n;
	    val n_dict' = if isSome n_o then
				Redblackmap.update (n_dict, lbl_tm, K (valOf n_o))
			      else
				n_dict;
	  in
	    n_dict'
	  end;
      in
	List.foldr update_n_dict n_dict_in lbl_tms_in
      end;


  (* pass 2 - determine basic blocks (i.e., straight to next "instruction") *)
  (* =================================== *)

  local

    open bir_auxiliaryLib;
    open bir_immSyntax;
    open wordsSyntax;

  in

    fun cfg_node_to_succ_lbl_tm (n:cfg_node) =
      let
	val lbl_tm   = #CFGN_lbl_tm n;
	val descr_o  = #CFGN_hc_descr n;
      in
      if (not (is_BL_Address lbl_tm)) orelse
	 (is_none descr_o)
      then NONE else
       let
	val descr = valOf descr_o;
	val (i, addr_w_tm) = (gen_dest_Imm o dest_BL_Address) lbl_tm;
	val addr = dest_word_literal addr_w_tm;

	val instrLen2 = (length o fst o (list_split_pred #" ") o explode) descr;
	val _ = if instrLen2 mod 2 = 0 then () else
		raise ERR "cfg_node_to_succ_lbl_tm"
			  ("something went wrong when trying to find the binary " ^
			   "instruction addr: " ^ (term_to_string lbl_tm) ^
			   ", descr: " ^ descr);
	val instrLen = instrLen2 div 2;
	val _ = if instrLen = 2 orelse instrLen = 4 then () else
		raise ERR "cfg_node_to_succ_lbl_tm"
			  ("something went wrong when trying to find the binary " ^
			   "instruction addr: " ^ (term_to_string lbl_tm) ^
			   ", wrong instruction length, descr: " ^ descr);

	val addr_succ = Arbnum.+ (addr, Arbnum.fromInt instrLen);
	val succ_lbl_tm = mk_key_from_address i addr_succ;
       in
	SOME succ_lbl_tm
       end
      end;

  end

  fun cfg_update_node_basic (n:cfg_node) =
    let
      val succ_lbl_tm_o = cfg_node_to_succ_lbl_tm n;
      val targets       = #CFGN_targets n;

      val update_this = is_some succ_lbl_tm_o andalso
			list_eq identical targets [valOf succ_lbl_tm_o];

      val n' =
	  { CFGN_lbl_tm   = #CFGN_lbl_tm n,
	    CFGN_hc_descr = #CFGN_hc_descr n,
	    CFGN_targets  = #CFGN_targets n,
	    CFGN_type     = CFGNT_Basic
	  } : cfg_node;
    in
      if update_this then SOME n' else NONE
    end


  fun cfg_update_nodes_basic lbl_tms n_dict_in =
      cfg_update_nodes_gen "cfg_update_node_basic"
                           cfg_update_node_basic
                           lbl_tms n_dict_in;

end (* local *)
end (* struct *)
