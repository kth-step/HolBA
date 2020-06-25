structure bir_cfgLib =
struct
local

open bir_blockCollectionLib;

in

  (* pass 1: Jump, CondJump, Halt will be determined from BIR code.
             for jumps/condjumps, fill with direct jump targets where applicable,
             otherwise empty list *)
  (* pass 2: look at Jump nodes with one direct target and update
             if they appear to be Basic (determinded from disassembly metadata) *)
  (* pass 3: check all jump blocks, which have no targets yet,
             determine Call and Return based on heuristic and static fixes (semi-automatic) *)
  (* pass 4: resolve remaining jumps/condjumps with no targets using static fixes *)
  datatype cfg_node_type =
      (* Core BIR types *)
      CFGNT_Jump
    | CFGNT_CondJump
    | CFGNT_Halt
      (* Special purpose types: used for visualization or higher level abstraction *)
    | CFGNT_Basic
    | CFGNT_Call
    | CFGNT_Return;

  (* cfg nodes correspond to BIR blocks, lbl_tm is normalized label of block and represents its id *)
  type cfg_node = {
    (* id: BIR label term of BIR block *)
    CFGN_lbl_tm   : term,
    (* meta information from disassembled and lifted binary *)
    CFGN_hc_descr : string option,
    (* flow information. statically exported from BIR blocks, or fixed semi-automatically *)
    CFGN_goto     : term list,
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

local

(* TODO: put this in the right place and cleanup elsewhere too *)
fun syntax_fns n d m = HolKernel.syntax_fns {n = n, dest = d, make = m} "bir_program_labels"

fun syntax_fns0 s = let val (tm, _, _, is_f) = syntax_fns 0
   (fn tm1 => fn e => fn tm2 =>
       if Term.same_const tm1 tm2 then () else raise e)
   (fn tm => fn () => tm) s in (tm, is_f) end;

val syntax_fns1 = syntax_fns 1 HolKernel.dest_monop HolKernel.mk_monop;
val syntax_fns2 = syntax_fns 2 HolKernel.dest_binop HolKernel.mk_binop;
val syntax_fns3 = syntax_fns 3 HolKernel.dest_triop HolKernel.mk_triop;

val (BL_Address_HC_tm,  mk_BL_Address_HC, dest_BL_Address_HC, is_BL_Address_HC)  = syntax_fns2 "BL_Address_HC";

in
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
		CFGN_goto     = cfg_t_l,
		CFGN_type     = cfgn_type
	      } : cfg_node;

    in n end;
end

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
          val targets = #CFGN_goto (n:cfg_node);

          val exclude_list = (lbl_tm::acc_ns)@acc_ex@todo;
          val new_todo = List.filter (fn x => List.all (fn y => x <> y) exclude_list) targets;

          val (acc_ns', acc_ex') =
            if targets <> [] then
              (lbl_tm::acc_ns, acc_ex)
            else
              (acc_ns, lbl_tm::acc_ex)
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


  (* pass 2 - determine basic blocks (i.e., straight to next "instruction") *)
  (* =================================== *)

  local

(* TODO: put this in the right place and cleanup elsewhere too *)
  fun list_split_pred_aux acc p [] = fail ()
    | list_split_pred_aux acc p (x::xs) =
      (if x = p then (List.rev acc, xs)
       else list_split_pred_aux (x::acc) p xs)

  fun list_split_pred p = list_split_pred_aux [] p

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

  (* cfg update functions take: bl_dict lbl_tms n_dict *)
  fun cfg_update_nodes_basic bl_dict lbl_tms n_dict =
    let
      fun update_n_dict (lbl_tm, n_dict) =
        let
          val n = case lookup_block_dict n_dict lbl_tm of
                     SOME x => x
                   | NONE => raise ERR "cfg_update_nodes_basic" ("cannot find label " ^ (term_to_string lbl_tm));

          val succ_lbl_tm_o = cfg_node_to_succ_lbl_tm n;
          val targets       = #CFGN_goto n;

          val update_this = is_some succ_lbl_tm_o andalso
                            targets = [valOf succ_lbl_tm_o];

          val n' = if not update_this then n else
              { CFGN_lbl_tm   = #CFGN_lbl_tm n,
		CFGN_hc_descr = #CFGN_hc_descr n,
		CFGN_goto     = #CFGN_goto n,
		CFGN_type     = CFGNT_Basic
	      } : cfg_node;
          val n_dict' = if not update_this then n_dict else
                        Redblackmap.update (n_dict, lbl_tm, K n');
        in
          n_dict'
        end;
    in
      List.foldr update_n_dict n_dict lbl_tms
    end;

end (* local *)
end (* struct *)
