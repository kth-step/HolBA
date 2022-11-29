structure bir_cfg_m0Lib =
struct
local

  open HolKernel Parse;

  open bir_programSyntax;
  open bir_valuesSyntax;
  open bir_immSyntax;
  open optionSyntax;
  open wordsSyntax;
  open listSyntax;

  open bir_block_collectionLib;
  open bir_cfgLib;

  val libname = "bir_cfg_m0Lib";
  val ERR = Feedback.mk_HOL_ERR libname;
  val wrap_exn = Feedback.wrap_exn libname;

  (* simple helpers *)
  val BVarLR32_tm = ``BVar "LR" (BType_Imm Bit32)``;
  fun is_Assign_LR tm =
    if is_BStmt_Assign tm then
      identical ((fst o dest_BStmt_Assign) tm) BVarLR32_tm
    else
      false;

  fun mk_lbl_tm addr =
    (mk_BL_Address o mk_Imm32 o mk_word) (addr, Arbnum.fromInt 32);

  fun dest_lbl_tm lbl_tm =
    (dest_word_literal o dest_Imm32 o dest_BL_Address) lbl_tm

in (* local *)

  (* continuation of bir_cfgLib passes: *)
  (* pass 3: check all jump blocks, which have no targets yet,
             determine Calls based on heuristic and static fixes (semi-automatic) *)
  (* pass 4: resolve indirect jumps (jumps with not yet resolved targets) using static fixes *)
  (* pass 5: check all remaining jump blocks without targets,
             try to determine Returns based on heuristic and static fixes (semi-automatic) *)

  (*
  val lbl_tm = mk_key_from_address 32 (Arbnum.fromHexString "c10");

  val lbl_tm = ``BL_Address (Imm32 1198w)``;

  val bl_dict = bl_dict_;
  val n      = valOf (lookup_block_dict n_dict_1 lbl_tm);
  val bl     = valOf (lookup_block_dict bl_dict_ lbl_tm);
  *)
  fun update_node_guess_type_call bl_dict fun_entry_lbl_tms (n:cfg_node) =
    if not (cfg_node_type_eq (#CFGN_type n, CFGNT_Jump)) orelse
       List.null (#CFGN_targets n) then NONE else
    (* take jumps with direct target to filter out the calls *)
    let
      val debug_on = false;

      val lbl_tm = #CFGN_lbl_tm n;
      val targets = #CFGN_targets n;

      val _ = if not debug_on then () else
	      print ((term_to_string lbl_tm) ^ "\n");

      val bl =
		    case lookup_block_dict bl_dict lbl_tm of
		       SOME x => x
		     | NONE => raise ERR "update_node_guess_type_call"
					 ("cannot find label " ^ (term_to_string lbl_tm));

      val (_, bbs, _) = dest_bir_block bl;

      val _ = if length targets = 1 then () else
	      raise ERR "update_node_guess_type_call"
			"there should be exactly 1 direct jump target"
      val goto_tm = hd targets;

      val isCall_lr       =  List.exists is_Assign_LR ((fst o dest_list) bbs);
      val isCall_to_entry = (List.exists (fn x => identical x goto_tm) fun_entry_lbl_tms);

      val _ = if isCall_lr = isCall_to_entry then ()
	      else raise ERR "update_node_guess_type_call"
			     ("something in call detection is unexpected: " ^ (term_to_string lbl_tm));
      val isCall = isCall_lr;

      val _ = if not (debug_on andalso isCall) then () else
	      (print "call        ::: "; print (Option.getOpt(#CFGN_hc_descr n, "NONE")); print "\t"; print_term lbl_tm);

      val call_cont_o = cfg_node_to_succ_lbl_tm n;
      val _ = if isSome call_cont_o then () else
	      raise ERR "update_node_guess_type_call"
			"cannot determine continuation block for call";

      val call_conts_guess = [valOf call_cont_o];

      val new_type = if isCall then CFGNT_Call call_conts_guess else #CFGN_type n;

      val new_n =
	      { CFGN_lbl_tm   = #CFGN_lbl_tm n,
		CFGN_hc_descr = #CFGN_hc_descr n,
		CFGN_targets  = #CFGN_targets n,
		CFGN_type     = new_type
	      } : cfg_node;
    in
      SOME new_n
    end;


  fun update_node_manual_indir_jump resolv_map (n:cfg_node) =
    if not (cfg_node_type_eq (#CFGN_type n, CFGNT_Jump)) orelse
       not (List.null (#CFGN_targets n)) then NONE else
    (* take jumps with no resolved direct targets to filter out the returns *)
    let
      val debug_on = false;

      val lbl_tm = #CFGN_lbl_tm n;
      val descr_o = #CFGN_hc_descr n;

      val descr = case descr_o of
		     SOME x => x
		   | NONE => raise ERR "update_node_manual_indir_jump"
				       ("need node description text from lifter: " ^ (term_to_string lbl_tm));

      val hack_map = resolv_map;

      val hackMatch = List.find (fn (loc_, descr_, _, _) =>
				   descr = descr_ andalso
				   dest_lbl_tm lbl_tm = Arbnum.fromInt loc_
				) hack_map;
      val isIndirJump = isSome hackMatch;
      (*
      val tl = ((fn (_, _, nt, tl) => tl) o hd) hack_map;
      val s = hd tl;
  rev_hs_to_num (Arbnum.fromInt 0) s
  Arbnum.toHexString (rev_hs_to_num (Arbnum.fromInt 0) s)
      *)
      val indirJumpUpdate = Option.map (fn (_, _, nt, tl) =>
	  let
	    val tl_unique = List.foldr (fn (x,l) => if List.exists (fn y => x=y) l then l else (x::l)) [] tl;
(*
	    fun split_string_byte s =
	      let
		val _ = if (String.size s) mod 2 = 0 then () else
			  raise ERR "split_string_byte" "bug: string length is wrong";
		val len = (String.size s) div 2;
	      in
		(Arbnum.fromHexString (String.substring(s, (len*2) - 2, 2)),
				       String.substring(s, 0, (len*2) - 2))
	      end;
	    fun rev_hs_to_num acc "" = acc
	      | rev_hs_to_num acc s  =
		  let
		    val sp = split_string_byte s;
		    val n  = Arbnum.+(Arbnum.*(acc, Arbnum.fromInt 256), fst sp);
		  in
		    rev_hs_to_num n (snd sp)
		  end;
*)
	  in
(*
	    (nt, List.map (rev_hs_to_num (Arbnum.fromInt 0)) tl_unique)
*)
	    (nt, List.map (Arbnum.fromHexString) tl_unique)
	  end
	) hackMatch;
  (*
      val isIndirJump = String.isSubstring "(mov pc," descr;
  *)
      val _ = if not (debug_on andalso isIndirJump) then () else
	      (print "indirect J  ::: "; print descr; print "\t"; print_term lbl_tm);

      val new_type = if isIndirJump then ((fst o valOf) indirJumpUpdate) else #CFGN_type n;

      val new_targets =
	    if isIndirJump then
	      (((List.map (mk_lbl_tm)) o snd o valOf) indirJumpUpdate)
	    else
	      #CFGN_targets n;

      val new_n =
	      { CFGN_lbl_tm   = #CFGN_lbl_tm n,
		CFGN_hc_descr = #CFGN_hc_descr n,
		CFGN_targets  = new_targets,
		CFGN_type     = new_type
	      } : cfg_node;
    in
      SOME new_n
    end;


  (*
  length ns

  val ns = List.map (update_node_guess_type_call o to_cfg_node) prog_lbl_tms_;
  val lbl_tm = mk_lbl_tm (Arbnum.fromInt 7936);
  val n  = find_node ns lbl_tm;
  val _ = List.map (update_node_guess_type_return o update_node_guess_type_call o to_cfg_node) prog_lbl_tms_;
  *)
  fun update_node_guess_type_return (n:cfg_node) =
    if not (cfg_node_type_eq (#CFGN_type n, CFGNT_Jump)) orelse
       not (List.null (#CFGN_targets n)) then NONE else
    (* take jumps with no resolved direct targets to filter out the returns *)
    let
      val debug_on = false;

      val lbl_tm = #CFGN_lbl_tm n;
      val descr_o = #CFGN_hc_descr n;

      val descr = case descr_o of
		     SOME x => x
		   | NONE => raise ERR "update_node_guess_type_return"
				       ("need node description text from lifter: " ^ (term_to_string lbl_tm));

      val isReturn = ((String.isSubstring "pop {" descr) andalso
		      (String.isSubstring "pc}" descr))
		     orelse
		     (String.isSubstring "(bx lr)" descr);

      (* hack for hand inspected instructions *)
      val isReturn = isReturn orelse (
		     (identical lbl_tm (mk_lbl_tm (Arbnum.fromInt 0x1fc))) andalso
		     (String.isPrefix "4718 (" descr)
	  );

      val _ = if not (debug_on andalso isReturn) then () else
	      (print "return      ::: "; print descr; print "\t"; print_term lbl_tm);

      (* still unclear type... *)
      val _ = if (isReturn) (* orelse (not debug_on) *) then ()
	      else print ("update_node_guess_type_return :: " ^
			     "cannot determine type: " ^ descr ^
			      "\t" ^ (term_to_string lbl_tm) ^ "\n");

      val new_type = CFGNT_Return;

      val new_n =
	      { CFGN_lbl_tm   = #CFGN_lbl_tm n,
		CFGN_hc_descr = #CFGN_hc_descr n,
		CFGN_targets  = #CFGN_targets n,
		CFGN_type     = new_type
	      } : cfg_node;
    in
      SOME new_n
    end;

  (*
  =================================================================================================
  *)

  fun collect_node_callinfo find_rel_symbol_from_lbl_tm (n:cfg_node) =
    let
      val rel_name  = (valOf o find_rel_symbol_from_lbl_tm o #CFGN_lbl_tm) n;
      val n_type    = #CFGN_type n;
      val n_targets = #CFGN_targets n;
    in
      if not (cfg_nodetype_is_call n_type) then NONE else SOME (
       rel_name,
       List.map (valOf o find_rel_symbol_from_lbl_tm) n_targets,
       let
	 val call_conts = case n_type of
			     CFGNT_Call cs => cs
			   | _ => raise ERR "collect_node_callinfo" "this would never happen";
	 val _ = if length call_conts = 1 then () else
		 raise ERR "collect_node_callinfo" "expecting exactly one call continuation target";
       in
	 hd call_conts
       end
      )
    end;


  fun lookup_calls_to ci to = List.foldr (fn ((_, tol, returnto), l) =>
      if List.exists (fn x => x = to) tol then
	(returnto)::l
      else
	l
    ) [] ci;

  fun update_node_fix_return_goto find_rel_symbol_from_lbl_tm lookup_calls_to_f (n:cfg_node) =
    if not (cfg_node_type_eq (#CFGN_type n, CFGNT_Return)) then NONE else
    let
      val debug_on = false;

      val rel_name = (valOf o find_rel_symbol_from_lbl_tm o #CFGN_lbl_tm) n;

      val new_targets = (lookup_calls_to_f) rel_name;

      val new_n =
	      { CFGN_lbl_tm   = #CFGN_lbl_tm n,
		CFGN_hc_descr = #CFGN_hc_descr n,
		CFGN_targets  = new_targets,
		CFGN_type     = #CFGN_type n
	      } : cfg_node;
    in
      SOME new_n
    end;

end (* local *)
end (* struct *)
