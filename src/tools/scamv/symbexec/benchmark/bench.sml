
open HolKernel Parse boolLib bossLib;

open bir_inst_liftingLib;
open bir_inst_liftingLibTypes;
open bir_inst_liftingHelpersLib;
open gcc_supportLib;
open PPBackEnd Parse;

open bir_programSyntax;

open bir_miscLib;


(*
=============================================================================
*)


fun run_naive_hol4_symbexec prog_ =
  let
    open listSyntax;
    open bir_symb_masterLib;

    val timer = timer_start 1;

    val numblocks = (length o fst o dest_list o dest_BirProgram) prog_;
    val maxdepth = 5 * numblocks (* (~1); *);
    val precond = ``bir_exp_true``;
    val leaves = symb_exec_process_to_leafs_nosmt maxdepth precond prog_;

    val timestrref = ref "";
    val _ = timer_stop (fn timestr => (timestrref := timestr; print ("naive hol4 symbolic execution took " ^ timestr ^ "\n"))) timer;

    val _ = print ("Number of blocks: " ^ (Int.toString numblocks) ^ "\n");
  in
    (leaves, !timestrref)
  end;


fun run_naive_hol4_symbexec2 prog_ =
    let
	open listSyntax;
	open bir_symb_execLib;
	     
	val (leafs, _) = run_naive_hol4_symbexec prog_;
	val numobss = List.foldr (op+) 0 (List.map (fn s => 
	  let
	    val (_,_,_,_,obs) = dest_bir_symb_state s;
          in (length o fst o dest_list) obs end) leafs);
        val message = "found " ^ (Int.toString numobss) ^ " observations in all paths.";
        val _ = print (message ^ "\n");
        (* val _ = bir_embexp_log (message); *)

        (* retrieval of path condition and observation expressions *)
	fun extract_cond_obs s =
	  let
	    val (_,_,cond,_,obs) = dest_bir_symb_state s;
	    val obss = ((List.map dest_bir_symb_obs) o fst o dest_list) obs;

	    (* determine whether this is an error state *)
	    val isErrorState = not (symb_is_BST_Halted s);

	    (* this converts BIR consts to HOL4 variables *)
	    val obs_list = List.map (fn (oid,ec,eo, obsf) =>
		   (oid,bir_exp_hvar_to_bvar ec, bir_exp_hvar_to_bvar eo, obsf)) obss;

	    (* we require singleton lists for the observations at the moment *)
	    (* check that we have HD as observation function, and apply it *)
	    val obs_list' = List.map (fn (oid,ec,eo,obsf) =>
		     let
		       val (otl,_) = dest_list eo;
		       val _ = (if listSyntax.is_hd ``^obsf x`` then () else raise ERR "" "")
			       handle _ =>
				 raise ERR "extract_cond_obs" ("currently we only support HD as observation function, not \"" ^ (term_to_string obsf) ^ "\"");
		     in
		       if length otl <> 1 then
		       	 raise ERR "extract_cond_obs" "currently we support only singleton observations"
		       else
			 (oid, ec, hd otl)
		     end
		   ) obs_list;
	  in
	    (bir_exp_hvar_to_bvar cond, if isErrorState then NONE else SOME obs_list')
	  end;

        val paths = List.map extract_cond_obs leafs;

        (* we also need all generated expressions to collect the variables *)
        val path_conds = List.map fst paths;
        val obs_exps = flatten (List.map (fn (_,x,y) => [x,y])
                          (flatten (List.map ((fn x =>
                             case x of NONE => [] 
                                     | SOME y => y) o snd) paths)));
        val all_exps = (path_conds @ obs_exps);
    in
        (paths, all_exps)
    end;
 

fun run_angr_symbexec prog_ =
  let
    val timer = timer_start 1;

    val res = bir_angrLib.do_symb_exec prog_;

    val timestrref = ref "";
    val _ = timer_stop (fn timestr => (timestrref := timestr; print ("angr symbolic execution took " ^ timestr ^ "\n"))) timer;
  in
    (res, !timestrref)
  end;

(*
=============================================================================
*)


val dafilename = "aes-aarch64.da";
val dafilename = "aes-2-aarch64.da";
val dafilename = "aes-vs-aarch64.da";
val dafilename = "retonly-aarch64.da";

(*
=============================================================================
*)

fun lift_prog dafilename =
    let
	val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
	val _ = set_trace "bir_inst_lifting.DEBUG_LEVEL" 2;

	val _ = print_with_style_ [Bold, Underline] ("Lifting " ^ dafilename ^ "\n");

	val (region_map, aes_sections) = read_disassembly_file_regions dafilename;

	val (thm_arm8, errors) = bmil_arm8.bir_lift_prog_gen ((Arbnum.fromInt 0), (Arbnum.fromInt 0x1000000)) aes_sections;

	val prog = (snd o dest_comb o concl) thm_arm8;


	val _ = print "\nLifting done.\n\n";
    in
	prog
    end;

(* val prog = lift_prog dafilename; *)

(*
=============================================================================
*)


fun main_loop 0 = ()
  |  main_loop n =
     let
	 open bir_prog_genLib;

	 val prog = if true then
			(* Prefetching *)
		     let	 
			 val gen_prefetch = prog_gen_store_prefetch_stride 3;
			 val prog = gen_prefetch ();
			 val (prog_id, lifted_prog) = prog;
		     in
			 lifted_prog
		     end
		    else
			(* Spectre *)	
		     let		 
			 (* val (prog_id, lifted_prog) = prog_gen_store_rand "" 2 (); *)
			 val (prog_id, lifted_prog) = prog_gen_store_a_la_qc  "spectre_v1" 5 ();
			 val prog = lifted_prog;
		     in
			 prog
		     end;
	     
	 val prog = (snd o dest_eq o concl o EVAL) prog;
	 val _ = print "\nInput prog prepared.\n\n";

	     
	 val _ = print "\nNow symbexecing.\n\n";

	 val (leaves, _) = run_naive_hol4_symbexec prog;

	 val (res, _) = run_angr_symbexec prog;

	 val _ = print "\nDone symbexecing.\n\n";
     in
	 main_loop (n-1)
     end;
    
(*
=============================================================================
*)

(* val _ = main_loop 2; *)

(*
=============================================================================
*)

val prog = “BirProgram
      [<|bb_label :=
           BL_Address_HC (Imm64 (0w :word64)) "D10043FF (sub sp, sp, #0x10)";
         bb_statements :=
           [(BStmt_Assign (BVar "SP_EL0" (BType_Imm Bit64))
               (BExp_BinExp BIExp_Minus
                  (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                  (BExp_Const (Imm64 (16w :word64)))) :
             'observation_type bir_stmt_basic_t)];
         bb_last_statement :=
           BStmt_Halt (BExp_Const (Imm64 8w))|>]”;

fun angr_symb_exec_list (bir_angrLib.exec_path s) =  s;


fun compare_angr_symb_exec_path
	(bir_angrLib.exec_path {observations = l1, ...})
	(bir_angrLib.exec_path {observations = l2, ...}) =
    length l1 = length l2;

compare_angr_symb_exec_path t2 t2;
    
fun scamv_to_angr t =
    let
	open listSyntax;
	open bir_symb_execLib;
	val (_,_,cond,_,obs) = dest_bir_symb_state t
	    handle _ => raise Fail "Scamv to Angr Failed";
	val obs_list = (fst o dest_list) obs;
	val r =  {final_pc = "0x0", guards = [cond], jmp_history = [], observations = obs_list};
    in
	bir_angrLib.exec_path r
    end;
    
strip_conj
