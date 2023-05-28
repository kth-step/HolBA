structure scamv_patchLib =
struct

local
    open HolKernel boolLib liteLib simpLib Parse bossLib;

    open bir_prog_genLib;
    open scamv_llvmLib;
    open embexp_logsLib;
    open experimentsLib;
    open persistenceLib;
    open bir_fileLib;

    (* error handling *)
    val libname  = "scamv_patchLib"
    val ERR      = Feedback.mk_HOL_ERR libname
    val wrap_exn = Feedback.wrap_exn libname
in

val (bt : string ref) = ref "";

val (current_patch_count: int ref) = ref 0;
val (current_fence_config: (int * bool) list option ref) = ref NONE;
val current_counterexamples = ref NONE;

fun set_board_type btype =
    bt := btype

fun reset () =
    (current_patch_count := 0;
     current_fence_config := NONE;
     current_counterexamples := NONE);

fun own_llvm_fence_insertion fname llvm_prog_bc binprog =
    let
      val patched_llvm_prog_bc = llvm_insert_fence fname llvm_prog_bc;
      val patched_bin_prog = case patched_llvm_prog_bc of
			       SOME patch_llvm_bc =>
			       let
				 val _ = current_patch_count := (!current_patch_count) + 1;
				 val bname = (binprog ^ "_" ^ (Int.toString (!current_patch_count)))
			       in
				 (SOME (compile_and_link_armv8_llvm_bc bname patch_llvm_bc (!bt))
				  handle HOL_ERR e => raise ERR "patch_current_llvm_prog" "error in compiling the patched LLVM program")
			       end
			     | NONE => NONE;
    in
      (patched_llvm_prog_bc, patched_bin_prog)
    end
fun aarch64_slh fname llvm_prog_bc binprog =
    let
      val patched_llvm_prog_bc = add_slh_attribute llvm_prog_bc;
      val patched_bin_prog = llvm_aarch64_slh binprog llvm_prog_bc (!bt)
    in
      (SOME llvm_prog_bc, patched_bin_prog)
    end
    
fun patch_current_llvm_prog () =
    let
      val patched_llvm_prog =
	case (!current_llvm_prog) of
	  SOME ((fname,fdesc,llvm_prog_bc), binprog) =>
	    let
	      (* val _ = print ("\nFunction: " ^ fname ^ "\n" ^ "File: " ^ llvm_prog_bc ^ "\n"); *)
	      (* val (patched_llvm_prog_bc, patched_bin_prog) = own_llvm_fence_insertion fname llvm_prog_bc binprog; *)
	      val (patched_llvm_prog_bc, patched_bin_prog) = aarch64_slh fname llvm_prog_bc binprog;
	    in
	      ((fname, fdesc, patched_llvm_prog_bc), patched_bin_prog)
	    end
	| NONE => raise ERR "patch_current_prog" "there is no llvm program under analysis, llvm patching cannot happen"
    in
      case patched_llvm_prog of
	  ((f,fd,SOME p), SOME b) => SOME ((f,fd,p),b)
	| _ => (current_patch_count := 0; NONE)
    end;
    
fun db_adding_patched_prog_w_cexps p cexamples =
    let
      open Json;
      (* initialise a new run for the patched program *)
      val _ = run_init (SOME "patch");

      val ((fname,fdesc,llvm_prog_bc), binfilename) = p;
      val prog = mk_experiment_prog []; (* this is useless *)
      val binstripped = bir_gccLib.bir_gcc_remove_data_section binfilename;
      val patched_prog_id =
	run_create_prog
	  ArchARM8
	  prog
	  binstripped
	  ([("patchbinfile", binfilename)]@
	   [("pathfilename", llvm_prog_bc), ("function_description", fdesc)]);

      val (entry, exits) = let
	                     val disassembly = process_binary binfilename;
			     val section = get_section_by_name fname disassembly;
			     val listEntryExits = List.map define_entry_and_exits [valOf section]
                           in
			     (case listEntryExits of
				[(en: Arbnum.num, ex: Arbnum.num list)] => (en, ex)
			      | _ => raise ERR "patch_current_prog_on_cexamples" "error in defining entry and exit points")
			   end;

      val exps = get_exps_outside (List.map (fn eid=> Arbnum.fromString eid) cexamples);

      val exp_ids = List.map (fn LogsExp (_,_,params,OBJECT inputs,_,_) =>
				 let
				   val exp_id =
				     run_create_exp
				       patched_prog_id
				       ExperimentTypeStdTwo
				       params
				       (List.map (fn (s,j)=> (List.nth (String.tokens (fn x => x = #"_") s, 1), Json_to_machstate j)) inputs)
				       entry
				       exits
				       [(* ("state_gen_id", !current_obs_model_id) *)];
				   val exp_gen_message = "Generated experiment: " ^ (embexp_logsLib.exp_handle_toString exp_id);
				   val _ = run_log_prog exp_gen_message;
				 in exp_id end) exps;
    in
      false
    end;

fun patch_current_prog_on_cexamples cexamples =
    let
      fun update_llvm_progs patched_llvm_prog =
	  current_llvm_progs := SOME (patched_llvm_prog::(valOf (!current_llvm_progs)));

      (* Note: always the same LLVM bitcode file will be modified,
         there is no need to update the current_llvm_prog*)
      val stop = case patch_current_llvm_prog () of
		     SOME p =>
		     let
			 (* add to the list to be a new program to test *)
			 val _ = if false then update_llvm_progs p else ();
		     in
			 db_adding_patched_prog_w_cexps p cexamples
		     end
		   | NONE => true (* raise ERR "patch_current_prog_on_cexamples" "no LLVM program to test" *);
      (*val stop = case (!current_llvm_prog) of
		     SOME p => db_adding_patched_prog_w_cexps p cexamples
		   | NONE => raise ERR "patch_current_prog_on_cexamples" "there is no program under analysis"*)
    in
	stop
    end

fun fence_reduction  binfilename bcfile =
    let
      fun set_fence_config (l::ls) =	
	case (l::ls) of
	    (1, false)::ls => (0,true)::ls
	  | (0, false)::_ => raise ERR "fence_reduction::set_fence_config" "should never happen"
	  | _::[] => raise ERR "fence_reduction::set_fence_config" "there are no more fences"
	  | _::ls => l::(set_fence_config ls)
      val _ = current_fence_config :=
	      (case (!current_fence_config) of
		   NONE => raise ERR "fence_reduction::fence_config" "should never happen"
		 | SOME fl => SOME (set_fence_config fl));
	    
      val fence_config_str = "-fc " ^ List.foldr (fn (f,l) => (Int.toString (fst f)) ^ l) "" (valOf (!current_fence_config));
      val (_,fc) = scamv_llvmLib.remove_fence_slh binfilename bcfile (!bt) fence_config_str;
      val _ = print (PolyML.makestring (fc) ^ "\n");
  
      val check =
	case (!current_llvm_prog) of
	    SOME p => db_adding_patched_prog_w_cexps p (valOf (!current_counterexamples))
	  | NONE => raise ERR "patch_current_prog_on_cexamples" "there is no program under analysis";
      val mf_exp_list_name = get_last_exp_list_name ();
      val _ = print ("Last list exp: " ^ mf_exp_list_name ^ "\n");
      val _ = check_exp_list_is_running ();
      val still_cexps = get_cexamples mf_exp_list_name (!bt);
    in
      still_cexps
    end
    
fun test_last_exps board_type do_patching =
    let
      val _ = set_board_type board_type;
      val exp_list_name = get_last_exp_list_name ();
      val _ = print ("List exp: " ^ exp_list_name ^ "\n");
      val _ = check_exp_list_is_running ()
    in
     (if do_patching then
        let
	  fun init_run_for_nex_prog () =
	    (* Start a new run for the next program *)
	    case (!current_llvm_progs) of
		NONE => raise ERR "run_last_exps::init_run_for_nex_prog" "should never happen"
	      | SOME [] => ()
	      (* | SOME (l::nil) => () *)
	      | SOME (l::ls) => run_init NONE;

	  val _ = current_counterexamples := embexp_logsLib.get_cexamples exp_list_name (!bt);
	in
	  case (!current_counterexamples) of
	    SOME cexps =>
	    let
	      val _ = print ("\n" ^ ((Int.toString o List.length) cexps)  ^ " counterexamples found\n");
	      val skip = if true then patch_current_prog_on_cexamples cexps
			 else patch_current_prog_on_cexamples (List.take (cexps, 10)) (*FIX ME*)
	      val llvm_slh_exp_list_name = get_last_exp_list_name ();
	      val _ = print ("LLVM SLH List exp: " ^ llvm_slh_exp_list_name ^ "\n");
	      val _ = check_exp_list_is_running ();
	      val still_cexps = get_cexamples llvm_slh_exp_list_name (!bt);

	      val num_of_fences =
		case (!current_llvm_prog) of
		    SOME ((_,_,llvm_prog_bc), binprog) =>
		    (case scamv_llvmLib.get_num_of_fences binprog llvm_prog_bc (!bt) of
			  NONE => raise ERR "test_last_exps::num_of_fences" "number is not a integer"
			| SOME nf =>
			  let fun init_fence_config 0 = [(1,false)]
				| init_fence_config n =
				  (1,false)::init_fence_config (n-1)
			  in
			    current_fence_config := SOME (init_fence_config nf)
			  end)
		  | NONE => raise ERR "test_last_exps::num_of_fences" "there is no llvm program under analysis";

	      fun minimization () =
		case still_cexps of
		    SOME cexps => init_run_for_nex_prog ()
		  | NONE => case (!current_llvm_prog) of
				SOME ((_,_,llvm_prog_bc), binprog) => (
				print("BC: " ^ llvm_prog_bc ^ "\n" ^ "BIN: " ^ binprog ^ "\n");
				fence_reduction binprog llvm_prog_bc;
				minimization ()
				)
			      | _ => raise ERR "minimization" ""    
	    in
	      case still_cexps of
		  SOME cexps => raise ERR "" "LLVM SLH did not stop counterexamples" (*init_run_for_nex_prog ()*)
		| NONE => minimization ()
	    end
	  | NONE => init_run_for_nex_prog ()
	end
      else ())
    end;

(*
fun run_last_exps () =
    (* NOTE: A new run - (holba_run_refs (and exp_list_handle)) - for each program *)
    let
      val _ = set_board_type board_type;
      val exp_list_name = get_last_exp_list_name ();
      val _ = print ("List exp: " ^ exp_list_name ^ "\n");
      (* val _ = run_exp_list exp_list_name (!bt); *)
      val _ = check_exp_list_is_running ()
    in
     (if do_patching then
        let
	  fun init_run_for_nex_prog () =
	    (* Start a new run for the next program *)
	    case (!current_llvm_progs) of
		NONE => raise ERR "run_last_exps::init_run_for_nex_prog" "should never happen"
	      | SOME [] => ()
	      (* | SOME (l::nil) => () *)
	      | SOME (l::ls) => run_init NONE;

	  val cexamples = get_cexamples exp_list_name (!bt);
	in
	  case cexamples of
	    SOME cexps =>
	    let
	      val _ = print ("\n" ^ ((Int.toString o List.length) cexps)  ^ " counterexamples found\n");
	      val skip = patch_current_prog_on_cexamples cexps;
	    in
		if skip then
		    init_run_for_nex_prog ()
		else run_last_exps ()
	    end
	  | NONE => init_run_for_nex_prog ()
	end
      else ())
    end;
*)


end

end
