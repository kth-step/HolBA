structure bir_scamv_driverLib :> bir_scamv_driverLib =
struct

open HolKernel boolLib liteLib simpLib Parse bossLib;

open bir_prog_genLib;

open bir_obs_modelLib;
open bir_exp_to_wordsLib;
open bir_rel_synthLib;
open bslSyntax;
open numSyntax;
open wordsSyntax;
open wordsLib;
open stringSyntax;
open listSyntax;
open experimentsLib;
open persistenceLib;
open bir_symb_execLib;
open bir_symb_masterLib;
open bir_typing_expTheory;
open bir_programSyntax;
open scamv_configLib;
open scamv_symb_exec_interfaceLib;
open bir_conc_execLib;
open scamv_path_structLib;
open visited_statesLib;
open bir_utilLib;
open scamv_trainingLib;

  (* error handling *)
  val libname  = "bir_scamv_driverLib"
  val ERR      = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname 

fun print_exn_location_option printfun (lo: PolyML.location option) =
  case lo of
     NONE => printfun "NO EXCEPTION LOCATION\n\n"
   | SOME (l:{file: string, startLine: int, endLine: int, startPosition: int, endPosition: int}) => (
       let val s1 =
         "EXCEPTION LOCATION:\n" ^
         " - file:      " ^ (#file l) ^ "\n" ^
         " - lines:     " ^ (Int.toString (#startLine l))     ^ "-" ^ (Int.toString (#endLine l))     ^ "\n" ^
         " - positions: " ^ (Int.toString (#startPosition l)) ^ "-" ^ (Int.toString (#endPosition l)) ^ "\n" ^
         "\n";
       in printfun s1 end);

fun handle_locinfo printfun f =
  let
    val r =
      PolyML.Exception.traceException (f, (fn (l,e) => (
        printfun ("\nTRACE\n==================\nEXCEPTION: " ^ (PolyML.makestring e) ^ "\n");
        print "EXCEPTION TRACE:\n";
        List.map print l ;
        PolyML.Exception.reraise e)))
      (* PolyML.Exception.exception_trace f *)
      handle e => (
        printfun ("\nEXCEPTION: " ^ (PolyML.makestring e) ^ "\n");
        print_exn_location_option printfun (PolyML.Exception.exceptionLocation e);
        PolyML.Exception.reraise e);
  in r end;

(*
 workflow:
 - (a) program generation
 - lifting
 - (b) obs model augmentation
 - symbolic execution
 - conversion to symbolic observation paths (n paths)
 - relation synthesis
 - (c) relation partitioning (m partitions)
 - somewhere around here: constraining memory accesses (and probably some registers or flags) for test setup
 - state generation using SMT solver
 - test execution
 - driver decision (jump to a, b or c)
 *)

exception NoObsInPath;

(* Prints a model, one variable per line. *)
fun print_model model =
    List.foldl
        (fn ((name, tm), _) =>
            (print (" - " ^ name ^ ": "); Hol_pp.print_term tm))
        () (rev model);


val hw_obs_model_id = ref "";
val do_enum = ref false;
val do_training = ref false;
val do_conc_exec = ref false;
val angr_symbexec = ref true;
val do_patching = ref false;
val patch_count = ref 0;
val do_run_exps = ref false;
val board_type = ref "";

val (current_prog_id : embexp_logsLib.prog_handle option ref) = ref NONE;
val (current_prog : term option ref) = ref NONE;
val (current_prog_entry_and_exits : (Arbnum.num * Arbnum.num list) option ref) = ref NONE;
val (current_prog_binary_pathname : string option ref) = ref NONE;
val (current_prog_w_obs : term option ref) = ref NONE;
val (current_prog_w_refined_obs : term option ref) = ref NONE;
val (current_obs_model_id : string ref) = ref "";
val (current_refined_obs_model_id : string option ref) = ref NONE;
val (current_obs_projection : int ref) = ref 1;
val (current_pathstruct :
     path_struct option ref) = ref NONE;
val (current_full_specs : path_spec list ref) = ref [];
val (current_visited_map : visited_map ref) = ref (init_visited ());
val (current_word_rel : term option ref) = ref NONE;
(*val (next_iter_rel    : (path_spec * term) option ref) = ref NONE; *)

fun reset () =
    (current_prog_id := NONE;
     current_prog := NONE;
     current_prog_entry_and_exits := NONE;
     current_prog_binary_pathname := NONE;
     current_prog_w_obs := NONE;
     current_prog_w_refined_obs := NONE;
     current_pathstruct := NONE;
     current_visited_map := init_visited ();
     current_full_specs := [];
     current_word_rel := NONE);

fun observe_line e =
    brshift (band (e, blshift (bconst64 0x7f, bconst64 6)), bconst64 6);

fun collect_observations observe_fun pathstruct =
    let fun collect_from_leaf NONE = []
          | collect_from_leaf (SOME leaf) =
            List.map (observe_fun o snd) leaf;

        val leaves = List.map snd pathstruct;
    in
        List.concat (List.map collect_from_leaf leaves)
    end

(* fun collect_targets observe_fun path pathstruct = *)
(*     let fun collect_from_leaf NONE = [] *)
(*           | collect_from_leaf (SOME leaf) = *)
(*             List.map (observe_fun o snd) leaf; *)

(*         val leaf = List.find (fn entry => fst entry = path) pathstruct; *)
(*     in *)
(*         case leaf of *)
(*             NONE => raise ERR "collect_targets" "wrong path given" *)
(*          | SOME l => *)
(*            List.concat (List.map collect_from_leaf leaves) *)
(*     end *)

fun enumerate_line_single_input path_struct =
    let val vars = extract_obs_variables path_struct
    in
        case vars of
            [] => []
          | (v::vs) => [(observe_line (bden (bvarimm64 (fromHOLstring v))),
                         bir_rel_synthLib.enum_range (0,60))]
    end;

fun default_enumeration_targets paths =
    if !do_enum
    then enumerate_line_single_input paths
    else [];

fun scamv_set_prog_state prog =
    let val (prog_id, lifted_prog, binfilename, entry_and_exits) = prog;
        val _ = current_prog_id := SOME prog_id;
        val _ = current_prog := SOME lifted_prog;
	val _ = current_prog_entry_and_exits := SOME entry_and_exits;
	val _ = current_prog_binary_pathname := SOME binfilename;
        val _ = min_verb 2 (fn () => print_term lifted_prog);
    in
      (prog_id, lifted_prog)
    end;

fun scamv_phase_add_obs () =
let 
  val _ = printv 1 "Adding obs\n";
  val obs_model = get_obs_model (!current_obs_model_id);
  val add_obs = #add_obs obs_model;
  val proginst_fun = proginst_fun_gen (#obs_hol_type obs_model);
  val entry = fst (valOf (!current_prog_entry_and_exits));
  val mem_bounds =
      let
        val (mem_base, mem_len) = embexp_params_memory;
        val mem_end = (Arbnum.- (Arbnum.+ (mem_base, mem_len), Arbnum.fromInt 128));
      in
        pairSyntax.mk_pair
            (mk_wordi (embexp_params_cacheable mem_base, 64),
             mk_wordi (embexp_params_cacheable mem_end, 64))
      end;
  val lifted_prog_w_obs = add_obs mem_bounds (proginst_fun (valOf (!current_prog))) entry;
  val _ = printv 1 "Obs added\n";
  val _ = current_prog_w_obs := SOME lifted_prog_w_obs;
  val _ = min_verb 3 (fn () => print_term lifted_prog_w_obs);
in
  lifted_prog_w_obs
end;

fun scamv_phase_symb_exec () =
    let
      val (paths, all_exps) =
        scamv_run_symb_exec
	  (valOf (!current_prog_w_obs))
	  (valOf (!current_prog_binary_pathname))
	  (valOf (!current_prog_entry_and_exits))
	  (!angr_symbexec);
      val _ = List.map (Option.map (List.map (fn (a,b,c) => print_term b)) o snd) paths;
      val ps = initialise paths;
      val _ = current_pathstruct := SOME ps;
      val _ = min_verb 4 (fn () => (print_path_struct ps; print (PolyML.makestring ps)));
    in
      ps
    end;

fun scamv_get_model word_relation =
    let
(*
val mem1_var = mk_var ("MEM", “:word64 |-> word8”);
val mem2_var = mk_var ("MEM'", “:word64 |-> word8”);

val word_relation = “
(w2w (w2w (^mem1_var ' R1) :word64):word1)
=
w2w (^mem2_var ' R2)”;

to_new_name "MEM"
to_new_name "MEM'"
val t = hd vars
*)
      fun to_new_name n =
        "sv_" ^ (if String.isSuffix "'" n then (String.substring(n, 0, (String.size n)-1) ^ "_p") else n);
      fun var_to_new t =
        let
          val (vn, vt) = dest_var t;
        in
          (t, mk_var (to_new_name vn, vt))
        end;
      fun rev_model_name rev_maplist (n_new, v) =
        let
          val m_o = List.find (fn (_, x) => x = n_new) rev_maplist;
          val n = case m_o of
             SOME (n,_) => n
           | NONE => raise ERR "scamv_get_model" "unexpected error";
        in
          (n, v)
        end;

      val vars = free_vars word_relation;
      val vars_to_new = List.map var_to_new vars;
      val varnames_to_new = List.map (fn (a,b) => ((fst o dest_var) a, (fst o dest_var) b)) vars_to_new;

      val word_relation_newnames = subst (List.map (|->) vars_to_new) word_relation;
      val model_newnames = Z3_SAT_modelLib.Z3_GET_SAT_MODEL word_relation_newnames;
      val model = List.map (rev_model_name varnames_to_new) model_newnames;
      val _ = min_verb 4 (fn () => (print "SAT model:\n"; print_model model; print "\nSAT model finished.\n"));

    in
      model
    end;

(*
val model = [
 ("MEM", “FUN_FMAP ((K 0w) :word64->word8) 𝕌(:word64)”),
 ("MEM'", “FUN_FMAP ((K 0w) :word64->word8) 𝕌(:word64)”),
 ("R26", “0x80100020w:word64”),
 ("R26'", “0x80100000w:word64”),
 ("R28", “0x80100001w:word64”),
 ("R28'", “0x80100000w:word64”)
];
*)

fun scamv_process_model model =
    let
      val (s1, s2) =
        let
          val (primed, nprimed) = List.partition ((String.isSuffix "'") o fst) model;
          val primed_rm = List.map (fn (r,v) => ((remove_suffix "'") r,v)) primed;
        in
          (to_sml_Arbnums nprimed, to_sml_Arbnums primed_rm)
        end;

      val _ = List.app (fn (st_n, st) =>
          if embexp_params_checkmemrange st then () else
          raise ERR "scamv_process_model"
                    (st_n ^ " memory contains mapping out of experiment range." ^
                     "is there a problem with the constraints?")
        ) [("s1", s1), ("s2", s2)];

      fun mk_var_val_mapping m =
        let
          fun mk_var_val_eq (n,v) = mk_eq (mk_var (n, type_of v), v);
        in list_mk_conj (List.map mk_var_val_eq m) end;

      (* filter the model for registers to create the constraint "different from this state pair" *)
      fun is_a_mem (n,_) = List.exists (fn x => x = n) ["MEM'", "MEM"];
      val regs = List.filter (not o is_a_mem) model;
      val constraint = mk_neg (mk_var_val_mapping regs);
    in
      (s1, s2, constraint)
    end;

fun scamv_phase_rel_synth_init () =
    let
      val paths = valOf (!current_pathstruct);
      val enum_env = default_enumeration_targets paths;
      val relation_enumeration =
          rel_synth_init paths (!current_obs_projection) enum_env; (* TODO consider validity *)
    in
      relation_enumeration
    end;

fun scamv_per_program_init prog =
    let
        val _ = reset ();

	val _ = (fn (_,_,_,(entry,_))=> print ("\nEntry: " ^ "0x" ^ (Arbnum.toHexString entry) ^ "\n")) prog;

        val _ = scamv_set_prog_state prog;
        val _ = scamv_phase_add_obs ();
        val _ = scamv_phase_symb_exec ();

        val result = scamv_phase_rel_synth_init ();
    in result end;

fun all_obs_not_present { a_run = (_,a_obs), b_run = (_,b_obs) } =
    let fun check xs = all (fn (b,_) => b = false) xs;
    in check a_obs andalso check b_obs
    end;

fun next_experiment all_exps next_relation (entry,exits) =
    let
        open bir_expLib;

	(* measuring time*)
	val timer = (Time.now());

        (* ADHOC this constrains paths to only those where *)
	(* none of the observations appear *)
        val guard_path_spec =
            if !do_enum
            then all_obs_not_present
            else (fn _ => true);

        val (path_spec, rel) =
	  (*   case !next_iter_rel of *)
		(* NONE        => valOf (next_relation guard_path_spec)  *)
	  (*     | SOME (p, r) => let val _ = next_iter_rel := NONE in (p, r) end *)
            valOf (next_relation guard_path_spec)
		        handle Option =>
                       raise ERR "next_experiment" "next_relation returned a NONE";
        val _ = min_verb 2 (fn () =>
                               (print "Selected path: ";
                                print (PolyML.makestring path_spec);
                                print "\n"));

        val _ = min_verb 3 (fn () =>
                               bir_exp_pretty_print rel);
        val _ = printv 4 ("Word relation\n");
        val new_word_relation = make_word_relation rel true;
        val print_word_rel_wtypes = false;
        val term_to_string_sel = if print_word_rel_wtypes then term_to_string_wtypes else term_to_string;
        val _ = min_verb 4 (fn () =>
                               (print (term_to_string_sel new_word_relation);
                                print "\n"));
(*        val word_relation =
            case !current_word_rel of
                NONE => new_word_relation
	      (* r is a constraint used to build the next relation for path enumeration *)
              | SOME r => mk_conj (new_word_relation, r); *)
        val word_relation = mk_conj(new_word_relation, lookup_visited (!current_visited_map) path_spec)
                            handle NotFound => new_word_relation;

        val _ = printv 2 ("Calling Z3\n");
        val (s1, s2, new_constraint) = (scamv_process_model o scamv_get_model) word_relation;
        val _ = min_verb 1 (fn () =>
                               (print "s1:\n";
                                machstate_print s1;
                                print "\n"));
        val _ = min_verb 1 (fn () =>
                               (print "s2:\n";
                                machstate_print s2;
                                print "\n"));
        val _ = min_verb 4 (fn () =>
                               (print "new constraint:\n";
                                print (term_to_string_sel new_constraint);
                                print "\n"));

        val prog_id =
          case !current_prog_id of
             NONE => raise ERR "next_experiment" "currently no prog_id loaded"
           | SOME x => x;

        val _ =
            current_visited_map := add_visited (!current_visited_map) path_spec new_constraint;
        val _ =
            current_word_rel := SOME (lookup_visited_all_paths (!current_visited_map));
(*                        current_word_rel :=
            (case !current_word_rel of
                 NONE => SOME new_constraint
               | SOME cumulative =>
                 SOME ``^cumulative /\ ^new_constraint``); *)

	(* ------------------------- training start ------------------------- *)
        val paths = valOf (!current_pathstruct);
        val st_o =
            if !do_training
            then
              SOME (
              compute_training_state (!current_full_specs)
                                     (!current_obs_projection)
                                     (lookup_visited (!current_visited_map) path_spec)
                                     (fst (#a_run path_spec))
                                     paths)
            else
              NONE;
	(* ------------------------- training end ------------------------- *)
	(* val _ = print_term (valOf (!current_word_rel)); *)

        (* check with concrete-symbolic execution whether the observations are actually equivalent *)
        val lifted_prog_w_obs = case !current_prog_w_obs of
				    SOME x => x
				  | NONE => raise ERR "next_test" "no program found";

        val _ = if not (!do_conc_exec) then () else (
          let
            val ce_obs_comp = conc_exec_obs_compare (!current_obs_projection) lifted_prog_w_obs (s1, s2);
            val _ = if ce_obs_comp then () else
                raise ERR "next_experiment" "Experiment does not yield equal observations, won't generate an experiment.";
          in () end);

	(* show time *)
	val d_s = Time.- (Time.now(), timer) |> Time.toString;
	val _ = print ("Time to generate the experiment : "^d_s^"\n");

        (* create experiment files *)
        val exp_id  =
          run_create_exp
            prog_id
            ExperimentTypeStdTwo
            (!hw_obs_model_id)
            ([("1", s1), ("2", s2)]@(Portable.the_list (Option.map (fn st => ("train", st)) st_o)))
            entry
	    exits
            [("state_gen_id", !current_obs_model_id), ("time", d_s)];
        val exp_gen_message = "Generated experiment: " ^ (embexp_logsLib.exp_handle_toString exp_id);
        val _ = run_log_prog exp_gen_message;

    in ()
    end;

fun patch_current_llvm_prog () =
    let
      open scamv_llvmLib;

      val patched_llvm_prog =
	case (!current_llvm_prog) of
	  SOME ((fname,fdesc,llvm_prog_bc), binprog) =>
	    let
	      (* val _ = print ("\nFunction: " ^ fname ^ "\n" ^ "File: " ^ llvm_prog_bc ^ "\n"); *)
	      val patched_llvm_prog_bc = llvm_insert_fence fname llvm_prog_bc;
	      val patched_bin_prog = case patched_llvm_prog_bc of
					 SOME patch_llvm_bc =>
					   let
					     val _ = patch_count := (!patch_count) + 1;
					     val bname = (binprog ^ "_" ^ (Int.toString (!patch_count)))
					   in
					     (SOME (compile_and_link_armv8_llvm_bc bname patch_llvm_bc (!board_type))
					      handle HOL_ERR e => raise ERR "patch_current_llvm_prog" "error in compiling the patched LLVM program")
					   end
				       | NONE => NONE;
	    in
	      ((fname, fdesc, patched_llvm_prog_bc), patched_bin_prog)
	    end
	| NONE => raise ERR "patch_current_prog" "there is no llvm program under analysis, llvm patching cannot happen"
    in
      case patched_llvm_prog of
	  ((f,fd,SOME p), SOME b) => SOME ((f,fd,p),b)
	| _ => (patch_count := 0; NONE)
    end;

fun patch_current_prog_on_cexamples cexamples =
    let
      open embexp_logsLib;
      open Json;

      fun update_llvm_progs patched_llvm_prog =
	  current_llvm_progs := SOME (patched_llvm_prog::(valOf (!current_llvm_progs)));

      (* Note: always the same LLVM bitcode file will be modified,
         there is no need to update the current_llvm_prog*)
      val stop = case patch_current_llvm_prog () of
				SOME p => let
      (* add to the list to be a new program to test *)
      val _ = if false then update_llvm_progs p else ();
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
				       [("state_gen_id", !current_obs_model_id)];
				   val exp_gen_message = "Generated experiment: " ^ (embexp_logsLib.exp_handle_toString exp_id);
				   val _ = run_log_prog exp_gen_message;
				 in exp_id end) exps;
	  in false end
	  | NONE => true (* raise ERR "patch_current_prog_on_cexamples" "no LLVM program to test" *)
    in
      stop
    end;

fun run_last_exps () =
    (* NOTE: A new run - (holba_run_refs (and exp_list_handle)) - for each program *)
    let
      open embexp_logsLib;
      val exp_list_name = get_last_exp_list_name ();
      val _ = print ("List exp: " ^ exp_list_name ^ "\n");
      val _ = run_exp_list exp_list_name (!board_type);
    in
     (if (!do_patching) then
        let
	  fun init_run_for_nex_prog () =
	    (* Start a new run for the next program *)
	    case (!current_llvm_progs) of
		NONE => raise ERR "run_last_exps::init_run_for_nex_prog" "should never happen"
	      | SOME [] => ()
	      (* | SOME (l::nil) => () *)
	      | SOME (l::ls) => run_init NONE;

	  val cexamples = embexp_logsLib.get_cexamples exp_list_name (!board_type);
	in
	  case cexamples of
	    SOME cexps =>
	    let
	      val _ = print ("\n" ^ ((Int.toString o List.length) cexps)  ^ " counterexamples found\n");
	      val skip = patch_current_prog_on_cexamples cexps
	    in
		if skip then
		    init_run_for_nex_prog ()
		else run_last_exps ()
	    end
	  | NONE => init_run_for_nex_prog ()
	end
      else ())
    end;

fun scamv_test_main tests (prog_id, prog_lifted, binfilename, list_entries_and_exits) =
    let
        val _ = reset();
        val exit_threshold = tests;

	fun test_prog entry_and_exits =
	    let
              val _ = (fn (en,exs) => if List.null exs then raise ERR "" "no exit point defined" else ())
 entry_and_exits;
	      val prog = (prog_id, prog_lifted, binfilename, entry_and_exits);

              val (full_specs, validity, next_relation) = scamv_per_program_init prog;
	      val _ = current_full_specs := full_specs;

	      fun init_tests () = (current_word_rel := NONE; current_full_specs := []; current_visited_map := init_visited ());
	      fun do_tests _ 0 entry_and_exits = init_tests ()
		| do_tests 0 _ entry_and_exits = (init_tests (); raise ERR "scamv_test_main" ("couldn't generate new test cases for " ^ (Int.toString exit_threshold) ^ " times"))
		| do_tests r n entry_and_exits =
		  let val success =
                  (handle_locinfo print (fn () => next_experiment [] next_relation entry_and_exits); true)
                  handle e as Thread.Interrupt => (
                    run_log_prog "Keyboard interrupt!\n";
		    PolyML.Exception.reraise e)
		       |  e => (
			  let
			    val message = "Skipping test case due to exception in pipleline:\n" ^ PolyML.makestring e ^ "\n***\n";
			  in
			    run_log_prog message;
			    print message;
			    false
			  end
			  )
		  in
		    if success then
                      do_tests exit_threshold (n-1) entry_and_exits
		    else
                      do_tests (r-1) n entry_and_exits
		  end
	    in
              do_tests exit_threshold tests entry_and_exits
	    end;

	fun do_tests_with_entries_and_exits [] = if (!do_run_exps) then run_last_exps () else ()
	  | do_tests_with_entries_and_exits (x::xs) =
	    let
              val excep_handler =
              (handle_locinfo print (fn () => test_prog x); true)
              handle e => (
                    let
                      val message = "Skipping test case due to exception in pipleline:\n" ^ PolyML.makestring e ^ "\n***\n";
                    in
                      run_log_prog message;
                      print message;
                      false
                    end
		     )
	    in
	      do_tests_with_entries_and_exits xs
	    end
    in
	(* outer loop *)
	do_tests_with_entries_and_exits list_entries_and_exits
    end

fun scamv_test_single_file filename =
    let val prog = prog_gen_store_fromfile filename ();
    in scamv_test_main 1 prog
    end;

fun show_error_no_free_vars (id,_) =
    print ("Program " ^ id ^ " skipped because it has no free variables.\n");

fun match_prog_gen gen sz generator_param =
    case gen of
        gen_rand => (
          case generator_param of
              SOME x => prog_gen_store_rand x  sz
            | NONE   => prog_gen_store_rand "" sz)
      | qc => (case generator_param of
              SOME x => prog_gen_store_a_la_qc x sz
            | NONE   => raise ERR "match_prog_gen::qc" "qc type needs to be specified as generator_param")
      | slice => prog_gen_store_rand_slice sz
      | from_file => (case generator_param of
              SOME x => prog_gen_store_fromfile x
            | NONE   => raise ERR "match_prog_gen::from_file" "file needs to be specified as generator_param")
      | from_list    => (case generator_param of
              SOME x => prog_gen_store_list x
            | NONE   => raise ERR "match_prog_gen::from_list" "list needs to be specified as generator_param")
      | from_binary  => (case generator_param of
              SOME x => prog_gen_store_frombinary x NONE
            | NONE   => raise ERR "match_prog_gen::from_binary" "binary needs to be specified as generator_param")
      | from_llvm    => (case generator_param of
              SOME x => prog_gen_store_fromllvm x
            | NONE   => raise ERR "match_prog_gen::from_llvm" "llvm needs to be specified as generator_param")
      | prefetch_strides => prog_gen_store_prefetch_stride sz
      | _ => raise ERR "match_prog_gen" ("unknown generator type: " ^ (PolyML.makestring gen));

fun match_obs_model obs_model =
    case obs_model of
        mem_address_pc =>
        "mem_address_pc"
      | mem_address_pc_lspc =>
        "mem_address_pc_lspc"
      | cache_tag_index  =>
        "cache_tag_index"
      | cache_tag_only =>
        "cache_tag_only"
      | cache_index_only =>
        "cache_index_only"
      | cache_tag_index_part =>
        "cache_tag_index_part"
      | cache_speculation =>
        "cache_speculation"
      | cache_speculation_first =>
        "cache_speculation_first"
      | cache_straightline =>
        "cache_straightline"
      | cache_tag_index_part_page =>
        "cache_tag_index_part_page"
      | _ => raise ERR "match_obs_model" ("unknown obs_model " ^ PolyML.makestring obs_model);

fun match_hw_obs_model hw_obs_model =
    case hw_obs_model of
        hw_cache_tag_index  =>
        "cache_multiw"
      | hw_cache_index_numvalid =>
        "cache_multiw_numinset"
      | hw_cache_tag_index_part =>
        "cache_multiw_subset"
      | hw_cache_tag_index_part_page =>
        "cache_multiw_subset_page_boundary"
      | _ => raise ERR "match_hw_obs_model" ("unknown hw_obs_model: " ^ (PolyML.makestring hw_obs_model));

fun scamv_run { max_iter = m, prog_size = sz, max_tests = tests, enumerate = enumerate
              , generator = gen, generator_param = generator_param
              , obs_model = obs_model, hw_obs_model = hw_obs_model
              , refined_obs_model = refined_obs_model, obs_projection = proj
              , verbosity = verb, seed_rand = seed_rand, do_training = train
              , run_description = descr_o, exec_conc = doexecconc, angr_symbexec = angr_se
	      , do_patching = patching } =
    let

        val _ = bir_randLib.rand_isfresh_set seed_rand;

        val _ = run_init descr_o;

        val _ = do_enum := enumerate;
        val _ = do_training := train;
        val _ = do_conc_exec := doexecconc;
        val _ = current_obs_projection := proj;
	val _ = angr_symbexec := angr_se;
	val _ = do_patching := patching;
	val _ = if (!do_patching) then do_run_exps := true else ();
	val _ = board_type := "rpi4";
        
        val prog_store_fun =
            match_prog_gen gen sz generator_param;

        val _ =
            current_obs_model_id := match_obs_model obs_model;

        val _ =
            current_refined_obs_model_id := Option.map match_obs_model refined_obs_model;

        val _ =
            hw_obs_model_id := match_hw_obs_model hw_obs_model;

        val config_str =
          "Scam-V set to the following test params:\n" ^
          ("Program generator    : " ^ PolyML.makestring gen ^ "\n") ^
          ("Prog gen params      : " ^ PolyML.makestring generator_param ^ "\n") ^
          ("Observation model    : " ^ !current_obs_model_id ^ "\n") ^
          ("Refined observation model: " ^ PolyML.makestring (!current_refined_obs_model_id) ^ "\n") ^
          ("Projection model: " ^ PolyML.makestring proj ^ "\n") ^
          ("HW observation model : " ^ !hw_obs_model_id ^ "\n") ^
          ("Enumerate            : " ^ PolyML.makestring (!do_enum) ^ "\n") ^
          ("Train branch pred.   : " ^ PolyML.makestring (!do_training) ^ "\n") ^
          ("Execute concretely   : " ^ PolyML.makestring (!do_conc_exec) ^ "\n") ^
          ("Run description text : " ^ PolyML.makestring descr_o ^ "\n") ^
	  ("Use angr symbolic execution : " ^ PolyML.makestring (!angr_symbexec) ^ "\n") ^
	  ("Patching : " ^ PolyML.makestring (!do_patching) ^ "\n");

        val _ = run_log config_str;
        val _ = min_verb 1 (fn () => print config_str);

        fun skipProgExText e = "Skipping program due to exception in pipleline:\n" ^ PolyML.makestring e ^ "\n***\n";
        
        fun main_loop 0 = ()
         |  main_loop n =
            (printv 1 ("Iteration: " ^ PolyML.makestring (m - n) ^ "\n");
             ((handle_locinfo print (fn () =>
              let val prog = prog_store_fun ()
              in
                scamv_test_main tests prog
                handle e => (run_log_prog (skipProgExText e); PolyML.Exception.reraise e)
              end))
              handle e as Thread.Interrupt => (
                        run_log "Keyboard interrupt!\n";
                        PolyML.Exception.reraise e)
                   | e => print (skipProgExText e));
             main_loop (n-1))
    in
        ((handle_locinfo print (fn () => main_loop m))
         handle _ => ()); run_finalize ()
    end;

fun scamv_run_with_opts () =
    let val cfg = scamv_getopt_config ();
    in
        scamv_run cfg
    end;

end;
