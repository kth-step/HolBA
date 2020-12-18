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
open bir_embexp_driverLib;
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

(* C like macros *)
val endif__ = (fn id => id);
fun ifdef__else__ x c c' e = (if x then c else c') |> e;
fun ifdef__ x c e = case x of true => c |> e;
fun force f = f ();

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

val (current_prog_id : string ref) = ref "";
val (current_prog : term option ref) = ref NONE;
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
    (current_prog_id := "";
     current_prog := NONE;
     current_prog_w_obs := NONE;
     current_prog_w_refined_obs := NONE;
     current_pathstruct := NONE;
     current_visited_map := init_visited ();
     current_full_specs := [];
     current_word_rel := NONE);

fun printv n str =
    if (#verbosity (scamv_getopt_config ()) >= n)
    then print str
    else ();

fun min_verb n f =
    if (#verbosity (scamv_getopt_config ()) >= n)
    then f ()
    else ();

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
    let val (prog_id, lifted_prog) = prog;
        val _ = current_prog_id := prog_id;
        val _ = current_prog := SOME lifted_prog;
        val _ = min_verb 2 (fn () => print_term lifted_prog);
    in
      (prog_id, lifted_prog)
    end;

fun scamv_phase_add_obs () =
let 
  val _ = printv 1 "Adding obs\n";
  val add_obs = #add_obs (get_obs_model (!current_obs_model_id));
  val mem_bounds =
      let
        open bir_embexp_driverLib;
        val (mem_base, mem_len) = bir_embexp_params_memory;
        val mem_end = (Arbnum.- (Arbnum.+ (mem_base, mem_len), Arbnum.fromInt 128));
      in
        pairSyntax.mk_pair
            (mk_wordi (bir_embexp_params_cacheable mem_base, 64),
             mk_wordi (bir_embexp_params_cacheable mem_end, 64))
      end;
  val lifted_prog_w_obs = add_obs mem_bounds (valOf (!current_prog));
  val _ = printv 1 "Obs added\n";
  val _ = current_prog_w_obs := SOME lifted_prog_w_obs;
  val _ = min_verb 3 (fn () => print_term lifted_prog_w_obs);
in
  lifted_prog_w_obs
end;

fun scamv_phase_symb_exec () =
    let
      val (paths, all_exps) = scamv_run_symb_exec (valOf (!current_prog_w_obs)) (SOME "*");
	    val _ = List.map (Option.map (List.map (fn (a,b,c) => print_term b)) o snd) paths;
      val ps = initialise paths;
      val _ = current_pathstruct := SOME ps;
      val _ = min_verb 4 (fn () => (print_path_struct ps; print (PolyML.makestring ps)));
    in
      ps
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

        val _ = scamv_set_prog_state prog;
        val _ = scamv_phase_add_obs ();
        val _ = scamv_phase_symb_exec ();

        val result = scamv_phase_rel_synth_init ();
    in result end;

fun all_obs_not_present { a_run = (_,a_obs), b_run = (_,b_obs) } =
    let fun check xs = all (fn (b,_) => b = false) xs;
    in check a_obs andalso check b_obs
    end;

(* This is used to build the next relation for path enumeration *)
fun mem_constraint [] = ``T``
  | mem_constraint mls =
    let fun is_addr_numeral tm = tm |> pairSyntax.dest_pair |> fst |> (fn x => (rhs o concl o EVAL) ``w2n ^x``) |> is_numeral
	fun adjust_prime s =
            if String.isSuffix "_" s
            then String.map (fn c => if c = #"_" then #"'" else c) s
            else s
	fun mk_cnst vname vls =
	    let
		val toIntls = (snd o finite_mapSyntax.strip_fupdate) vls
		val mem = mk_var (adjust_prime vname ,Type`:word64 |-> word8`)
		val memconstraint = map (fn p => let val (t1,t2) = pairSyntax.dest_pair p
						 in
						     ``^mem ' (^t1) = ^t2``
						 end) toIntls;
		val mc_conj = foldl (fn (a,b) => mk_conj (a,b)) (hd memconstraint) (tl memconstraint);
	    in
		(``~(^mc_conj)``, toIntls)
	    end

	val (hc, hv)::(tc, tv)::[] = (map (fn (vn, vl) =>  mk_cnst vn vl ) mls)
	val mc_conj = mk_conj ((if is_addr_numeral (hd hv) then hc else ``T``), (if is_addr_numeral (hd tv) then tc else ``T``))
    in
	mc_conj
    end

fun next_experiment all_exps next_relation  =
    let
        open bir_expLib;

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
        val _ = min_verb 1 (fn () =>
                               (print "Selected path: ";
                                print (PolyML.makestring path_spec);
                                print "\n"));

        val _ = min_verb 3 (fn () =>
                               bir_exp_pretty_print rel);
        val _ = printv 4 ("Word relation\n");
        val new_word_relation = make_word_relation rel;
        val _ = min_verb 4 (fn () =>
                               (print_term new_word_relation;
                                print "\n"));
(*        val word_relation =
            case !current_word_rel of
                NONE => new_word_relation
	      (* r is a constraint used to build the next relation for path enumeration *)
              | SOME r => mk_conj (new_word_relation, r); *)
        val word_relation = mk_conj(new_word_relation, lookup_visited (!current_visited_map) path_spec)
                            handle NotFound => new_word_relation;

        val _ = printv 2 ("Calling Z3\n");
        val model = Z3_SAT_modelLib.Z3_GET_SAT_MODEL word_relation;
        val _ = min_verb 1 (fn () => (print "SAT model:\n"; print_model model; print "\nSAT model finished.\n"));

	      val (ml, regs) = List.partition (fn el =>  (String.isSubstring (#1 el) "MEM_")) model
	      val (primed, nprimed) = List.partition (isPrimedRun o fst) model
	      val rmprime = List.map (fn (r,v) => (remove_prime r,v)) primed
        val s1 = to_sml_Arbnums nprimed;
	      val s2 = to_sml_Arbnums primed;
        val prog_id = !current_prog_id;

        fun mk_var_mapping s =
            let fun mk_eq (a,b) =
                    let fun adjust_prime s =
                            if String.isSuffix "_" s
                            then String.map (fn c => if c = #"_" then #"'" else c) s
                            else s;
                        val va = mk_var (adjust_prime a,``:word64``);
                    in ``^va = ^b``
                    end;
            in list_mk_conj (map mk_eq s) end;

        val reg_constraint = ``~^(mk_var_mapping (regs))``;
	      val mem_constraint = mem_constraint ml;
	      val new_constraint = mk_conj (reg_constraint, mem_constraint);

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
        val st =
            if !do_training
            then
              compute_training_state (!current_full_specs)
                                     (!current_obs_projection)
                                     (lookup_visited (!current_visited_map) path_spec)
                                     (fst (#a_run path_spec))
                                     paths
            else
              machstate_empty;
	(* ------------------------- training end ------------------------- *)
	(* val _ = print_term (valOf (!current_word_rel)); *)

        (* clean up s2 *)
	val s2 = to_sml_Arbnums rmprime

        (* check with concrete-symbolic execution whether the observations are actually equivalent *)
        val lifted_prog_w_obs = case !current_prog_w_obs of
				    SOME x => x
				  | NONE => raise ERR "next_test" "no program found";

	(* remove meory for now from states*)
	val ce_obs_comp = conc_exec_obs_compare (!current_obs_projection) lifted_prog_w_obs (s1, s2)
        val _ = if #1 ce_obs_comp then () else
                  raise ERR "next_experiment" "Experiment does not yield equal observations, won't generate an experiment.";
	val s1::s2::_ = #2 ce_obs_comp

        (* create experiment files *)
        val exp_id  = bir_embexp_states2_create ("arm8", !hw_obs_model_id, !current_obs_model_id) prog_id (s1, s2, SOME st);
        val exp_gen_message = "Generated experiment: " ^ exp_id;
        val _ = bir_embexp_log_prog exp_gen_message;

(*
        val _ =  (if (#only_gen (scamv_getopt_config ())) then
                    printv 1 exp_gen_message
                    (* no need to do anything else *)
                  else (
                    let val test_result = bir_embexp_run exp_id false;
                    in case test_result of
                          (NONE, msg) => printv 1 ("result = NO RESULT (" ^ msg ^ ")")
                        | (SOME r, msg) => printv 1 ("result = " ^ (if r then "ok!" else "failed") ^ " (" ^ msg ^ ")")
                    end);
                 printv 1 "\n\n");
*)
    in ()
    end;

fun scamv_test_main tests prog =
    let
        val _ = reset();
        val (full_specs, validity, next_relation) = scamv_per_program_init prog;
        val _ = current_full_specs := full_specs;
        fun do_tests 0 =  (current_word_rel := NONE; current_full_specs := []; current_visited_map := init_visited ())
          | do_tests n =
            let val _ = next_experiment [] next_relation
                        handle e => (
                               let
                                 val message = "Skipping test case due to exception in pipleline:\n" ^ PolyML.makestring e ^ "\n***\n";
                               in
                                 bir_embexp_log_prog message;
                                 print message
                               end
                        )
            in do_tests (n-1) end
    in do_tests tests
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
      | from_listfile => (case generator_param of
              SOME x => prog_gen_store_listfile x
            | NONE   => raise ERR "match_prog_gen::from_file" "listfile needs to be specified as generator_param")
      | prefetch_strides => prog_gen_store_prefetch_stride sz
      | _ => raise ERR "match_prog_gen" ("unknown generator type: " ^ (PolyML.makestring gen));

fun match_obs_model obs_model =
    case obs_model of
        mem_address_pc =>
        "mem_address_pc"
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
              , verbosity = verb, seed_rand = seed_rand, do_training = train } =
    let

        val _ = bir_randLib.rand_isfresh_set seed_rand;

        val _ = do_enum := enumerate;
        val _ = do_training := train;
        val _ = current_obs_projection := proj;
        
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
          ("Train branch pred.   : " ^ PolyML.makestring (!do_training) ^ "\n");

        val _ = bir_embexp_log config_str;
        val _ = min_verb 1 (fn () => print config_str);

        fun skipProgExText e = "Skipping program due to exception in pipleline:\n" ^ PolyML.makestring e ^ "\n***\n";
        
        fun main_loop 0 = ()
         |  main_loop n =
            (printv 1 ("Iteration: " ^ PolyML.makestring (m - n) ^ "\n");
             (let val prog = prog_store_fun ()
              in
                scamv_test_main tests prog
                handle e => (bir_embexp_log_prog (skipProgExText e); raise e)
              end
              handle e => print (skipProgExText e));
             main_loop (n-1))
    in
        (main_loop m
         handle _ => ()); bir_embexp_finalize ()
    end;

fun scamv_run_with_opts () =
    let val cfg = scamv_getopt_config ();
    in
        scamv_run cfg
    end;

end;
