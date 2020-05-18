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
open scamv_configLib;
open bir_conc_execLib;

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

fun symb_exec_phase prog =
    let
        (* leaf list *)
        val maxdepth = 5 * length (fst (dest_list (dest_BirProgram prog))) (* (~1); *)
        val precond = ``bir_exp_true``
        val leafs = symb_exec_process_to_leafs_nosmt maxdepth precond prog;

        (* retrieval of path condition and observation expressions *)
	fun extract_cond_obs s =
	  let
	    val (_,_,cond,_,obs) = dest_bir_symb_state s;
	    val obss = ((List.map dest_bir_symb_obs) o fst o dest_list) obs;

	    (* determine whether this is an error state *)
	    val isErrorState = not (symb_is_BST_Halted s);

	    (* this converts BIR consts to HOL4 variables *)
	    val obs_list = List.map (fn (ec,eo, obsf) =>
		   (bir_exp_hvar_to_bvar ec, bir_exp_hvar_to_bvar eo, obsf)) obss;

	    (* we require singleton lists for the observations at the moment *)
	    (* check that we have HD as observation function, and apply it *)
	    val obs_list' = List.map (fn (ec,eo,obsf) =>
		     let
		       val (otl,_) = dest_list eo;
		       val _ = (if listSyntax.is_hd ``^obsf x`` then () else raise ERR "" "")
			       handle _ =>
				 raise ERR "extract_cond_obs" ("currently we only support HD as observation function, not \"" ^ (term_to_string obsf) ^ "\"");
		     in
		       if length otl <> 1 then
			 raise ERR "extract_cond_obs" "currently we support only singleton observations"
		       else
			 (ec, hd otl)
		     end
		   ) obs_list;
	  in
	    (bir_exp_hvar_to_bvar cond, if isErrorState then NONE else SOME obs_list')
	  end;

        val paths = List.map extract_cond_obs leafs;

        (* we also need all generated expressions to collect the variables *)
        val path_conds = List.map fst paths;
        val obs_exps = flatten (List.map (fn (x,y) => [x,y])
                          (flatten (List.map ((fn x =>
                             case x of NONE => [] 
                                     | SOME y => y) o snd) paths)));
        val all_exps = (path_conds @ obs_exps);
    in
        (paths, all_exps)
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
		       List.concat (map bir_free_vars args)
		end
	    else []
    in
	fvs
    end;

exception NoObsInPath;

fun n_times 0 f x = x | n_times n f x = n_times (n-1) f (f x);
fun dest_mem_load size tm =
    if size = 7 
    then tm |> (finite_mapSyntax.dest_fapply  o  (n_times  7 (#2 o dest_word_concat))) 
    else tm |> (#1 o dest_word_lsr o #1 o dest_w2w)
	    |> (finite_mapSyntax.dest_fapply o (n_times size (#2 o dest_word_concat)));


fun make_word_relation relation exps =
    let
        fun primed_subst exp =
            map (fn v =>
                    let val vp = lift_string string_ty (fromHOLstring v ^ "'")
                    in ``BVar ^v`` |-> ``BVar ^vp`` end)
                (bir_free_vars exp)

        fun primed_vars exp = map (#residue) (primed_subst exp);
        fun nub [] = []
          | nub (x::xs) = x::nub(List.filter (fn y => y <> x) xs);
        val primed = sort (curry String.<=)
                     (map (fromHOLstring o snd o dest_comb)
                         (nub (flatten (map primed_vars exps))));
        val unprimed = sort (curry String.<=)
                       (nub (map fromHOLstring
                            (flatten (map bir_free_vars exps))));

        val pairs = zip unprimed primed;
	val (mpair, rpair) = List.partition (fn el =>  (String.isSubstring (#1 el) "MEM")) pairs

        fun mk_distinct_reg (a,b) =
            let val va = mk_var (a,``:word64``);
                val vb = mk_var (b,``:word64``);
            in
		``(^va <> ^vb)``
            end;
	val rel2w = (bir2bool relation)

	fun mk_distinct_mem (a, b) rel = 
	    let 
		open finite_mapSyntax
		val va = mk_var (a, ``:word64 |-> word8``)
		val vb = mk_var (b, ``:word64 |-> word8``)
		fun split_mem  tms m = filter (fn tm => (#1 (dest_fapply(find_term is_fapply tm)) = m)) tms
		fun extract_mem_load n rel = ((nub o find_terms (can (dest_mem_load n))) rel);
		val memop  = (extract_mem_load 7 rel)@(extract_mem_load 3 rel)@(extract_mem_load 1 rel)@(extract_mem_load 0 rel)
		val m1 = zip (split_mem  memop va) (split_mem memop vb)
		val res = if List.null m1 then T else list_mk_disj (map (fn (tm, tm') => ``^tm <> ^tm'`` ) m1)
	    in 
		res
	    end;

        val distinct = if null pairs 
		       then raise NoObsInPath 
		       else (* if List.null mpair *)
		       (* then *) list_mk_disj (map mk_distinct_reg rpair)
		       (* else mk_conj (list_mk_disj ((map mk_distinct_reg rpair)), (mk_distinct_mem (hd mpair) rel2w)) *)
    in
       ``^rel2w /\ ^distinct``
    end

(* Prints a model, one variable per line. *)
fun print_model model =
    List.foldl
        (fn ((name, tm), _) =>
            (print (" - " ^ name ^ ": "); Hol_pp.print_term tm))
        () (rev model);

fun to_sml_Arbnums model =
    List.map (fn (name, tm) => 
        if finite_mapSyntax.is_fupdate tm
	then
	    let val vlsW = (snd o finite_mapSyntax.strip_fupdate) tm
		val vlsN = map (fn p =>
				   let
				       val (ad, vl) = pairSyntax.dest_pair p
				   in
				       (dest_word_literal ad, dest_word_literal vl)
				       handle _ => (Arbnum.fromInt 969696, dest_word_literal vl)
				   end) vlsW
	    in
		memT(name, vlsN)
	    end
	else
	    regT(name, dest_word_literal tm)) model;


val hw_obs_model_id = ref "";
val do_enum = ref false;

val (current_prog_id : string ref) = ref "";
val (current_prog : term option ref) = ref NONE;
val (current_prog_w_obs : term option ref) = ref NONE;
val (current_obs_model_id : string ref) = ref "";
val (current_pathstruct :
     path_struct ref) = ref [];
val (current_word_rel : term option ref) = ref NONE;

fun reset () =
    (current_prog_id := "";
     current_prog := NONE;
     current_prog_w_obs := NONE;
     current_pathstruct := [];
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

fun extract_obs_variables ps =
    List.concat (
        List.map (fn (_,obs_list) =>
                     case obs_list of
                         NONE => []
                       | SOME list => 
                         List.concat (List.map (fn (_,term) => bir_free_vars term) list))
                ps);

fun enumerate_line_single_input path_struct =
    let val vars = extract_obs_variables path_struct
    in
        case vars of
            [] => []
          | (v::vs) => [(observe_line (bden (bvarimm64 (fromHOLstring v))), bir_rel_synthLib.enum_range (0,60))]
    end;

fun default_enumeration_targets paths =
    if !do_enum
    then enumerate_line_single_input paths
    else [];

fun start_interactive prog =
    let
        val _ = reset ();

        val (prog_id, lifted_prog) = prog;
        val _ = current_prog_id := prog_id;
        val _ = current_prog := SOME lifted_prog;
        val _ = min_verb 2 (fn () => print_term lifted_prog);

        val add_obs = #add_obs (get_obs_model (!current_obs_model_id))

        val lifted_prog_w_obs = add_obs lifted_prog;
        val _ = current_prog_w_obs := SOME lifted_prog_w_obs;
        val _ = min_verb 3 (fn () => print_term lifted_prog_w_obs);
        val (paths, all_exps) = symb_exec_phase lifted_prog_w_obs;
	(* val _ = List.map (Option.map (List.map (print_term o fst)) o snd) paths; *)
        
        fun has_observations (SOME []) = false
          | has_observations NONE = false
          | has_observations _ = true
        val _ =
            if exists (has_observations o snd) paths
            then () (* fine, there is at least one observation
                       in the paths list *)
            else raise ERR "start_interactive" "no observations";

        val enum_env = default_enumeration_targets paths;
        val (path_struct, validity, next_relation) =
            rel_synth_init paths enum_env; (* TODO consider validity *)
        val _ = current_pathstruct := path_struct;
        val _ = min_verb 4 (fn () => print_path_struct path_struct);
    in (path_struct, all_exps, next_relation) end;


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

val getReg = (fn tm => case tm of regT x => x)
val getMem = (fn tm => case tm of memT x => x) 
val is_memT= (fn tm => can getMem tm)
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
            valOf (next_relation guard_path_spec)
            handle Option =>
                   raise ERR "next_experiment" "next_relation returned a NONE";
        
        val _ = min_verb 3 (fn () =>
                               (print "Selected path: ";
                                print (PolyML.makestring path_spec);
                                print "\n"));

        val _ = min_verb 3 (fn () =>
                               bir_exp_pretty_print rel);
        val _ = printv 4 ("Word relation\n");
        val new_word_relation = make_word_relation rel all_exps;
        val _ = min_verb 3 (fn () =>
                               (print_term new_word_relation;
                                print "\n"));
        val word_relation =
            case !current_word_rel of
                NONE => new_word_relation
	      (* r is a constraint used to build the next relation for path enumeration *)
              | SOME r => mk_conj (new_word_relation, r);

        val _ = printv 1 ("Calling Z3\n");
        val model = Z3_SAT_modelLib.Z3_GET_SAT_MODEL word_relation;
        val _ = min_verb 1 (fn () => (print "SAT model:\n"; print_model model(*; print "\n"*)));
        val _ = printv 1 ("Printed model\n");
	(*Need to be removed later. It is just for experimental reasone*)

        fun remove_prime str =
          if String.isSuffix "_" str then
            (String.extract(str, 0, SOME((String.size str) - 1)))
          else
            raise ERR "remove_prime" "there was no prime where there should be one";

	fun isPrimedRun s = String.isSuffix "_" s;
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
	val new_constraint = mk_conj (reg_constraint, mem_constraint)

        val _ =
            current_word_rel :=
            (case !current_word_rel of
                 NONE => SOME new_constraint
               | SOME cumulative =>
                 SOME ``^cumulative /\ ^new_constraint``);

	(* val _ = print_term (valOf (!current_word_rel)); *)

        (* clean up s2 *)
	val s2 = to_sml_Arbnums rmprime

        (* check with concrete-symbolic execution whether the observations are actually equivalent *)
        val lifted_prog_w_obs = case !current_prog_w_obs of
				    SOME x => x
				  | NONE => raise ERR "next_test" "no program found";

	(* remove meory for now from states*)
	val is_state_mem_emp = (fn s => getMem(filter is_memT s |> hd) |> #2 |> List.null)
	val ce_obs_comp = conc_exec_obs_compare lifted_prog_w_obs (s1, s2)
        val _ = if #1 ce_obs_comp then () else
                  raise ERR "next_experiment" "Experiment does not yield equal observations, won't generate an experiment.";
	val (s1, s2) = if not (#2 ce_obs_comp |> hd |> is_state_mem_emp)
		       then let val s1'::s2'::_ = #2 ce_obs_comp in (s1',s2') end
		       else (s1,s2)

        (* create experiment files *)
        val exp_id  = bir_embexp_sates2_create ("arm8", !hw_obs_model_id, !current_obs_model_id) prog_id (s1, s2);
        val exp_gen_message = "Generated experiment: " ^ exp_id;
        val _ = bir_embexp_log_prog exp_gen_message;

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
    in ()
    end;

fun mk_round_robin n =
    let val counter = ref 0;
    in fn (ys : term list) =>
          let val c = !counter;
          in
              (if c = n
               then counter := 0
               else counter := c + 1) ;
              List.nth (ys, c)
          end
    end

fun mk_round_robin_every s n =
    let val counter = ref n;
        val step = ref 0;
    in fn (ys : term list) =>
          let val c = !counter;
          in
              (if c = n
               then (counter := 0; step := 0)
               else (if (!step = s)
                     then (counter := c + 1;
                           step := 0)
                     else (step := !step + 1));
               printv 1 ("Path counter: " ^ PolyML.makestring (!counter) ^ "\n");
               List.nth (ys, c))
          end
    end

fun scamv_test_main tests prog =
    let
        val _ = reset();
        val (path_structure, all_exps, next_relation) = start_interactive prog;
        fun do_tests 0 = ()
          | do_tests n =
            let val _ = next_experiment all_exps next_relation
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


fun scamv_test_gen_run tests (prog_id, lifted_prog) =
    (raise ERR "scamv_test_gen_run" "function DEPRECATED and will be removed soon - use scamv_run with from_file generator instead"; (NONE, "DEPRECATED"));


fun scamv_test_single_file filename =
    let val prog = prog_gen_store_fromfile filename ();
    in scamv_test_main 1 prog
    end;

fun show_error_no_free_vars (id,_) =
    print ("Program " ^ id ^ " skipped because it has no free variables.\n");

fun scamv_run { max_iter = m, prog_size = sz, max_tests = tests, enumerate = enumerate
              , generator = gen, generator_param = generator_param
              , obs_model = obs_model, hw_obs_model = hw_obs_model
              , verbosity = verb, only_gen = og, seed_rand = seed_rand } =
    let

        val _ = bir_scamv_helpersLib.rand_isfresh_set seed_rand;

        val _ = do_enum := enumerate;

        val prog_store_fun =
           case gen of
                gen_rand => (case generator_param of
                                 SOME x => prog_gen_store_rand x  sz
                               | NONE   => prog_gen_store_rand "" sz)
              | qc => (case generator_param of
                                 SOME x => prog_gen_store_a_la_qc x sz
                               | NONE   => raise ERR "scamv_run::qc" "qc type needs to be specified as generator_param")
              | slice => prog_gen_store_rand_slice sz
              | from_file => (case generator_param of
                                 SOME x => prog_gen_store_fromfile x
                               | NONE   => raise ERR "scamv_run::from_file" "file needs to be specified as generator_param")
              | prefetch_strides => prog_gen_store_prefetch_stride sz
	      | spectre => prog_gen_rand_spectre sz
              | _ => raise ERR "scamv_run" ("unknown generator type " ^ PolyML.makestring gen)

        val _ =
           case obs_model of
	       (*  mem_address_pc_trace => *)
	      (* 	      current_obs_model_id := "mem_address_pc_trace" *)
              (* | *) cache_tag_index  =>
                      current_obs_model_id := "cache_tag_index"
              | cache_tag_only =>
                      current_obs_model_id := "cache_tag_only"
              | cache_index_only =>
                      current_obs_model_id := "cache_index_only"
              | cache_tag_index_part =>
                      current_obs_model_id := "cache_tag_index_part"
              | cache_tag_index_part_page =>
                      current_obs_model_id := "cache_tag_index_part_page"
              | _ => raise ERR "scamv_run" ("unknown obs_model " ^ PolyML.makestring obs_model);

        val _ =
           case hw_obs_model of
                hw_cache_tag_index  =>
                      hw_obs_model_id := "cache_multiw"
              | hw_cache_index_numvalid =>
                      hw_obs_model_id := "cache_multiw_numinset"
              | hw_cache_tag_index_part =>
                      hw_obs_model_id := "cache_multiw_subset"
              | hw_cache_tag_index_part_page =>
                      hw_obs_model_id := "cache_multiw_subset_page_boundary"
              | _ => raise ERR "scamv_run" ("unknown hw_obs_model " ^ PolyML.makestring hw_obs_model);

        val config_str =
          "Scam-V set to the following test params:\n" ^
          ("Program generator    : " ^ PolyML.makestring gen ^ "\n") ^
          ("Prog gen params      : " ^ PolyML.makestring generator_param ^ "\n") ^
          ("Observation model    : " ^ !current_obs_model_id ^ "\n") ^
          ("HW observation model : " ^ !hw_obs_model_id ^ "\n") ^
          ("Enumerate            : " ^ PolyML.makestring (!do_enum) ^ "\n");

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
