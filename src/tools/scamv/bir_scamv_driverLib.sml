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
    if is_comb exp then
        let val (con,args) = strip_comb exp
        in if con = ``BExp_Den`` then
               let val v = case strip_comb (hd args) of
                               (_,v::_) => v
                             | _ => raise ERR "bir_free_vars" "not expected"
               in [v]
               end
           else
               List.concat (map bir_free_vars args)
        end
    else [];

exception NoObsInPath;

(*
val exps = all_exps;
*)
fun make_word_relation relation exps =
    let
        fun primed_subst exp =
            map (fn v =>
                    let val vp = lift_string string_ty (fromHOLstring v ^ "'")
                    in ``BVar ^v`` |-> ``BVar ^vp`` end)
                (bir_free_vars exp);

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
        fun mk_distinct (a,b) =
            let val va = mk_var (a,``:word64``);
                val vb = mk_var (b,``:word64``);
            in
``(^va <> ^vb)``
            end;
        val distinct = if null pairs then raise NoObsInPath else list_mk_conj (map mk_distinct pairs);
    in
       ``^(bir2bool relation) /\ ^distinct``
    end

(* Prints a model, one variable per line. *)
fun print_model model =
    List.foldl
        (fn ((name, tm), _) =>
            (print (" - " ^ name ^ ": "); Hol_pp.print_term tm))
        () (rev model);

fun to_sml_Arbnums model =
    List.map (fn (name, tm) => (name, dest_word_literal tm)) model;

val (current_prog_id : string ref) = ref "";
val (current_prog : term option ref) = ref NONE;
val (current_pathstruct :
     (term * (term * term) list option) list ref) = ref [];
val (current_word_rel : term option ref) = ref NONE;
val (current_antecedents : term list ref) = ref [];

fun reset () =
    (current_prog_id := "";
     current_prog := NONE;
     current_pathstruct := [];
     current_word_rel := NONE;
     current_antecedents := [])

fun start_interactive prog =
    let
        val (prog_id, lifted_prog) = prog;
        val _ = current_prog_id := prog_id;
        val _ = current_prog := SOME lifted_prog;
(*        val _ = print_term lifted_prog; *)

        val lifted_prog_w_obs =
            bir_arm8_cache_line_tag_model.add_obs lifted_prog;
(*      val _ = print_term lifted_prog_w_obs; *)
        val (paths, all_exps) = symb_exec_phase lifted_prog_w_obs;
        
        fun has_observations (SOME []) = false
          | has_observations NONE = false
          | has_observations _ = true
        val _ =
            if exists (has_observations o snd) paths
            then () (* fine, there is at least one observation
                       in the pathstruct *)
            else raise ERR "start_interactive" "no observations";

        val _ = current_pathstruct := paths;
        val (conds, relation) = mkRel_conds paths;
        val _ = print_term relation;
        val _ = print ("Word relation\n");
        val word_relation = make_word_relation relation all_exps;
        val _ = current_word_rel := SOME word_relation;
        val _ = current_antecedents := List.map bir2bool conds;
    in paths end

fun next_test select_path =
    let
        val path = select_path (!current_antecedents);
        val _ = (print "Selecting path: "; print_term path);
        val rel = case !current_word_rel of
                    SOME x => x
                  | NONE => raise ERR "next_test" "no relation found";
        val word_relation = ``^rel /\ ^path``;
        
        val _ = print ("Calling Z3\n");
        val model = Z3_SAT_modelLib.Z3_GET_SAT_MODEL word_relation;
        val _ = (print "SAT model:\n"; print_model model(*; print "\n"*));

        val sml_model = to_sml_Arbnums model;
        fun isPrimedRun s = String.isSuffix "_" s;
        val (s2,s1) = List.partition (isPrimedRun o fst) sml_model;
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
        val _ = current_word_rel := SOME ``^rel /\ ~^(mk_var_mapping model)``;

(*        val _ = print_term (valOf (!current_word_rel)); *)

        val exp_id  =  bir_embexp_sates2_create ("arm8", "exp_cache_multiw", "obs_model_name_here") prog_id (s1, s2);
    in
        (if (#only_gen (scamv_getopt_config ()))
         then print ("Generated experiment: " ^ exp_id)
                    (* no need to do anything else *)
         else
             let val test_result = bir_embexp_run exp_id false;
             in case test_result of
		                (NONE, msg) => print ("result = NO RESULT (" ^ msg ^ ")")
		              | (SOME r, msg) => print ("result = " ^ (if r then "ok!" else "failed") ^ " (" ^ msg ^ ")")
             end); print "\n\n"
    end

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

fun scamv_test_main tests prog =
    let
        val _ = reset();
        val prog_obss_result = start_interactive prog;
        val round_robin = mk_round_robin (length (!current_antecedents) - 1);
        fun do_tests 0 = ()
          | do_tests n =
            let val _ = next_test round_robin
                        handle e =>
                               raise ERR "scamv_test_main" "next_test failed";
            in do_tests (n-1) end
    in do_tests tests
    end


fun scamv_test_gen_run tests (prog_id, lifted_prog) =
    let
        val lifted_prog_w_obs =
            bir_arm8_cache_line_tag_model.add_obs lifted_prog;
        val _ = print_term(lifted_prog_w_obs);
        val (paths, all_exps) = symb_exec_phase lifted_prog_w_obs;


        val relation = mkRel paths;
        val _ = print ("Word relation\n");
        val word_relation = make_word_relation relation all_exps;
        val _ = print_term(word_relation);
        val _ = print ("Calling Z3\n");

        val model = Z3_SAT_modelLib.Z3_GET_SAT_MODEL word_relation;
        val _ = (print "SAT model:\n"; print_model model(*; print "\n"*));

        val sml_model = to_sml_Arbnums model;
        fun isPrimedRun s = String.isSuffix "_" s;
        val (s2,s1) = List.partition (isPrimedRun o fst) sml_model;

        val exp_id  =  bir_embexp_sates2_create ("arm8", "exp_cache_multiw", "obs_model_name_here") prog_id (s1, s2);
        val test_result = bir_embexp_run exp_id false;

        val _ = case test_result of
		   (NONE, msg) => print ("result = NO RESULT (" ^ msg ^ ")")
		 | (SOME r, msg) => print ("result = " ^ (if r then "ok!" else "failed") ^ " (" ^ msg ^ ")");

        val _ = print ("\n\n");
    in
        test_result
    end

val scamv_test_mock = scamv_test_gen_run 1 o prog_gen_store_mock;

fun scamv_test_single_file filename =
    let val prog = prog_gen_store_fromfile filename ();
    in scamv_test_main 1 prog
    end;

fun show_error_no_free_vars (id,_) =
    print ("Program " ^ id ^ " skipped because it has no free variables.\n");

fun scamv_run { max_iter = m, prog_size = sz, max_tests = tests
              , generator = gen, only_gen = og } =
    let val is_mock = (gen = mock);
        val _ = bir_prog_gen_arm8_mock_set_wrap_around false;
        val _ = bir_prog_gen_arm8_mock_set [["b #0x80"]];

        val prog_store_fun =
            case gen of
                gen_rand => prog_gen_store_rand sz
              | rand_simple => prog_gen_store_rand_simple sz
              | qc => prog_gen_store_a_la_qc sz
              | slice => prog_gen_store_rand_slice sz
              | from_file filename => prog_gen_store_fromfile filename
              | mock => prog_gen_store_mock

        fun main_loop 0 = ()
         |  main_loop n =
            (print ("Iteration: " ^ PolyML.makestring (m - n) ^ "\n");
             (let val prog =
                      prog_store_fun ()
              in scamv_test_main tests prog end
              handle e =>
                     print("Skipping program due to exception in pipleline:\n" ^ PolyML.makestring e ^ "\n***\n"));
             main_loop (n-1))
    in
        main_loop m
    end;

fun scamv_run_with_opts () =
    let val cfg = scamv_getopt_config ();
    in
        scamv_run cfg
    end;

end;
