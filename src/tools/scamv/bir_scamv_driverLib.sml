structure bir_scamv_driverLib :> bir_scamv_driverLib =
struct

open HolKernel boolLib liteLib simpLib Parse bossLib;
open bir_prog_genLib;
open bir_inst_liftingLib;
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
open gcc_supportLib;
open bir_gccLib;
open bir_typing_expTheory;

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


(* Load the dependencies in interactive sessions *)
val _ = if !Globals.interactive then (
            load "../Z3_SAT_modelLib"; (* ../ *)
            load "../bir_exp_to_wordsLib"; (* ../ *)
            ()) else ();

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = Globals.show_tags := true;


(* for arm8 *)
val (bmil_bir_lift_prog_gen, disassemble_fun) = (bmil_arm8.bir_lift_prog_gen, arm8AssemblerLib.arm8_disassemble);

(* this was copied -----> *)
fun disassembly_section_to_minmax section =
    case section of
        BILMR(addr_start, entries) =>
        let
            val data_strs = List.map fst entries;
	          (* val _ = List.map (fn x => print (x ^ "\r\n")) data_strs; *)
            val lengths_st = List.map String.size data_strs;
            val _ = List.map (fn x => ()) lengths_st;
            val lengths = List.map (fn x => Arbnum.fromInt (x div 2)) lengths_st;
            val length = List.foldr (Arbnum.+) Arbnum.zero lengths;
        in
            (addr_start, Arbnum.+(addr_start, length))
        end;

fun minmax_fromlist ls = List.foldl (fn ((min_1,max_1),(min_2,max_2)) =>
                                        ((if Arbnum.<(min_1, min_2) then min_1 else min_2),
                                         (if Arbnum.>(max_1, max_2) then max_1 else max_2))
                                    ) (hd ls) (tl ls);

fun da_sections_minmax sections = minmax_fromlist (List.map disassembly_section_to_minmax sections);
(* <---- this was copied *)

fun lift_program_from_sections sections =
    let
        val prog_range = da_sections_minmax sections;
        val (thm_prog, errors) = bmil_bir_lift_prog_gen prog_range sections;
        val lifted_prog = (snd o dest_comb o concl) thm_prog;
        val lifted_prog_typed =
            inst [Type`:'observation_type` |-> Type`:bir_val_t`]
                 lifted_prog;
    in
        lifted_prog_typed
    end

fun process_asm_code asm_code =
    let
        val da_file = bir_gcc_assembe_disassemble asm_code "./tempdir"

        val (region_map, sections) = read_disassembly_file_regions da_file;
    in
        (asm_code, sections)
    end

fun prog_gen_from_file s_file =
    let
        val file = TextIO.openIn s_file;
        val s    = TextIO.inputAll file before TextIO.closeIn file;

        val asm_code = s; 
    in
        process_asm_code asm_code
    end

fun prog_gen_mock () =
    let
        val asm_code = bir_prog_gen_asm_lines_to_code (bir_prog_gen_arm8_mock ())
    in
        process_asm_code asm_code
    end

fun symb_exec_phase prog =
    let
        (* leaf list *)
        val maxdepth = (~1);
        val precond = ``bir_exp_true``
        val leafs = symb_exec_process_to_leafs_nosmt maxdepth precond prog;

        (* retrieval of path condition and observation expressions *)
	fun extract_cond_obs s =
	  let
	    val (_,_,cond,_,obs) = dest_bir_symb_state s;
	    val obss = ((List.map dest_bir_symb_obs) o fst o dest_list) obs;

	    (* determine whether this is an error state *)
	    val isErrorState = symb_is_BST_AssertionViolated s;

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

(*
val exps = all_exps;
*)
fun make_word_relation relation exps =
    let
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
``(^va <> ^vb)  /\ (^va < 0x80042FF8w) /\ (^vb < 0x80042FF8w)``
            end;
        val distinct = list_mk_conj (map mk_distinct pairs);
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

val (current_asm : string ref) = ref "";
val (current_prog : term option ref) = ref NONE;
val (current_pathstruct :
     (term * (term * term) list option) list ref) = ref [];
val (current_word_rel : term option ref) = ref NONE;
val (current_antecedents : term list ref) = ref [];

fun reset () =
    (current_asm := "";
     current_prog := NONE;
     current_pathstruct := [];
     current_word_rel := NONE;
     current_antecedents := [])

fun start_interactive prog =
    let
        val (asm_file_contents, sections) = prog;
        val _ = current_asm := asm_file_contents;
        val lifted_prog = lift_program_from_sections sections;
        val _ = current_prog := SOME lifted_prog;

        val lifted_prog_w_obs =
            bir_arm8_cache_line_tag_model.add_obs lifted_prog;
        val (paths, all_exps) = symb_exec_phase lifted_prog_w_obs;

        val _ = current_pathstruct := paths;
        val (conds, relation) = mkRel_conds paths;
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
        val asm_file_contents = !current_asm;

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

        val _ = print_term (valOf (!current_word_rel));
        
        val exp_path = bir_embexp_create ("obs_model_name_here", ("arm8", "exp_cache_multiw")) asm_file_contents (s1, s2);
        val test_result = bir_embexp_run exp_path false;

        val _ = case test_result of
		   (NONE, msg) => print ("result = NO RESULT (" ^ msg ^ ")")
		 | (SOME r, msg) => print ("result = " ^ (if r then "ok!" else "failed") ^ " (" ^ msg ^ ")");

        val _ = print ("\n\n");
    in
        test_result
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
                               (NONE, "next_test failed"); 
            in do_tests (n-1) end
    in do_tests tests
    end


fun scamv_test_gen_run tests (asm_code, sections) =
    let
        val lifted_prog = lift_program_from_sections sections;
        val lifted_prog_w_obs =
            bir_arm8_cache_line_model.add_obs lifted_prog;
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

        val exp_path = bir_embexp_create ("obs_model_name_here", ("arm8", "exp_cache_multiw")) asm_code (s1, s2);
        val test_result = bir_embexp_run exp_path false;

        val _ = case test_result of
		   (NONE, msg) => print ("result = NO RESULT (" ^ msg ^ ")")
		 | (SOME r, msg) => print ("result = " ^ (if r then "ok!" else "failed") ^ " (" ^ msg ^ ")");

        val _ = print ("\n\n");
    in
        test_result
    end

val scamv_test_mock = scamv_test_gen_run 1 o prog_gen_mock;
val scamv_test_asmf = scamv_test_gen_run 1 o prog_gen_from_file;

type scamv_config = { max_iter : int, prog_size : int, max_tests : int }

fun scamv_run { max_iter = m, prog_size = sz, max_tests = tests } =
    let val is_mock = true;

        val _ = bir_prog_gen_arm8_mock_set_wrap_around true;

        fun prog_gen_fun () =
          if is_mock then
            bir_prog_gen_arm8_mock ()
          else
            bir_prog_gen_arm8_rand sz;
        
        fun main_loop 0 = ()
         |  main_loop n =
            let val prog =
                    process_asm_code (bir_prog_gen_asm_lines_to_code (prog_gen_fun ()))
            in scamv_test_main tests prog; main_loop (n-1) end
    in
        main_loop m
    end;

end;
