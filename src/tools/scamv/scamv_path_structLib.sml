structure scamv_path_structLib : scamv_path_structLib =
struct

open HolKernel Parse liteLib boolLib bossLib;
open stringSyntax;
open bslSyntax;
open numSyntax;
open bir_utilLib;

open bir_programTheory;

(* error handling *)
val libname  = "bir_rel_synthLib"
val ERR      = Feedback.mk_HOL_ERR libname
val wrap_exn = Feedback.wrap_exn libname


datatype cobs_repr = cobs of int * term * term * term;
datatype path_repr = path of int * term * (cobs_repr list);
type path_struct = path_repr list;

type path_spec = {a_run: int * (bool * int) list, b_run: int * (bool * int) list};

fun path_id_of (path (id, _, _)) = id;
fun path_cond_of (path (_,cond,_)) = cond;
fun path_obs_of (path (_,_,obs)) = obs;
fun cobs_id_of (cobs (id,_,_,_)) = id;

fun path_domain (ps : path_struct) =
    List.map path_id_of ps;

fun num_paths (ps : path_struct) = length (path_domain ps);

fun obs_domain_path xs =
    List.map cobs_id_of xs;

fun obs_domain (ps : path_struct) =
    List.concat (List.map (obs_domain_path o path_obs_of) ps);

fun gen_obs_ids fresh ts =
    List.map (fn (oid, c,t) => cobs (fresh (), oid, c, t)) ts;

fun gen_path_ids fresh ps =
    List.map (fn (pcond, cobslist) =>
                 path (fresh (), pcond, gen_obs_ids fresh cobslist)) ps;

fun lookup_path path_id path_struct =
    List.find (fn p => path_id_of p = path_id) path_struct;

fun lookup_spec path1 path2 path_specs =
    List.find
        (fn sp => fst (#a_run sp) = path1 andalso fst (#b_run sp) = path2)
        path_specs;

fun lookup_obs obs_id obs_list =
    List.find (fn obs => cobs_id_of obs = obs_id) obs_list;

val fresh_id =
    stateful_tabulate
        (fn n =>
            let fun onechar n =
                    (Char.chr (Char.ord (#"A") + (n mod 26)));
                fun c m =
                    if m < 26
                    then [onechar m]
                    else #"Z" :: (String.explode (Int.toString (n-25)));
            in
              String.implode (c n)
            end);

fun mk_fresh_gen () =
    stateful_tabulate (fn n => n);

(* input: (bir_exp * (cobs list) option) list *)
fun initialise ps : path_struct =
    let
	    val (somes, nones) = partition (is_some o snd) ps;
      val ps' = List.map (fn (p,ob) => (p, Option.getOpt (ob,[]))) somes;
      fun smart_bandl xs = if null xs then btrue else bandl xs;
(*      val negCond = smart_bandl o List.map (bnot o fst);
      val validity = negCond nones; *)
      val fresh = mk_fresh_gen ();
      fun has_observations (SOME []) = false
        | has_observations NONE = false
        | has_observations _ = true
      val _ =
          if exists (has_observations o snd) ps
          then () (* fine, there is at least one observation
                       in the paths list *)
          else raise ERR "scamv_path_structLib.initialise" "no observations";

    in (gen_path_ids fresh ps') (*, band (validity, primed_term validity)) *)
    end;

fun filter pred ps =
    let fun check p =
            pred (path_id_of p, path_cond_of p)
    in
      List.filter check ps
    end;

fun get_distinct_path path_id ps =
    filter (fn (id,_) => not (id = path_id)) ps;

fun filter_feasible_naive_paths ps =
    let
      val debug_z3_taut_on = false;
      fun z3_is_taut wtm =
	  let val wtm_fixed = subst [mk_var ("MEM", ``:word64|->word8``) |-> Term`MEMV:word64|->word8`] wtm; in
	      ((HolSmtLib.Z3_ORACLE_PROVE wtm_fixed; true)
	       handle HOL_ERR e => (
		      if not debug_z3_taut_on then () else
		      let
			val _ = print "--- not a tautology:\n";
			val _ = print_term wtm_fixed;
			val _ = print ">>> generating a model\n";
			val model = Z3_SAT_modelLib.Z3_GET_SAT_MODEL (mk_neg wtm_fixed);
			(*val _ = PolyML.print model;*)
			val _ = print "<<< done generating a model\n";
		      in () end;
		      false))
	  end;

	fun check_path_infeasability p =
	    let
	      val path_cond = path_cond_of p;
	      val wtm = bir_exp_to_wordsLib.bir2bool path_cond;
	    in
	      z3_is_taut (mk_neg wtm)
	    end
    in
      List.filter (not o (fn p => check_path_infeasability p)) ps
    end;

fun extract_obs_variables ps =
    List.concat (
      List.map (fn (path (_,_,obs_list)) =>
                    List.concat (List.map (fn (cobs (_,_,_,term)) => bir_free_vars term) obs_list))
               ps);

fun print_path_struct path_struct =
    let fun print_obs (cobs (id, oid, obs_cond, obs_term)) =
            (print ("Obs " ^ PolyML.makestring id
                    ^ ": (model " ^ PolyML.makestring (int_of_term oid) ^ ") ");
             print_term obs_cond;
             print (" => ");
             print_term obs_term;
             print "\n");
        fun print_path (path (id, path_cond, obs_list)) =
            (print ("Path " ^ PolyML.makestring id ^ ": ");
             print_term path_cond;
             print (" =>\n");
             List.app print_obs obs_list);
    in List.app print_path path_struct
    end;

end

