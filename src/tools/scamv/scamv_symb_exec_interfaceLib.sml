structure scamv_symb_exec_interfaceLib :> scamv_symb_exec_interfaceLib =
struct

local
  open HolKernel boolLib Parse;
  open bir_symb_execLib;
  open bir_symb_masterLib;
  open listSyntax;
  open bslSyntax;
  open bir_programSyntax;
  
  (* error handling *)
  val libname  = "scamv_symb_exec_interfaceLib"
  val ERR      = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname

fun do_symb_exec prog =
    let
        (* leaf list *)
        val maxdepth = 5 * length (fst (dest_list (dest_BirProgram prog))) (* (~1); *)
        val precond = ``bir_exp_true``
        val leafs = symb_exec_process_to_leafs_nosmt maxdepth precond prog;

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

	    (* we forward the observations as list of expressions with observation function for handling their corresponding values, which is assumed to be reducable with EVAL to conjunctions of equality of word expressions *)
	    val obs_list' = List.map (fn (oid,ec,eo,obsf) =>
		     let
		       val (otl,_) = dest_list eo;
		     in
                       (oid, ec, otl, obsf)
		     end
		   ) obs_list;
	  in
	    (bir_exp_hvar_to_bvar cond, if isErrorState then NONE else SOME obs_list')
	  end;

        val paths = List.map extract_cond_obs leafs;

        fun print_symbobs NONE = print "ERROR STATE"
	  | print_symbobs (SOME ol) = (
                print "obss:";
                List.map (fn (oid, ec, otl, obsf) => (
                    print "- (";
                    print_term oid;
                    print ", ";
                    print_term ec;
                    print ", [";
                    List.map (fn ot => (print_term ot; print "; ")) otl;
                    print "], ";
                    print_term obsf;
                    print ")"
                  )) ol; ()
              );
        val _ = if true then () else (
            List.map (fn (cond, obsso) => (
                print "path cond: ";
                print_term cond;
                print_symbobs obsso;
                print "\n\n"
              )) paths; ()
          );

        (* we also need all generated expressions to collect the variables *)
        val path_conds = List.map fst paths;
        val obs_exps = flatten (List.map (fn (_,x,ys, _) => x::ys)
                          (flatten (List.map ((fn x =>
                             case x of NONE => [] 
                                     | SOME y => y) o snd) paths)));
        val all_exps = (path_conds @ obs_exps);
    in
        (paths, all_exps)
    end

in

(* Given a program, run symbolic execution and return the feasible paths
  TODO filter out infeasible paths
 *)
fun scamv_run_symb_exec p =
    do_symb_exec p;

end

end;
