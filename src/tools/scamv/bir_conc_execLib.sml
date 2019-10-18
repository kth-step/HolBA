open HolKernel pairLib listSyntax stringSyntax;
open bir_rel_synthLib;
open bir_obs_modelLib;
open bir_symb_execLib;
open bir_symb_init_envLib;     
open bir_scamv_driverLib;
     

open bir_prog_genLib;


val debug_on = false;

(* We represent an Execution as a tree, where branches
 * in the Tree represent the Branches in the CFG *)
datatype 'a symb_tree_t = Symb_Node  of ('a  * 'a symb_tree_t list);


(* The main function to execute a BIR Program:
 * Builds an Execution Tree  *)
(*
 val bp = bir_program;
 val st = state;
 *)
val (halted :
     term list ref) = ref [];    
fun exec_run max bp  st = 
    if (not (symb_is_BST_Running st)) orelse (max = 0) then
	Symb_Node (st, [])
    else
	let
	    val max_new = if max < 0 then max else (max-1);
	    val (sts_running, sts_terminated) = 
		((dest_pair o  rhs o concl o EVAL) ``bir_symb_exec_label_block ^bp ^st``);
	    val sts_ter = (#1 (dest_list sts_terminated));
	    val sts_run = (#1 (dest_list sts_running));
	    val sts = (sts_ter @ sts_run);
	    val _ = halted := (!halted@sts_ter)
	    val _ = if not debug_on then () else
		    let
			val _ = print "=========================================\n";
			val _ = print (Int.toString max);
			val _ = print "\n=========================================\n";
		    in () end;
	    val sts_rec = List.map (exec_run max_new bp) sts;
	in
	    Symb_Node (st, sts_rec)
	end;
    

    
val obs_model_id = "bir_arm8_cache_line_model";
val hw_obs_model_id = "exp_cache_multiw";

val (current_prog_id : string ref) = ref "";
val (current_prog : term option ref) = ref NONE;
val (current_obs_model_id : string ref) = ref obs_model_id;


fun conc_test_gen_run tests (prog_id, lifted_prog) =
    let
        val add_obs = #add_obs (get_obs_model (!current_obs_model_id))

        val lifted_prog_w_obs = add_obs lifted_prog;
        val _ = print_term(lifted_prog_w_obs);
	val (paths, all_exps) = symb_exec_phase lifted_prog_w_obs; 



        val relation = mkRel paths;
        val _ = print ("Word relation\n");
        val word_relation = make_word_relation relation all_exps;
        val _ = print_term(word_relation);
        val _ = print ("Calling Z3\n");

        val model = Z3_SAT_modelLib.Z3_GET_SAT_MODEL word_relation
    in
	(lifted_prog_w_obs,model)
    end

val test_rand = conc_test_gen_run 1 o prog_gen_store_rand 5;

fun conc_exec_program depth prog env =
    let 
	val precond = ``BExp_Const (Imm1 1w)``;
	val state = (rhs o concl o EVAL)
			``bir_symb_state_init ^prog ^env ^precond``;
	val tree  = exec_run depth prog state;
	val _ = print ("Execution: Done!\n");
    in 
	tree
    end;

fun update_env name value env = 
    let val hname = fromMLstring name in
	(rhs o concl o EVAL) `` bir_symb_env_update 
			^hname (BExp_Const (Imm64 ^value)) (BType_Imm Bit64) ^env
			``
    end;


fun conc_obs_compare model prog = 

    let fun obs_extract depth prog env =
	    let val _ = halted := [];
		val _ = conc_exec_program depth prog env;
		val haltedNode = filter (fn c => symb_is_BST_Halted c) (!halted);
		val observation = map (fn n => let val (_,_,_,_,ob) = dest_bir_symb_state n in ob end) haltedNode;
	    in observation end

	fun obs_eval obs = 
	    let val nonemp_obs = filter (fn ob => (not o List.null o snd o strip_comb) ob) obs
		val obs_elem = map (fn ob => (fst o dest_list) ob)nonemp_obs
		val obs_exp = map (fn ob => let val (_,t,_) = (dest_bir_symb_obs)  ob in t end) (flatten obs_elem);
		val res = map (fn ob => let val t = (hd o snd o strip_comb ) ob in ((rhs o concl)(EVAL ``bir_eval_exp ^t (BEnv (\x. NONE))``))  end) obs_exp
	    in
		res
	    end

	val prm =  map (fn e1 => ((hd o String.tokens (fn c => c = #"_"))  (fst e1), snd e1))
		       (filter (fn e2 => Char.contains (fst e2) #"_") model);
	val nprm =   filter (fn c => not(Char.contains (fst c) #"_")) model;    
	val env1 = init_env ();
	val env2 = init_env ();
	val env1up = foldr (fn ((n,v),e) => update_env n v e) env1 prm;
	val env2up = foldr (fn ((n,v),e) => update_env n v e) env2 nprm;
	val obs1 = obs_extract 200 prog env1up;
	val obs2 = obs_extract 200 prog env2up;
    in
	(* ((obs_eval obs1) , (obs_eval obs2)) *)
	((obs_eval obs1) = (obs_eval obs2))
    end


    (* TEST *)
    (* val (prog, model) = test_rand (); *)
    (* conc_obs_compare model prog; *)

