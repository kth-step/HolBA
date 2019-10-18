open HolKernel pairLib listSyntax stringSyntax wordsSyntax;
open bir_rel_synthLib;
open bir_obs_modelLib;
open bir_symb_execLib;
open bir_symb_init_envLib;     
open bir_scamv_driverLib;
open bir_embexp_driverLib;
   

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

(*
val depth = 200;
val env = env1up;
*)

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

fun find_THE_state states =
  let
    fun eq_true t = t = ``SOME (BVal_Imm (Imm1 1w))``;
    fun pathcond_val s = (snd o dest_eq o concl o EVAL)
                         ``bir_eval_exp ((^s).bsst_pred) (BEnv (K NONE))``;
    val filteredStates = List.filter (eq_true o pathcond_val) states;
    val _ = if length filteredStates = 1 then () else
              raise ERR "conc_obs_compare" "more than one state has a true path condition?!?!?!";
  in
    hd filteredStates
  end;


fun conc_obs_compare model prog = 

    let fun obs_extract depth prog env =
	    let val _ = halted := [];
		val _ = conc_exec_program depth prog env;
		val haltedNode = find_THE_state (!halted);
		val _ = if symb_is_BST_Halted haltedNode then () else
                          raise ERR "conc_obs_compare" "the input state did not execute the whole program properly?!?!?!";
		val (_,_,_,_,observation) = dest_bir_symb_state haltedNode;
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
	((obs_eval [obs1]) = (obs_eval [obs2]))
    end


local
    fun remove_padding s =
	s |> Substring.full
	  |> Substring.dropl Char.isSpace
	  |> Substring.dropr Char.isSpace
	  |> Substring.string;
in
fun inspect_counterexamples filename len () =
    let
	val istrm = TextIO.openIn filename;
	val inprog = TextIO.inputAll istrm before TextIO.closeIn istrm
	val prog_gen_id = "Test Counterexmaples";
	val asm_code = remove_padding inprog;
	val compile_opt = SOME (process_asm_code asm_code);
	val lifted_prog =   case compile_opt of
				SOME sections => lift_program_from_sections sections;
	val prog_with_halt =
            let
		val (blocks,ty) = dest_list (dest_BirProgram lifted_prog);
		val obs_ty = (hd o snd o dest_type) ty;
		val lbl = ``BL_Address (Imm64 ^(mk_wordi (Arbnum.fromInt (len*4), 64)))``;
		val new_last_block =  bir_programSyntax.mk_bir_block
					  (lbl, mk_list ([], mk_type ("bir_stmt_basic_t", [obs_ty])),
					   ``BStmt_Halt (BExp_Const (Imm32 0x000000w))``);
            in
		(mk_BirProgram o mk_list) (blocks@[new_last_block],ty)
            end
	val prog_id = bir_embexp_prog_create ("arm8", prog_gen_id) asm_code;
    in
	(prog_id, prog_with_halt)
    end;
end

(*
val test_rand = conc_test_gen_run 1 o prog_gen_store_rand 5;
val test_rand = conc_test_gen_run 1 o (inspect_counterexamples "tempdir/code2_neq.asm" 10);
val (prog, model) = test_rand ();
conc_obs_compare model prog;
*)

(*

val prm = [("R0", ``0x8000000000030000w:word64``), ("R18", ``0x1FFFFFFFFFFFFE00w:word64``)];
val nprm = [("R0", ``0x8000000000000000w:word64``), ("R18", ``0xEFFFFFFFFFFFFE20w:word64``)];

val prog = ``
BirProgram
      [<|bb_label := BL_Address (Imm64 0w);
         bb_statements :=
           [BStmt_Assign (BVar "ProcState_C" (BType_Imm Bit1))
              (BExp_BinPred BIExp_LessOrEqual (BExp_Const (Imm64 0xCA2000w))
                 (BExp_Den (BVar "R0" (BType_Imm Bit64))));
            BStmt_Assign (BVar "ProcState_N" (BType_Imm Bit1))
              (BExp_BinPred BIExp_SignedLessThan
                 (BExp_BinExp BIExp_Minus
                    (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 0xCA2000w))) (BExp_Const (Imm64 0w)));
            BStmt_Assign (BVar "ProcState_V" (BType_Imm Bit1))
              (BExp_BinPred BIExp_Equal
                 (BExp_BinPred BIExp_SignedLessThan
                    (BExp_BinExp BIExp_Minus
                       (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 0xCA2000w)))
                    (BExp_Const (Imm64 0w)))
                 (BExp_BinPred BIExp_SignedLessOrEqual
                    (BExp_Const (Imm64 0xCA2000w))
                    (BExp_Den (BVar "R0" (BType_Imm Bit64)))));
            BStmt_Assign (BVar "ProcState_Z" (BType_Imm Bit1))
              (BExp_BinPred BIExp_Equal
                 (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 0xCA2000w)));
            BStmt_Assign (BVar "R15" (BType_Imm Bit64))
              (BExp_BinExp BIExp_Minus
                 (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 0xCA2000w)))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 4w)))|>;
       <|bb_label := BL_Address (Imm64 4w); bb_statements := [];
         bb_last_statement :=
           BStmt_CJmp (BExp_Den (BVar "ProcState_V" (BType_Imm Bit1)))
             (BLE_Label (BL_Address (Imm64 40w)))
             (BLE_Label (BL_Address (Imm64 8w)))|>;
       <|bb_label := BL_Address (Imm64 40w); bb_statements := [];
         bb_last_statement := BStmt_Halt (BExp_Const (Imm32 0w))|>]  
``;

*)
