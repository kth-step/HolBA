structure bir_conc_execLib : bir_conc_execLib =
struct

  open HolKernel pairLib listSyntax stringSyntax wordsSyntax;
  open bir_rel_synthLib;
  open bir_obs_modelLib;
  open bir_symb_execLib;
  open bir_symb_masterLib;
  open bir_symb_init_envLib;     
  open bir_scamv_driverLib;
  open bir_embexp_driverLib;

  open bir_prog_genLib;


  fun update_env name value env = 
      let val hname = fromMLstring name in
	  (rhs o concl o EVAL) `` bir_symb_env_update 
			  ^hname (BExp_Const (Imm64 ^value)) (BType_Imm Bit64) ^env
			  ``
      end;

  fun gen_symb_updates s env =
    foldr (fn ((n,v),e) => update_env n v e) (env) s;

  fun conc_exec_program depth prog envfo =
    let 
      val precond = ``BExp_Const (Imm1 1w)``;

      val states = symb_exec_process_to_leafs_pdecide (fn x => true) envfo depth precond prog;

      (* filter for the concrete path *)
      fun eq_true t = t = ``SOME (BVal_Imm (Imm1 1w))``;
      fun pathcond_val s = (snd o dest_eq o concl o EVAL)
			   ``bir_eval_exp ((^s).bsst_pred) (BEnv (K NONE))``;
      val filteredStates = List.filter (eq_true o pathcond_val) states;
      val final_state = case filteredStates of
			   [s] => s
			 | []  => raise ERR "conc_obs_compute" "no state has a true path condition?!?!?!"
                         | _   => raise ERR "conc_obs_compute" "more than one state has a true path condition?!?!?!";
    in
      final_state
    end;

  fun conc_exec_obs_extract symb_state =
    let
      val state_ = symb_state;
      val _ = if symb_is_BST_Halted state_ then () else
              raise ERR "conc_exec_program" "the final state is not halted, something is off";
      val (_,_,_,_,observation) = dest_bir_symb_state state_;

      val nonemp_obs = filter (fn ob => (not o List.null o snd o strip_comb) ob) [observation];
      val obs_elem = map (fn ob => (fst o dest_list) ob)nonemp_obs;
      val obs_exp = map (fn ob => let val (_,t,_) = (dest_bir_symb_obs)  ob in t end) (flatten obs_elem);
      val res = map (fn ob => let val t = (hd o snd o strip_comb ) ob in ((rhs o concl)(EVAL ``bir_eval_exp ^t (BEnv (\x. NONE))``))  end) obs_exp;
    in res end;

  fun conc_exec_obs_compute prog s =
    let
      val envfo = SOME (gen_symb_updates s);
      val state_ = conc_exec_program 200 prog envfo;
      val obs = conc_exec_obs_extract state_;
    in
      obs
    end;

  fun conc_exec_obs_compare prog (s1, s2) =
    conc_exec_obs_compute prog s1 = conc_exec_obs_compute prog s2;


(* ============================================================ *)

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

(*
export HOLBA_EMBEXP_LOGS=/home/andreas/data/hol/HolBA_logs/EmbExp-Logs_hamed
*)

val exp_id = "arm8/exps2/exp_cache_multiw/269c03c7a99a2a222bc8fee1ba30a6984df76f2b";
val (asm_lines, (s1,s2)) = bir_embexp_load_exp exp_id;

val (_, lifted_prog) = prog_gen_store_fromlines asm_lines ();
val prog = lifted_prog;

conc_exec_obs_compute prog s1
conc_exec_obs_compare prog (s1,s2);

*)

end (* struct *)
