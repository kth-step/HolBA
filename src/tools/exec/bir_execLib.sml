structure bir_execLib =
struct

  open HolKernel boolLib liteLib simpLib Parse bossLib;

  open holba_auxiliaryTheory;
  open bir_program_multistep_propsTheory;
  open bir_programSyntax;
  open bir_envSyntax;

  open bir_exec_auxLib;
  open bir_exec_blockLib;
  open bir_exec_typingLib;

  open numSyntax;
  open HolBACoreSimps;


  val log = ref (NONE : TextIO.outstream option);

  fun log_setfile log_filename = log := SOME (TextIO.openOut log_filename);

  (* a function with the old behavior of print_with_style (no implicit newline at the end) *)
  fun print_with_style_ sty = print o (add_style_to_string sty);

  fun print_log_with_style sty f s = let
    val log_ = !log;
    val _ = case log_ of
	        NONE       => ()
	      | SOME log_v => if f then TextIO.output (log_v, s) else ();
    val _ = print_with_style_ sty s;
  in () end;

  val print_log = print_log_with_style [];
  val print_l = print_log true;


(*
  bir_exec_prog_step_n var_eq_thms thm

  bir_exec_prog_step_iter (bir_exec_prog_step_n var_eq_thms) thm

  bir_exec_prog prog 1
  bir_exec_prog prog 2
  bir_exec_prog prog 3
  bir_exec_prog prog 4
  bir_exec_prog prog 5
  bir_exec_prog prog 6
  bir_exec_prog prog 7
*)


  (* determines whether a term is a sufficiently evaluated sate triple *)
  fun bir_exec_is_state_triple t =
    if not (is_pair t) orelse not (is_pair (snd (dest_pair t))) then false
    else
                               let
                                 val (_,x) = dest_pair t;
                                 val (n_acc,s) = dest_pair x;
                               in
                                 is_numeral n_acc andalso
                                 is_bir_state s andalso
                                 let val (pc,env,_) = dest_bir_state s in
                                   is_BEnv env andalso
                                   is_bir_programcounter pc andalso
                                   let val (l,i) = dest_bir_programcounter pc in
                                     is_numeral i andalso
                                     (is_BL_Label l orelse is_BL_Address l)
                                   end
                                 end
                               end;


  fun syntax_fns n d m = HolKernel.syntax_fns {n = n, dest = d, make = m} "bir_program_multistep_props"
  val syntax_fns3 = syntax_fns 3 HolKernel.dest_triop HolKernel.mk_triop;
  val (bir_exec_step_n_acc_tm,  mk_bir_exec_step_n_acc, dest_bir_exec_step_n_acc, is_bir_exec_step_n_acc)  = syntax_fns3 "bir_exec_step_n_acc";

  (* conversion for applying one BIR step *)
  fun bir_exec_prog_step_n_conv block_thm_map var_eq_thms =
    let
      val is_tm_fun = (fn t => is_bir_exec_step_n_acc t andalso
                               let
                                 val (_,n,x) = dest_bir_exec_step_n_acc t;
                               in
                                 is_numeral n andalso
                                 bir_exec_is_state_triple x
                               end
                      );
      val check_tm_fun = (fn t => is_tm_fun t orelse
                                  bir_exec_is_state_triple t
                         );
      fun conv t =
        let
          val (_,n,x) = dest_bir_exec_step_n_acc t;
          val (_,x) = dest_pair x;
          val (_,s) = dest_pair x;
          val is_terminated_thm = (SIMP_CONV (std_ss++bir_TYPES_ss) [bir_state_is_terminated_def])
                                      (mk_bir_state_is_terminated s);

          val n_eq_0_tm = (mk_eq (n, mk_numeral (Arbnum.fromInt 0)));
          val n_eq_0_thm = SIMP_CONV arith_ss [] n_eq_0_tm;

          val thm2 = (REWRITE_CONV [Once bir_exec_step_n_acc_def, is_terminated_thm, n_eq_0_thm]) t;

          val thm3 = CONV_RULE (RAND_CONV (bir_exec_prog_step_conv block_thm_map var_eq_thms)) thm2;
          val thm4 = CONV_RULE (RAND_CONV (SIMP_CONV (arith_ss) [LET_DEF])) thm3;
        in
          thm4
        end;
    in
      GEN_selective_conv is_tm_fun check_tm_fun conv
    end;

(*
val _ = debug_trace := 2;
*)
  (* executes one step and then recurses (one BIR statement per step) *)
  fun bir_exec_prog_step_iter step_n_conv thm =
    let
      val _ = if (!debug_trace > 0) then (print_l "!") else ();
      val t = (snd o dest_eq o concl) thm;
      val thm1 = (step_n_conv THENC (REWRITE_CONV [OPT_CONS_REWRS])) t;
      val thm2 = TRANS thm thm1;
      val thm = thm2;
      val _ = if (!debug_trace > 1) then (
                print_l "\n--------------------------------------\n";
                print_l (term_to_string t);
                print_l "\n--------------------------------------\n"
              ) else ();
    in
      (bir_exec_prog_step_iter step_n_conv thm)
      handle UNCHANGED =>
      (
        if (!debug_trace > 0) then (print_l "done\n") else ();
        let
          val result = (snd o dest_eq o concl) thm;
          fun check_thm_fun _ = bir_exec_is_state_triple result;
          fun extract_print_tm_fun _ = result;
        in
          GEN_check_thm check_thm_fun extract_print_tm_fun thm
        end
      )
    end;




  (* preprocessing and execution *)
  fun bir_exec_prog_gen prog_l_def n_max valid_prog_thm state =
    let
      val _ = if (!debug_trace > 0) then (print_l "input validation starts\n") else ();
      (* verify that the inputs are as expected (definition theorem and program theorems) *)
      val prog_l_const = (fst o dest_eq o concl) prog_l_def;
      val prog_const = (mk_BirProgram prog_l_const);
      val prog = (snd o dest_eq o concl o (REWRITE_CONV [prog_l_def])) prog_const;
(*      val prog = bir_exec_prog_normalize prog handle UNCHANGED => prog;*)
      val _ = if not (is_const prog_l_const) orelse
                 not (identical (concl valid_prog_thm) ``bir_is_valid_program ^prog_const``) then
                raise ERR "bir_exec_prog_gen"
                          "input validation failed"
              else
                ();
      val _ = if (!debug_trace > 0) then (print_l ("done\n")) else ();
      val _ = if (!debug_trace > 0) then (print_l ("\n")) else ();
      

      val _ = if (!debug_trace > 0) then (print_l "preprocessing starts\n") else ();
      val timer = timer_start 0;

      val n = numSyntax.mk_numeral (Arbnumcore.fromInt n_max);

      val labels = gen_labels_of_prog prog;
      val block_thm_map = gen_block_thm_map prog_l_def valid_prog_thm;

      val vars = gen_vars_of_prog prog;
      val var_eq_thms = gen_var_eq_thms vars;

      val exec_term = ``bir_exec_step_n ^prog_const ^state ^n``;
      val thm = REWRITE_CONV [GSYM bir_exec_step_n_acc_eq_thm] exec_term;

      val step_n_conv = (bir_exec_prog_step_n_conv block_thm_map var_eq_thms);
      val d_s = timer_stop timer;

      val _ = if (!debug_trace > 0) then (print_l ("done\n")) else ();
      val _ = if (!debug_trace > 0) then (print_l (" - " ^ d_s ^ " s - \n")) else ();
      val _ = if (!debug_trace > 0) then (print_l ("\n")) else ();


      val _ = if (!debug_trace > 0) then (print_l "execution starts\n") else ();

      (* execute *)
      val timer = timer_start 0;
      val exec_thm = bir_exec_prog_step_iter step_n_conv thm;
      val d_s = timer_stop timer;
      val _ = if (!debug_trace > 0) then (print_l ("done\n")) else ();
      val _ = if (!debug_trace > 0) then (print_l (" - " ^ d_s ^ " s - \n")) else ();
      val _ = if (!debug_trace > 0) then (print_l ("\n")) else ();

      (* fix REVERSEd observations *)
      val reverse_list_conv = REWRITE_CONV [REVERSE_DEF, APPEND];
      val _ = if (!debug_trace > 0) then (print_l "reversing observations\n") else ();
      val exec_thm' = (CONV_RULE (RAND_CONV reverse_list_conv)) exec_thm;
      val _ = if (!debug_trace > 0) then (print_l "done\n") else ();

      val result_t = (snd o dest_eq o concl) exec_thm';
      val (ol, x)  = dest_pair result_t;
      val (n, s2)  = dest_pair x;
    in
      (ol, n, s2, exec_thm')
    end;

  (* function for using execution in scripts, it prints out relevant progress information and the output *)
  fun bir_exec_prog_print name prog n_max validprog_o welltypedprog_o state_o =
    let
      val _ = print_l "\n";
      val _ = print_l ("executing " ^ name ^ "\n");
      val _ = print_l "================================\n";

      (* determine if a block list definition has to be created, and do so if required *)
      val _ = print_l "checking block list definition...\n";
      val _ = print_l "--------------------------------\n";
      val prog_l = dest_BirProgram prog;
      val prog_l_def = if (is_const prog_l) then
                         let
                           val def_str = (fst o dest_const) prog_l;
                           val def_thm = #1 o #2 $ hd (DB.find def_str);
                         in
                           def_thm
                         end
                       else
                         Define [QUOTE ("bir_exec_prog_" ^ name ^ "_l"),
                                 QUOTE " = ", ANTIQUOTE prog_l];
      val _ = print_l "ok\n";
      val _ = print_l "\n";

      (* if validprog theorem is not supplied, compute it *)
      val _ = print_l "program validity...\n";
      val _ = print_l "--------------------------------\n";
      val timer = timer_start 0;

      val valid_prog_thm = case validprog_o of
			      SOME thm => thm
	                    | NONE     => bir_exec_valid_prog prog_l_def;

      val d_s = timer_stop timer;
      val _ = print_l "ok\n";
      val _ = if (!debug_trace > 0) then (print_l (" - " ^ d_s ^ " s - \n")) else ();
      val _ = print_l "\n";

      (* if welltypedprog theorem is not supplied, compute it *)
      val _ = print_l "typechecking...\n";
      val _ = print_l "--------------------------------\n";
      val timer = timer_start 0;

      val well_typed_prog_thm = case welltypedprog_o of
				    SOME thm => thm
				  | NONE     => bir_exec_well_typed_prog prog_l_def;

      val d_s = timer_stop timer;
      val _ = print_l "ok\n";
      val _ = if (!debug_trace > 0) then (print_l (" - " ^ d_s ^ " s - \n")) else ();
      val _ = print_l "\n";

      (* if state is not supplied, compute an empty one *)
      val _ = print_l "state checking/generation...\n";
      val _ = print_l "--------------------------------\n";
      val timer = timer_start 0;

      val state = case state_o of
		    SOME state => state
		  | NONE       =>
                      let
			val pc = (snd o dest_eq o concl o EVAL) ``bir_pc_first ^prog``;

			val vars = gen_vars_of_prog prog;

			val env = bir_exec_env_initd_env vars;

			val state = ``<| bst_pc := ^pc ; bst_environ := ^env ; bst_status := BST_Running |>``;
                      in
                        state
                      end;

      val d_s = timer_stop timer;
      val _ = print_l "ok\n";
      val _ = if (!debug_trace > 0) then (print_l (" - " ^ d_s ^ " s - \n")) else ();
      val _ = print_l "\n";

      (* now execution *)
      val _ = print_l "executing...\n";
      val _ = print_l "--------------------------------\n";
      val timer = timer_start 0;
      val (ol, n, s2, exec_thm) = bir_exec_prog_gen prog_l_def n_max valid_prog_thm state;
      val d_s = timer_stop timer;
      val _ = print_l "ok\n";

      val _ = if (!debug_trace > 0) then (print_l (" exec total: - " ^ d_s ^ " s - \n")) else ();
      val _ = print_l "\n";


      (* now the result *)
      val _ = print_l "\n";
      val _ = print_l "================================\n";
      val _ = print_l "result:\n";
      val _ = print_l "================================\n";
      val _ = print_l "\n";

      val _ = print_l "\n";
      val _ = print_l "ol = ";
      val _ = print_l (term_to_string ol);
      val _ = print_l "\n";

      val _ = print_l "\n";
      val _ = print_l "n = ";
      val _ = print_l (term_to_string n);
      val _ = print_l "\n";

      val _ = print_l "\n";
      val _ = print_l "s2 = ";
      val _ = print_l (term_to_string s2);
      val _ = print_l "\n";



      val _ = print_l "\n";
      val _ = print_l "================================\n";
      val _ = print_l "done\n";
      val _ = print_l "================================\n";
      val _ = print_l "\n";
    in
      exec_thm
    end;



end
