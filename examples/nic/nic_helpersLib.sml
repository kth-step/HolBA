structure nic_helpersLib :> nic_helpersLib =
struct

  open HolKernel Parse boolLib bossLib;
  open bslSyntax;
  open pretty_exnLib;

  val ERR = mk_HOL_ERR "nic_helpersLib";
  val wrap_exn = Feedback.wrap_exn "nic_helpersLib";

  val level_log = ref (logLib.INFO: int)
  val _ = register_trace ("nic_helpersLib", level_log, logLib.MAX)

  val {error, warn, info, debug, trace, ...} = logLib.gen_fn_log_fns "nic_helpersLib" level_log;

  fun term_to_ppstring term = (ppstring pp_term) term
  fun thm_to_ppstring thm = (ppstring pp_thm) thm
  fun pprint_term term = ((print o ppstring pp_term) term; print "\n")
  fun pprint_thm thm = ((print o ppstring pp_thm) thm; print "\n")

  (* End of prelude
   ****************************************************************************)

  (*****************************************************************************
   * Misc. helpers
   *)

  fun timer_start () = Time.now();
  fun timer_stop tm = Time.toSeconds (Time.- (Time.now(), tm));
  fun timer_stop_str tm = Time.toString (Time.- (Time.now(), tm));

  (*****************************************************************************
   * Types used in signatures
   *)

  type bir_block = (Term.term * Term.term list * Term.term)

  (*****************************************************************************
   * BSL extensions
   *)

  val bvarstate = bvarimm32
  val bdenstate = (bden o bvarstate)
  val bstateval = bconst32
  val bjmplabel_str = (bjmp o belabel_str)

  type state_helpers = {
    state_list:             string list,
    autonomous_step_list:   string list,

    state_id_of:            string -> int,
    is_autonomous_step:     string -> bool,

    bstateval:              string -> term
  }
  fun gen_state_helpers automaton_name state_list =
    let
      (********* Private stuff *********)

      (* Map from state names to state info *)
      val state_map = Redblackmap.insertList (Redblackmap.mkDict String.compare,
        List.map (fn (name, (id, is_autonomous)) =>
          (name, {id=id, name=name, is_autonomous=is_autonomous})) state_list)

      fun find_state name = Redblackmap.find (state_map, name)
        handle e => raise wrap_exn ("State not found: '" ^ name ^ "'") e

      (********* Public stuff *********)

      val state_list = List.map fst (Redblackmap.listItems state_map)
      val autonomous_step_list = List.map fst (List.filter (#is_autonomous o snd) (Redblackmap.listItems state_map))

      fun state_id_of state_name = #id (find_state state_name)
      fun is_autonomous_step state_name = #is_autonomous (find_state state_name)

      val bstateval = (bconst32 o state_id_of)
    in
      {
        state_list=state_list,
        autonomous_step_list=autonomous_step_list,

        state_id_of=state_id_of,
        is_autonomous_step=is_autonomous_step,

        bstateval=bstateval
      }
    end

  (*****************************************************************************
   * Frequent BIR blocks
   *)

  fun block_nic_die (label_str, jmp_label_str) = (blabel_str label_str, [
    bassign (bvarimm1 "nic_dead", btrue)
  ], (bjmp o belabel_str) jmp_label_str)

  fun bjmp_block (label_str, jmp_label_str) =
    (blabel_str label_str, [], bjmplabel_str jmp_label_str)

  fun bstate_cases (state_var_name, unknown_state_lbl_str, (bstateval_fn: string -> term)) jumps =
    snd (List.foldl
      (fn ((lbl_str, state_name, then_lbl_str), (next_lbl_str, acc)) =>
        (lbl_str, (blabel_str lbl_str, [], bcjmp (beq (bdenstate state_var_name,
                                                       bstateval_fn state_name),
                                                  belabel_str then_lbl_str,
                                                  belabel_str next_lbl_str))::acc))
      (unknown_state_lbl_str, []) (rev jumps))
    handle e => raise wrap_exn "bstates_cases" e

  (*****************************************************************************
   * WP helpers
   *)

  fun prove_p_imp_wp proof_name prog_def precondition postcondition =
    let
      val proof_prefix = "[" ^ proof_name ^ "] "
      val debug = debug "prove_p_imp_wp"
      val trace = trace "prove_p_imp_wp"
      val wrap_exn = wrap_exn "prove_p_imp_wp"

      val p_imp_wp_bir_tm = easy_noproof_wpLib.compute_p_imp_wp_tm proof_name
        prog_def precondition postcondition
        handle e => raise pp_exn_s (proof_prefix ^ "compute_p_imp_wp_tm failed") (wrap_exn e)

      val _ = trace ("p_imp_wp_bir_tm:\n" ^ term_to_ppstring p_imp_wp_bir_tm)

      (* BIR expr => SMT-ready expr*)
      val smt_ready_tm = bir_exp_to_wordsLib.bir2bool p_imp_wp_bir_tm
        handle e => raise pp_exn_s (proof_prefix ^ "bir2bool failed") (wrap_exn e)

      val _ = trace ("smt_ready_tm:\n" ^ term_to_ppstring smt_ready_tm)

      (* Prove it using an SMT solver *)
      val start_time = timer_start ();
      val smt_thm = HolBA_HolSmtLib.Z3_ORACLE_PROVE smt_ready_tm
        handle sat_exn => (* Pretty-exn + try to show a SAT model if level_log=DEBUG *)
          let
            (* Wrap the exn, and pretty-print it to the user *)
            val wrapped_exn = pp_exn_s (proof_prefix ^ "Z3_ORACLE_PROVE failed") (wrap_exn sat_exn);

            (* Show a SAT model if level_log=DEBUG *)
            val _ = if not (!level_log >= logLib.DEBUG) then () else
              let
                fun print_model model = List.foldl
                  (fn ((name, tm), _) => (print (" - " ^ name ^ ": "); pprint_term tm))
                  () (rev model)
                val _ = debug "Asking Z3 for a SAT model..."
                val model = Z3_SAT_modelLib.Z3_GET_SAT_MODEL (mk_neg smt_ready_tm)
                val _ = (debug "SAT model:"; print_model model; print "\n")
              in () end
                handle _ => debug "Failed to compute a SAT model. Ignoring.";
          in
            raise wrapped_exn
          end
      val _ = info (proof_prefix ^ "SMT solver took: " ^ (timer_stop_str start_time) ^ " sec");

      val _ = debug "Solver reported UNSAT."
    in
      (p_imp_wp_bir_tm, smt_ready_tm, smt_thm)
    end

end (* nic_helpersLib *)
