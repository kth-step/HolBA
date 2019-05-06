open HolKernel Parse boolLib bossLib;
open bslSyntax;
open pretty_exnLib;
open nic_helpersLib nic_stateLib;
open nic_common_invariantsLib;

(* Load the dependencies in interactive sessions *)
val _ = if !Globals.interactive then (
  load "HolSmtLib"; (* HOL/src/HolSmt *)
  ()) else ();

val _ = if !Globals.interactive then () else (
  Feedback.set_trace "HolSmtLib" 2;
  Feedback.set_trace "bir_wpLib.DEBUG_LEVEL" 1;
  Feedback.set_trace "easy_noproof_wpLib" 2;
  Feedback.set_trace "nic_helpersLib" logLib.INFO;
  Feedback.set_trace "Define.storage_message" 1;
  Feedback.emit_WARNING := false;
  ());

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = Globals.show_tags := true;
val _ = Globals.linewidth := 100;

val _ = bir_ppLib.install_bir_pretty_printers ();

(*
val _ = Globals.linewidth := 100;
val _ = Globals.show_tags := true;
val _ = Globals.show_types := true;
val _ = Globals.show_assums := true;
val _ = wordsLib.add_word_cast_printer ();
val _ = Feedback.set_trace "HolSmtLib" 0;
val _ = Feedback.set_trace "HolSmtLib" 4;
val _ = Feedback.set_trace "bir_wpLib.DEBUG_LEVEL" 2;
val _ = Feedback.set_trace "easy_noproof_wpLib" 2;
val _ = Feedback.set_trace "Define.storage_message" 1;
*)

val level_log = ref (logLib.INFO: int)
val {error, warn, info, debug, trace, ...} = logLib.gen_log_fns "init-wp-test" level_log;

fun term_to_ppstring term = (ppstring pp_term) term
fun thm_to_ppstring thm = (ppstring pp_thm) thm
fun pprint_term term = ((print o ppstring pp_term) term; print "\n")
fun pprint_thm thm = ((print o ppstring pp_thm) thm; print "\n")

(* End of prelude
 ****************************************************************************)

val bstateval_init = #bstateval init_state
val bstateval_tx = #bstateval tx_state
val bstateval_td = #bstateval td_state

(* Load and print the program *)
val nic_program_def = Define `nic_program = ^(nic_programLib.nic_program)`;
val _ = if !level_log >= logLib.INFO
  then (pprint_thm nic_program_def; print "\n")
  else ();


(* Init automaton: NIC doesn't die in autonomous transition *)
val (_, _, init_autonomous_step_doesnt_die_thm) = prove_p_imp_wp
  "init_automaton_doesnt_die"
  (* prog_def *) nic_program_def
  (* Precondition *) (
    blabel_str "init_entry",
    bandl [
      invariant_nic_not_dead,
      (* Current init automaton state is an autonomous one *)
      borl (List.map (fn s => beq (bdenstate "nic_init_state", bstateval_init s))
            (#autonomous_step_list init_state))
    ]
  )
  (* Postcondition *) (
    [blabel_str "init_end"],
    invariant_nic_not_dead
  )
val _ = info "Successfully proved: init automaton doesn't die"
val _ = if !level_log >= logLib.INFO
  then (pprint_thm init_autonomous_step_doesnt_die_thm; print "\n")
  else ();


(* Init automaton: NIC *dies* in not-autonomous transition *)
val init_not_autonom_states = List.filter
  (fn state_name => not ((#is_autonomous_step init_state) state_name))
  (#state_list init_state)

val (_, _, init_autonomous_step_doesnt_die_thm) = prove_p_imp_wp
  "init_automaton_dies"
  (* prog_def *) nic_program_def
  (* Precondition *) (
    blabel_str "init_entry",
    bandl [
      invariant_nic_not_dead,
      borl [
        beq (bdenstate "nic_init_state", bstateval_init "it_power_on"),
        beq (bdenstate "nic_init_state", bstateval_init "it_initialize_hdp_cp"),
        beq (bdenstate "nic_init_state", bstateval_init "it_initialized")
      ]
    ]
  )
  (* Postcondition *) (
    [blabel_str "init_end"],
    bnot invariant_nic_not_dead
  )
val _ = info "Successfully proved: init automaton dies"
val _ = if !level_log >= logLib.INFO
  then (pprint_thm init_autonomous_step_doesnt_die_thm; print "\n")
  else ();


(* TX automaton: NIC doesn't die in autonomous transition *)
val (_, _, tx_autonomous_step_doesnt_die_thm) = prove_p_imp_wp
  "tx_automaton_doesnt_die"
  (* prog_def *) nic_program_def
  (* Precondition *) (
    blabel_str "tx_entry",
    bandl [
      invariant_nic_not_dead,
      borl (List.map (fn s => beq (bdenstate "nic_tx_state", bstateval_tx s))
            (#autonomous_step_list tx_state))
    ]
  )
  (* Postcondition *) (
    [blabel_str "tx_end"],
    invariant_nic_not_dead
  )
val _ = info "Successfully proved: tx automaton doesn't die"
val _ = if !level_log >= logLib.INFO
  then (pprint_thm tx_autonomous_step_doesnt_die_thm; print "\n")
  else ();
