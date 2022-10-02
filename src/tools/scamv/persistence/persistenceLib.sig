signature persistenceLib = sig

  (* logging of holba run data and run context management *)
  (* ======================================== *)
  val run_log_prog       : string -> unit;
  val run_log_exp        : string -> unit;
  val run_log            : string -> unit;
  (* persistenceLib implicitly creates a run with first call, "finalize" completes the whole run and writes runtime *)
  val run_finalize       : unit   -> unit;
  (* manually start a new run with an optional description text *)
  val run_init           : string option -> unit;


  (* storing to logs *)
  (* ======================================== *)
  (* Inputs:
       - architecture
       - experiment program
       - run metadata (e.g. prog_gen_id)
     Returns id of program entry (prog_id)
   *)
  val run_create_prog :
    experimentsLib.experiment_arch ->
    experimentsLib.experiment_prog ->
    string ->
    (string * string) list ->
    embexp_logsLib.prog_handle;

  (* Inputs:
       - prog_id (see above)
       - type of experiment (e.g. exps2)
       - experiment run parameters (e.g. experiment_type_id/attacker_id)
       - states (e.g. state1, state2, train)
       - entry point
       - exit pints
       - run metadata (e.g. state_gen_id/obs_model_id)
     Returns experiment id (exp_id)
   *)
  val run_create_exp :
    embexp_logsLib.prog_handle ->
    experimentsLib.experiment_type ->
    string ->
    (string * experimentsLib.machineState) list ->
    Arbnum.num ->
    Arbnum.num list ->
    (string * string) list ->
    embexp_logsLib.exp_handle;


  (* retrieving from logs *)
  (* ======================================== *)
  val runlogs_load_progs : string -> experimentsLib.experiment_prog list;
  val get_last_exp_list_name : unit -> string;
  val run_exp_list : string -> bool;

end
