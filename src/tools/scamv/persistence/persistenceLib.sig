signature persistenceLib = sig

  (* logging of holba run data and run context management *)
  (* ======================================== *)
  val run_log_prog_close : unit   -> unit;
  val run_log_exp_close  : unit   -> unit;
  val run_log_prog       : string -> unit;
  val run_log_exp        : string -> unit;
  val run_log            : string -> unit;
  (* persistenceLib implicitly creates a run with first call, "finalize" completes the whole run and writes runtime *)
  val run_finalize       : unit   -> unit;


  (* storing to logs *)
  (* ======================================== *)
  (* Inputs:
       - (architecture_id, prog_gen_id)
       - experiment program
     Returns id of program entry (prog_id)
   *)
  val run_create_prog :
    (experimentsLib.experiment_arch * string) ->
    experimentsLib.experiment_prog ->
    embexp_logsLib.prog_handle;

  (* Inputs:
       - (experiment_type_id/attacker_id, state_gen_id/obs_model_id)
       - prog_id (see above)
       - (state1, state2, train_option)
     Returns experiment id (exp_id)
   *)
  val run_create_states2 : (string * string) ->
                                  embexp_logsLib.prog_handle ->
                                  (experimentsLib.machineState *
                                   experimentsLib.machineState *
                                   experimentsLib.machineState option) ->
                                  embexp_logsLib.exp_handle;


  (* retrieving from logs *)
  (* ======================================== *)
  val run_load_progs : string -> experimentsLib.experiment_prog list;

end
