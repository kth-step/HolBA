signature bir_embexp_driverLib = sig

  (* experiment creation and running *)
  (* ======================================== *)
  (* Inputs:
       - (architecture_id, prog_gen_id)
       - asm_code
     Returns id of program entry (prog_id)
   *)
  val bir_embexp_prog_create : (string * string) -> string -> string

  (* Inputs:
       - (architecture_id, experiment_type_id/attacker_id, state_gen_id/obs_model_id)
       - prog_id (see above)
       - (state1, state2, train_option)
     Returns experiment id (exp_id)
   *)
  val bir_embexp_states2_create : (string * string * string) ->
                                  string ->
                                  (experimentsLib.machineState *
                                   experimentsLib.machineState *
                                   experimentsLib.machineState option) ->
                                  string


  (* progress logging *)
  (* ======================================== *)
  val bir_embexp_log_prog_close : unit   -> unit
  val bir_embexp_log_exp_close  : unit   -> unit
  val bir_embexp_log_prog       : string -> unit
  val bir_embexp_log_exp        : string -> unit
  val bir_embexp_log            : string -> unit


  (* embexp implicitly starts a run, "finalize" completes the run and writes runtime *)
  (* ======================================== *)
  val bir_embexp_finalize       : unit   -> unit


  (* loading programs and experiment inputs from logs *)
  (* ======================================== *)
  (* Inputs: - prog_id *)
  (*         - arch_id *)
  (* Output: asm_lines *)
  val bir_embexp_load_prog : string -> string -> string list

  (* Input: exp_id *)
  (* Output: asm_lines, model pair *)
  val bir_embexp_load_exp  : string -> string list * (experimentsLib.machineState *
                                                      experimentsLib.machineState *
                                                      experimentsLib.machineState option)

  val bir_embexp_load_exp_ids : string -> string list

  val bir_embexp_load_progs : string -> string list list

  val bir_embexp_create_list_open : string -> string -> TextIO.outstream

end
