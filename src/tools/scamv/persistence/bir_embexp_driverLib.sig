signature bir_embexp_driverLib = sig
  (* a machine consists of register to value mappings and a memory mapping *)
  (* register names are for example R0 - R29, unmapped registers are 0 *)
  (* memory mapping has a word size, unmapped memory is 0 *)
  datatype machineState = MACHSTATE of (((string, Arbnum.num) Redblackmap.dict) * (int * ((Arbnum.num, Arbnum.num) Redblackmap.dict)));
  val machstate_empty   : machineState;
  val machstate_print   : machineState -> unit
  val machstate_add_reg : string * Arbnum.num -> machineState -> machineState
  val machstate_replace_mem : int * (Arbnum.num, Arbnum.num) Redblackmap.dict -> machineState -> machineState

  (* platform parameters *)
  (* ======================================== *)
  val bir_embexp_params_code   : Arbnum.num (* base address for placement *)
  val bir_embexp_params_memory : Arbnum.num * Arbnum.num (* base, length *)

  val bir_embexp_params_cacheable : Arbnum.num -> Arbnum.num

  (* conversion from asm program (asm lines) to "normal program" *)
  val bir_embexp_prog_to_code : string list -> string
  (* and the other direction *)
  val bir_embexp_code_to_prog : string -> string list


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
                                  (machineState * machineState * machineState option) ->
                                  string
  (* Inputs:
       - exp_id (see above)
       - with_reset (run with reset or not)
     Returns (maybe result, comment)
   *)
(*
  val bir_embexp_run : string -> bool -> (bool option * string)
*)


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
  val bir_embexp_load_exp  : string -> string list * (machineState * machineState * machineState option)

  val bir_embexp_load_exp_ids : string -> string list

  val bir_embexp_load_progs : string -> string list list

  val bir_embexp_create_list_open : string -> string -> TextIO.outstream

end
