signature bir_embexp_driverLib = sig

  (* platform parameters *)
  (* ======================================== *)
  val bir_embexp_params_code   : Arbnum.num (* base address for placement *)
  val bir_embexp_params_memory : Arbnum.num * Arbnum.num (* base, length *)

  (* conversion from asm program (asm lines) to "normal program" *)
  val bir_embexp_prog_to_code : string list -> string


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
       - (state1, state2)
     Returns experiment id (exp_id)
   *)
  val bir_embexp_sates2_create : (string * string * string) -> string -> (((string * num) list) * ((string * num) list)) -> string

  (* Inputs:
       - exp_id (see above)
       - with_reset (run with reset or not)
     Returns (maybe result, comment)
   *)
  val bir_embexp_run : string -> bool -> (bool option * string)

end
