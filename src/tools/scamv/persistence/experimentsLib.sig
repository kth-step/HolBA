signature experimentsLib = sig

  (* machine states *)
  (* ======================================== *)
  (* a machine consists of register to value mappings and a memory mapping *)
  (* register names are for example R0 - R29, unmapped registers are 0 *)
  (* memory mapping has a word size, unmapped memory is 0 *)
  datatype machineState = MACHSTATE of (((string, Arbnum.num) Redblackmap.dict) * (int * ((Arbnum.num, Arbnum.num) Redblackmap.dict)));
  val machstate_empty   : machineState;
  val machstate_print   : machineState -> unit
  val machstate_add_reg : string * Arbnum.num -> machineState -> machineState
  val machstate_replace_mem : int * (Arbnum.num, Arbnum.num) Redblackmap.dict -> machineState -> machineState

  (* conversions to and fro Json *)
  val machstate_to_Json : machineState -> Json.json
  val Json_to_machstate : Json.json -> machineState


  (* programs *)
  (* ======================================== *)
  (* conversion from asm program (asm lines) to "normal program" *)
  val bir_embexp_prog_to_code : string list -> string
  (* and the other direction *)
  val bir_embexp_code_to_prog : string -> string list

  val bir_embexp_code_to_prog_raw : (string list -> string list) -> string -> string list
  val bir_embexp_prog_std_preproc : string list -> string list


  (* embexp platform parameters *)
  (* ======================================== *)
  val bir_embexp_params_code   : Arbnum.num (* base address for placement *)
  val bir_embexp_params_memory : Arbnum.num * Arbnum.num (* base, length *)

  val bir_embexp_params_cacheable : Arbnum.num -> Arbnum.num

end
