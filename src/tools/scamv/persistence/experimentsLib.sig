signature experimentsLib = sig

  val term_to_string_wtypes : Abbrev.term -> string;

  (* machine states *)
  (* ======================================== *)
  (* a machine consists of register to value mappings and a memory mapping *)
  (* register names are for example R0 - R29, unmapped registers are 0 *)
  (* memory mapping has
       - a word size, and
       - defines the value of unmapped memory as Arbnum (in word size)
   *)
  datatype machineState = MACHSTATE of (((string, Arbnum.num) Redblackmap.dict) *
                                        (int * Arbnum.num * ((Arbnum.num, Arbnum.num) Redblackmap.dict)));
  val machstate_empty   : Arbnum.num -> machineState;
  val machstate_print   : machineState -> unit
  val machstate_add_reg : string * Arbnum.num -> machineState -> machineState
  val machstate_replace_mem : int * Arbnum.num * (Arbnum.num, Arbnum.num) Redblackmap.dict -> machineState -> machineState

  (* conversions to and fro Json *)
  val machstate_to_Json : machineState -> Json.json
  val Json_to_machstate : Json.json -> machineState


  (* programs *)
  (* ======================================== *)
  type experiment_prog;

  val mk_experiment_prog   : string list -> experiment_prog;
  val prog_from_asm_code   : string      -> experiment_prog;

  val prog_length          : experiment_prog -> int;
  val dest_experiment_prog : experiment_prog -> string list;
  val prog_to_asm_code     : experiment_prog -> string;


  (* additional structured data *)
  (* ======================================== *)
  datatype experiment_arch = ArchARM8;
  val exp_arch_to_string : experiment_arch -> string;

  datatype experiment_type = ExperimentTypeStdTwo;
  val exp_type_to_string : experiment_type -> string;


  (* embexp platform parameters *)
  (* ======================================== *)
  val embexp_params_code   : Arbnum.num; (* base address for placement *)
  val embexp_params_memory : Arbnum.num * Arbnum.num; (* base, length *)

  val embexp_params_cacheable : Arbnum.num -> Arbnum.num;

  val embexp_params_checkmemrange : machineState -> bool;

end
