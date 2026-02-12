signature nic_helpersLib =
sig

  (* Frequent type abbreviations *)
  type bir_block = term * term list * term;

  (* BSL extensions *)
  val bvarstate: string -> term
  val bdenstate: string -> term
  val bstateval: int -> term
  val bjmplabel_str: string -> term

  type state_helpers = {
    state_list:             string list,
    autonomous_step_list:   string list,

    state_id_of:            string -> int,
    is_autonomous_step:     string -> bool,

    bstateval:              string -> term
  }
  val gen_state_helpers: string -> (string * (int * bool)) list -> state_helpers

  (* Frequent BIR blocks *)
  val block_nic_die: (string * string) -> bir_block
  val bjmp_block: (string * string) -> bir_block

  val bstate_cases: (string * string * (string -> term))
                 -> (string * string * string) list
                 -> bir_block list

  (* WP helpers *)
  val prove_p_imp_wp: string -> thm -> (term * term) -> (term list * term) -> (term * term * thm)

  (* Misc. helpers *)
  val timer_start: unit -> Time.time
  val timer_stop: Time.time -> LargeInt.int
  val timer_stop_str: Time.time -> string

end (* nic_helpersLib *)
