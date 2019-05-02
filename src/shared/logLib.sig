signature logLib =
sig

  (****************************************************************************)
  (* Log function generating library.                                         *)
  (*                                                                          *)
  (* Usage:                                                                   *)
  (*   val (error, warn, info, debug, trace) = gen_log_fns                    *)
  (*     "my_fancyLib" ref_to_debug_level;                                    *)
  (*                                                                          *)
  (* Where ref_to_debug_level is a ref to an int variable. Log levels are as  *)
  (* follows: ERROR < WARN < INFO < DEBUG < TRACE = MAX.                      *)
  (*                                                                          *)
  (* It is recommended to use the provided variables to specify log levels    *)
  (* instead of directly using int values (ERROR, WARN, and so on).           *)
  (*                                                                          *)
  (* Hence, the recommended pattern to register a log trace is as follows:    *)
  (*                                                                          *)
  (*   val level_log = ref (logLib.INFO: int)                                 *)
  (*   val _ = register_trace ("script_name", level_log, logLib.MAX)          *)
  (*                                                                          *)
  (****************************************************************************)

  val ERROR: int
  val WARN:  int
  val INFO:  int
  val DEBUG: int
  val TRACE: int
  val MAX:   int

  (* Top-level log functions. Recommended for usage in examples and tests.
   *)
  type log_functions = {
    error: string -> unit,
    warn : string -> unit,
    info : string -> unit,
    debug: string -> unit,
    trace: string -> unit
  }
  val gen_log_fns: string -> int ref -> log_functions;

  (* Log functions used inside functions. Recommended for usage in libs and
   * theories.
   *)
  type fn_log_functions = {
    error: string -> string -> unit,
    warn : string -> string -> unit,
    info : string -> string -> unit,
    debug: string -> string -> unit,
    trace: string -> string -> unit
  }
  val gen_fn_log_fns: string -> int ref -> fn_log_functions;

end
