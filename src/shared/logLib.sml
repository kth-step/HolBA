structure logLib :> logLib =
struct

  open HolKernel Parse PPBackEnd;

  val ERR = mk_HOL_ERR "logLib";
  val wrap_exn = Feedback.wrap_exn "logLib";

  val ERROR = 0
  val WARN  = 1
  val INFO  = 2
  val DEBUG = 3
  val TRACE = 4
  val MAX   = TRACE

  infixr $
  fun f $ x = f x

  type log_functions = {
    error: string -> unit,
    warn : string -> unit,
    info : string -> unit,
    debug: string -> unit,
    trace: string -> unit
  }
  fun gen_log_fns lib_name level_ref =
    let
      fun error msg = if !level_ref >= ERROR then (
          print $ (add_style_to_string [FG OrangeRed, Bold] ("[ERROR @ " ^ lib_name ^ "] "))
                ^ (add_style_to_string [FG OrangeRed] msg)
                ^ "\n"
        ) else ();
      fun warn msg = if !level_ref >= WARN then (
          print $ (add_style_to_string [FG Yellow, Bold] ("[ WARN @ " ^ lib_name ^ "] "))
                ^ msg
                ^ "\n"
        ) else ();
      fun info msg = if !level_ref >= INFO then (
          print $ (add_style_to_string [FG Blue, Bold] ("[ INFO @ " ^ lib_name ^ "] "))
                ^ msg
                ^ "\n"
        ) else ();
      fun debug msg = if !level_ref >= DEBUG then (
          print $ (add_style_to_string [FG BlueGreen, Bold] ("[DEBUG @ " ^ lib_name ^ "] "))
                ^ msg
                ^ "\n"
        ) else ();
      fun trace msg = if !level_ref >= TRACE then (
          print $ (add_style_to_string [FG Purple, Bold] ("[TRACE @ " ^ lib_name ^ "] "))
                ^ msg
                ^ "\n"
        ) else ();
    in
      {error=error, warn=warn, info=info, debug=debug, trace=trace}
    end;

  type fn_log_functions = {
    error: string -> string -> unit,
    warn : string -> string -> unit,
    info : string -> string -> unit,
    debug: string -> string -> unit,
    trace: string -> string -> unit
  }
  fun gen_fn_log_fns lib_name level_ref =
    let
      fun error func_name msg = if !level_ref >= ERROR then (
          print $ (add_style_to_string [FG OrangeRed, Bold]
                  ("[ERROR @ " ^ lib_name ^ "::" ^ func_name ^ "] "))
                ^ (add_style_to_string [FG OrangeRed] msg)
                ^ "\n"
        ) else ();
      fun warn func_name msg = if !level_ref >= WARN then (
          print $ (add_style_to_string [FG Yellow, Bold]
                  ("[ WARN @ " ^ lib_name ^ "::" ^ func_name ^ "] "))
                ^ msg
                ^ "\n"
        ) else ();
      fun info func_name msg = if !level_ref >= INFO then (
          print $ (add_style_to_string [FG Blue, Bold]
                  ("[ INFO @ " ^ lib_name ^ "::" ^ func_name ^ "] "))
                ^ msg
                ^ "\n"
        ) else ();
      fun debug func_name msg = if !level_ref >= DEBUG then (
          print $ (add_style_to_string [FG BlueGreen, Bold]
                  ("[DEBUG @ " ^ lib_name ^ "::" ^ func_name ^ "] "))
                ^ msg
                ^ "\n"
        ) else ();
      fun trace func_name msg = if !level_ref >= TRACE then (
          print $ (add_style_to_string [FG Purple, Bold]
                  ("[TRACE @ " ^ lib_name ^ "::" ^ func_name ^ "] "))
                ^ msg
                ^ "\n"
        ) else ();
    in
      {error=error, warn=warn, info=info, debug=debug, trace=trace}
    end;

end (* logLib *)
