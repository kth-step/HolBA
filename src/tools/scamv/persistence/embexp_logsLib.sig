signature embexp_logsLib =
sig

  eqtype prog_list_handle;
  eqtype exp_list_handle;
  eqtype run_handle;
  eqtype prog_handle;
  eqtype exp_handle;

  datatype logs_list = LogsList of (string * string option);
  datatype logs_run  = LogsRun  of (string * prog_list_handle * exp_list_handle);
  datatype logs_prog = LogsProg of (string * string);
  datatype logs_exp  = LogsExp  of (prog_handle * string * string * Json.json * Arbnum.num * Json.json);

  eqtype meta_handle;
  datatype logs_meta = LogsMeta of (meta_handle * string option);

  val embexp_logs_dir : unit -> string;

  (* operations on handles *)
  val prog_handle_compare : (prog_handle * prog_handle) -> order;
  val exp_handle_compare  : (exp_handle  * exp_handle ) -> order;

  (* readable representation of handles *)
  val prog_list_handle_toString : prog_list_handle -> string;
  val exp_list_handle_toString  : exp_list_handle  -> string;
  val run_handle_toString       : run_handle       -> string;
  val prog_handle_toString      : prog_handle      -> string;
  val exp_handle_toString       : exp_handle       -> string;
  val meta_handle_toString      : meta_handle      -> string;


  (* make metadata handles *)
  val mk_run_meta_handle  : (run_handle  * string option * string) -> meta_handle;
  val mk_prog_meta_handle : (prog_handle * string option * string) -> meta_handle;
  val mk_exp_meta_handle  : (exp_handle  * string option * string) -> meta_handle;
  (* decompose metadata handles *)
  val dest_run_meta_handle  : meta_handle -> (run_handle  * string option * string);
  val dest_prog_meta_handle : meta_handle -> (prog_handle * string option * string);
  val dest_exp_meta_handle  : meta_handle -> (exp_handle  * string option * string);

  (* creation of basic entries *)
  val create_prog_list : logs_list -> prog_list_handle;
  val create_exp_list  : logs_list -> exp_list_handle;

  val create_run  : logs_run  -> run_handle;
  val create_prog : logs_prog -> prog_handle;
  val create_exp  : logs_exp  -> exp_handle;

  (* adding progs/exps to corresponding lists *)
  val add_to_prog_list : (prog_list_handle * prog_handle * int) -> unit;
  val add_to_exp_list  : (exp_list_handle  * exp_handle  * int) -> unit;

  (* adding metadata *)
  val init_meta    : meta_handle -> string option -> unit;
  val append_meta  : meta_handle -> string -> unit;


  (* retrieval of basic entries *)
  val get_prog_lists : prog_list_handle list -> logs_list list;
  val get_exp_lists  : exp_list_handle  list -> logs_list list;

  val get_runs  : run_handle  list -> logs_run  list;
  val get_progs : prog_handle list -> logs_prog list;
  val get_exps  : exp_handle  list -> logs_exp  list;

  (* retrieval of progs/exps from lists *)
  val get_prog_list_entries : prog_list_handle -> (int * prog_handle) list;
  val get_exp_list_entries  : exp_list_handle  -> (int * exp_handle ) list;

  (* retrieval of list of whole entries *)
  val get_prog_list_entries_full : prog_list_handle -> (int * logs_prog) list;
  val get_exp_list_entries_full  : exp_list_handle  -> (int * logs_exp ) list;

  (* retrieval of metdata *)
  val get_run_metadata    : run_handle  -> logs_meta list;
  val get_prog_metadata   : prog_handle -> logs_meta list;
  val get_exp_metadata    : exp_handle  -> logs_meta list;

  (* retrieval of some data *)
  val get_cexamples : string -> string list option
  val get_exps_outside : Arbnum.num list -> logs_exp list

  (* queries *)
  val query_all_prog_lists : unit -> prog_list_handle list;
  val query_all_exp_lists  : unit -> exp_list_handle  list;

(*
  val query_match_runs  : (string option *
                           prog_list_handle option *
                           exp_list_handle option) list
                          -> run_handle  list;
  val query_match_progs : (string option *
                           string option)
                          -> prog_handle list;
  val query_match_exps  : (prog_handle option *
                           string option *
                           string option *
                           Json.json option) list
                          -> exp_handle  list;
*)

  (*
    most general query with raw input and raw output.
    - ! it deliberately doesn't return handles so that links in the db cannot be messed up !
    - the returned json values are of one of the following types: NULL, NUMBER, STRING
  *)
  val query_sql : string -> (string list * Json.json list list);


  (* function to enable the testing mode, i.e., uses the testing db *)
  val set_testing : unit -> unit;

end
