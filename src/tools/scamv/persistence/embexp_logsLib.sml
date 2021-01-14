structure embexp_logsLib :> embexp_logsLib =
struct
local
  val ERR = Feedback.mk_HOL_ERR "embexp_logsLib"
  val wrap_exn = Feedback.wrap_exn "embexp_logsLib"

  open bir_json_execLib;
  open Json;
in

val is_testing = ref false;

fun set_testing () =
  is_testing := true;

(* ==================================================== *)

val embexp_logs_dir =
  case OS.Process.getEnv ("HOLBA_EMBEXP_LOGS") of
     SOME x => x
   | NONE   => raise Fail "cannot find holba embexp logs directory variable";

val command = embexp_logs_dir ^ "/scripts/db-interface.py";

fun run_db ops arg =
  bir_json_execLib.call_json_exec (command, (if !is_testing then ["-t"] else [])@[ops], arg);

val run_db_q = run_db "query";
fun run_db_q_gen id_only t vs = run_db_q (
  OBJECT
    [("type", STRING "match_simple"),
     ("query",
      OBJECT
       [("table", STRING t),
        ("values", OBJECT vs),
        ("id_only", BOOL id_only)])]);
fun run_db_q_all id_only t =
  run_db_q_gen id_only t [];
fun get_db_q r =
  case r of
     OBJECT [("fields", ARRAY fs), ("rows", ARRAY xs)] => (fs, xs)
   | _ => raise Fail "scanned result does not match a query response";

val run_db_c = run_db "create";
fun run_db_c_map id_only do_match t vs =
      run_db_c (
         OBJECT
           [("table", STRING t),
            ("values", OBJECT vs),
            ("id_only", BOOL id_only),
            ("match_existing", BOOL do_match)]);

fun run_db_c_id do_match t vs =
  case run_db_c_map true do_match t vs of
     OBJECT [(n, NUMBER i)] =>
       if n = "id" then i else
       raise ERR "run_db_c_id" "unexpected output"
   | _ => raise ERR "run_db_c_id" "unexpected output";

fun run_db_c_ignore do_match t vs =
      (run_db_c (
         OBJECT
           [("table", STRING t),
            ("values", OBJECT vs),
            ("id_only", BOOL false),
            ("match_existing", BOOL do_match)]);
       ());

val run_db_a = run_db "append";
fun run_db_a_ignore t vs =
  case run_db_a (
         OBJECT
           [("table", STRING t),
            ("values", OBJECT vs)]) of
     BOOL true => ()
   | _ => raise ERR "run_db_a_ignore" "unexpected output";

(* ==================================================== *)

  type prog_list_handle = Arbnum.num;
  type exp_list_handle = Arbnum.num;
  type run_handle = Arbnum.num;
  type prog_handle = Arbnum.num;
  type exp_handle = Arbnum.num; 

  datatype logs_list = LogsList of (string * string option);
  datatype logs_run  = LogsRun  of (string * prog_list_handle * exp_list_handle);
  datatype logs_prog = LogsProg of (string * string);
  datatype logs_exp  = LogsExp  of (prog_handle * string * string * Json.json);

  datatype meta_type = MetaTypeRun | MetaTypeProg | MetaTypeExp;
  type meta_handle   = meta_type * (Arbnum.num * string option * string);
  datatype logs_meta = LogsMeta of (meta_handle * string option);

(*
*)
  fun prog_list_handle_toString id = "(ProgList, id=" ^ (Arbnum.toString id) ^ ")";
  fun exp_list_handle_toString  id = "(ExpList, id="  ^ (Arbnum.toString id) ^ ")";
  fun run_handle_toString       id = "(Run, id="      ^ (Arbnum.toString id) ^ ")";
  fun prog_handle_toString      id = "(Prog, id="     ^ (Arbnum.toString id) ^ ")";
  fun exp_handle_toString       id = "(Exp, id="      ^ (Arbnum.toString id) ^ ")";

  fun meta_type_toString MetaTypeRun  = "MetaRun"
    | meta_type_toString MetaTypeProg = "MetaProg"
    | meta_type_toString MetaTypeExp  = "MetaExp";
  fun meta_handle_toString      (metaty, (id, k_o, n)) =
    "("       ^ (meta_type_toString metaty) ^
    ", id="   ^ (Arbnum.toString id) ^
    ", kind=" ^ (Option.getOpt (k_o, "NULL")) ^
    ", name=" ^ n ^ ")";


(*
*)
  fun mk_run_meta_handle  (run_id , k_o, n) = (MetaTypeRun,  (run_id,  k_o, n));
  fun mk_prog_meta_handle (prog_id, k_o, n) = (MetaTypeProg, (prog_id, k_o, n));
  fun mk_exp_meta_handle  (exp_id , k_o, n) = (MetaTypeExp,  (exp_id,  k_o, n));


(*
*)
  fun create__list t (LogsList (n,d_o)) =
    run_db_c_id false
      t
      [("name",        STRING n),
       ("description", Option.getOpt(Option.map STRING d_o, NULL))];

  fun create_prog_list lld =
      create__list "exp_progs_lists" lld;
  fun create_exp_list lld =
      create__list "exp_exps_lists" lld;

  fun create_run (LogsRun (name, prog_l_id, exp_l_id)) =
    run_db_c_id false
      "holba_runs"
      [("name", STRING name),
       ("exp_progs_lists_id", NUMBER prog_l_id),
       ("exp_exps_lists_id",  NUMBER exp_l_id)];
  fun create_prog (LogsProg (arch, code)) =
    run_db_c_id true
      "exp_progs"
      [("arch",               STRING arch),
       ("code",               STRING code)];
  fun create_exp (LogsExp (prog_id, exp_type, exp_params, input_data)) =
    run_db_c_id true
      "exp_exps"
      [("exp_progs_id",       NUMBER prog_id),
       ("type",               STRING exp_type),
       ("params",             STRING exp_params),
       ("input_data",         STRING (Json.serialise input_data))];


(*
*)
  fun add_to__list (t, f1, f2) (l_id, x_id) =
    run_db_c_ignore true
      t
      [(f1, NUMBER l_id),
       (f2, NUMBER x_id)];

  fun add_to_prog_list le_d =
    add_to__list 
    ("exp_progs_lists_entries", "exp_progs_lists_id", "exp_progs_id")
    le_d;
  fun add_to_exp_list  le_d =
    add_to__list 
    ("exp_exps_lists_entries", "exp_exps_lists_id", "exp_exps_id")
    le_d;


(*
*)
  fun init__meta (t, f_id) (x_id, k_o, n) v_o =
    run_db_c_ignore false
      t
      [(f_id,    NUMBER x_id),
       ("kind",  Option.getOpt(Option.map STRING k_o, NULL)),
       ("name",  STRING n),
       ("value", Option.getOpt(Option.map STRING v_o, NULL))];
  fun append__meta (t, f_id) (x_id, k_o, n) v =
    run_db_a_ignore
      t
      [(f_id,    NUMBER x_id),
       ("kind",  Option.getOpt(Option.map STRING k_o, NULL)),
       ("name",  STRING n),
       ("value", STRING v)];

  local
    fun metaty_to_db MetaTypeRun  = ("holba_runs_meta", "holba_runs_id")
      | metaty_to_db MetaTypeProg = ("exp_progs_meta", "exp_progs_id")
      | metaty_to_db MetaTypeExp  = ("exp_exps_meta", "exp_exps_id");
  in
    fun init_meta   (metaty, lmd) = init__meta   (metaty_to_db metaty) lmd;
    fun append_meta (metaty, lmd) = append__meta (metaty_to_db metaty) lmd;
  end;


(*
*)
  (* TODO: change to not ignore the fields in the result *)
  fun get_from_id (t, f_id) unpack_fun id =
    case get_db_q (run_db_q_gen false t [(f_id, NUMBER id)]) of
       (_, [x]) => (case x of
               ARRAY vals => unpack_fun vals
             | _ => raise ERR "get_all_ids" "result not as expected")
     | _ => raise ERR "get_all_ids" "result not as expected";
  fun get_from_id_mult (t, f_id) unpack_fun id =
    case get_db_q (run_db_q_gen false t [(f_id, NUMBER id)]) of
       (_, xs) => List.map (fn x => case x of
               ARRAY vals => unpack_fun vals
             | _ => raise ERR "get_all_ids_mult" "result not as expected") xs;

  fun get_from_ids (t, f_id) unpack_fun ids = List.map (fn id => get_from_id (t, f_id) unpack_fun id) ids;

  fun unpack_json s =
    case Json.parse s of
       Json.ERROR e =>
         raise ERR "unpack_json" ("result not as expected, json error: " ^ e)
     | Json.OK json =>
         json;

  fun unpack_string_opt x =
    case x of
       STRING x => SOME x
     | NULL => NONE
     | _ => raise ERR "unpack_string_opt" "result not as expected";

  fun unpack_logs_list x =
    case x of
       [NUMBER _, STRING n, json_d_o] => LogsList (n, unpack_string_opt json_d_o)
     | _ => raise ERR "unpack_logs_list" "result not as expected";

  fun unpack_logs_run x =
    case x of
       [NUMBER _, STRING n, NUMBER pl_id, NUMBER el_id] => LogsRun (n, pl_id, el_id)
     | _ => raise ERR "unpack_logs_run" "result not as expected";

  fun unpack_logs_prog x =
    case x of
       [NUMBER _, STRING a, STRING c] => LogsProg (a, c)
     | _ => raise ERR "unpack_logs_prog" "result not as expected";

  fun unpack_logs_exp x =
    case x of
       [NUMBER _, NUMBER p_id, STRING ty, STRING pa, STRING indat] =>
          LogsExp (p_id, ty, pa, unpack_json indat)
     | _ => raise ERR "unpack_logs_exp" "result not as expected";

  fun unpack_list_entry x =
    case x of
       [NUMBER _, NUMBER mem_id] => mem_id
     | _ => raise ERR "unpack_list_entry" "result not as expected";

  fun get_prog_lists ids =
    get_from_ids
      ("exp_progs_lists", "id")
      unpack_logs_list
      ids;
  fun get_exp_lists  ids =
    get_from_ids
      ("exp_exps_lists", "id")
      unpack_logs_list
      ids;

  fun get_runs  ids =
    get_from_ids
      ("holba_runs", "id")
      unpack_logs_run
      ids;
  fun get_progs ids =
    get_from_ids
      ("exp_progs", "id")
      unpack_logs_prog
      ids;
  fun get_exps  ids =
    get_from_ids
      ("exp_exps", "id")
      unpack_logs_exp
      ids;

  fun get_prog_list_entries id =
    get_from_id_mult
      ("exp_progs_lists_entries", "exp_progs_lists_id")
      unpack_list_entry
      id;
  fun get_exp_list_entries  id =
    get_from_id_mult
      ("exp_exps_lists_entries", "exp_exps_lists_id")
      unpack_list_entry
      id;

(*
*)
(*
  (* retrieval of metdata *)
  val get_run_metadata    : run_handle  -> logs_meta list;
  val get_prog_metadata   : prog_handle -> logs_meta list;
  val get_exp_metadata    : exp_handle  -> logs_meta list;
*)


(*
*)
  fun get_all_ids t =
    case get_db_q (run_db_q_all true t) of
       ([STRING s_id], jsonids)
         => if s_id = "id" then List.map (fn x => case x of
                ARRAY [NUMBER i] => i | _ => raise ERR "get_all_ids" "result not as expected") jsonids else
            raise ERR "get_all_ids" "result not as expected"
     | _ => raise ERR "get_all_ids" "result not as expected";

  fun query_all_prog_lists () = get_all_ids "exp_progs_lists";
  fun query_all_exp_lists  () = get_all_ids "exp_exps_lists";


end (* local *)
end (* struct *)
