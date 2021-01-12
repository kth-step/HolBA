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
  bir_json_execLib.call_json_exec (command ^ (if !is_testing then " -t" else "")) ops arg;

val run_db_q = run_db "query";
fun run_db_q_table t = run_db_q (
  OBJECT
    [("type", STRING "match_simple"),
     ("query",
      OBJECT
       [("table", STRING t),
        ("values", OBJECT [])])]);
fun get_db_q r =
  case r of
     OBJECT [("fields", ARRAY _), ("rows", subjson)] => subjson
   | _ => raise Fail "scanned result does not match a query response";
fun get_db_q_a r =
  case get_db_q r of
     ARRAY xs => xs
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

fun run_db_c_irgnore do_match t vs =
      (run_db_c (
         OBJECT
           [("table", STRING t),
            ("values", OBJECT vs),
            ("id_only", BOOL false),
            ("match_existing", BOOL do_match)]);
       ());

val run_db_a = run_db "append";
fun run_db_a_irgnore t vs =
  case run_db_a (
         OBJECT
           [("table", STRING t),
            ("values", OBJECT vs)]) of
     BOOL true => ()
   | _ => raise ERR "run_db_a_irgnore" "unexpected output";

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
  datatype logs_meta = LogsMeta of (string option * string * string option);


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

  fun create_run (LogsRun (time, prog_l_id, exp_l_id)) =
    run_db_c_id false
      "holba_runs"
      [("time", STRING time),
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
    run_db_c_irgnore true
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
  fun init__metadata (t, f_id) x_id (LogsMeta (k_o, n, v_o)) =
    run_db_c_irgnore false
      t
      [(f_id,    NUMBER x_id),
       ("kind",  Option.getOpt(Option.map STRING k_o, NULL)),
       ("name",  STRING n),
       ("value", Option.getOpt(Option.map STRING v_o, NULL))];
  fun append__metadata (t, f_id) x_id (LogsMeta (k_o, n, v_o)) =
    run_db_a_irgnore
      t
      [(f_id,    NUMBER x_id),
       ("kind",  Option.getOpt(Option.map STRING k_o, NULL)),
       ("name",  STRING n),
       ("value", Option.getOpt(Option.map STRING v_o, NULL))];

  fun init_run_metadata    run_id  lmd =
    init__metadata
      ("holba_runs_meta", "holba_runs_id")
      run_id
      lmd;
  fun init_prog_metadata   prog_id lmd =
    init__metadata
      ("exp_progs_meta", "exp_progs_id")
      prog_id
      lmd;
  fun init_exp_metadata    exp_id  lmd =
    init__metadata
      ("exp_exps_meta", "exp_exps_id")
      exp_id
      lmd;

  fun append_run_metadata  run_id  lmd =
    append__metadata
      ("holba_runs_meta", "holba_runs_id")
      run_id
      lmd;
  fun append_prog_metadata prog_id lmd =
    append__metadata
      ("exp_progs_meta", "exp_progs_id")
      prog_id
      lmd;
  fun append_exp_metadata  exp_id  lmd =
    append__metadata
      ("exp_exps_meta", "exp_exps_id")
      exp_id
      lmd;


  fun run_testing () =
    let
      val _ = if !is_testing then () else
              raise ERR "run_testing" "not in testing mode";

fun assert_w_descr descr f = (
  print ("asserting: \"" ^ descr ^ "\"\n");
  if f () then print ("OK\n") else
  raise ERR "run_testing" ("assert failed"));

val lld_p_1 = LogsList ("progs__", NONE);
val lld_p_2 = LogsList ("hello progs 3", NONE);
val lld_p_3 = LogsList ("hello progs 4", SOME "amazing progs description 4");
val lld_e_1 = LogsList ("hello", NONE);
val lld_e_2 = LogsList ("hello 2", SOME "amazing description 2");

val prog_list_1 = create_prog_list lld_p_1;
val prog_list_2 = create_prog_list lld_p_2;
val prog_list_3 = create_prog_list lld_p_3;
val exp_list_1  = create_exp_list  lld_e_1;
val exp_list_2  = create_exp_list  lld_e_2;

val _ =
  assert_w_descr
    "no match for prog list"
    (fn () => (create_prog_list lld_p_3; false)
              handle _ => true);
val _ =
  assert_w_descr
    "no match for exp list"
    (fn () => (create_exp_list lld_e_1; false)
              handle _ => true);

val holba_run_d_1 = LogsRun ("a time long ago 1", prog_list_3, exp_list_2);
val holba_run_1 = create_run holba_run_d_1;
val _ =
  assert_w_descr
    "no match for holba run"
    (fn () => (create_run holba_run_d_1; false)
              handle _ => true);

val prog_d_1 = LogsProg ("arm22", "\tpush all\n");
val prog_1 = create_prog prog_d_1;
val exp_d_1  = LogsExp (prog_1, "exps0", "no args", OBJECT [("inputs", NULL)]);
val exp_1  = create_exp  exp_d_1;

val _ =
  assert_w_descr
    "match for prog and exp result in the same handle again"
    (fn () => (create_prog prog_d_1 = prog_1) andalso (create_exp  exp_d_1 = exp_1));

val _ = add_to_prog_list (prog_list_3, prog_1);
val _ = add_to_exp_list (exp_list_2, exp_1);

val _ =
  assert_w_descr
    "match for prog and exp entries result in no unique constraint exception"
    (fn () => (add_to_prog_list (prog_list_3, prog_1);
               add_to_exp_list (exp_list_2, exp_1);
               true));

val run_m_1  = LogsMeta(SOME "all", "run meta 1",  SOME "very important\n");
val prog_m_1 = LogsMeta(SOME "all", "prog meta 1", SOME "very important\n");
val exp_m_1  = LogsMeta(SOME "all", "exp meta 1",  SOME "very important\n");

val run_m_2  = LogsMeta(SOME "all", "run meta 1",  SOME "very important add\n");
val prog_m_2 = LogsMeta(SOME "all", "prog meta 1", SOME "very important add\n");
val exp_m_2  = LogsMeta(SOME "all", "exp meta 1",  SOME "very important add\n");

val _ =
  assert_w_descr
    "append without init run metadata"
    (fn () => (append_run_metadata holba_run_1 run_m_1; false)
              handle _ => true);
val _ =
  assert_w_descr
    "append without init prog metadata"
    (fn () => (append_prog_metadata prog_1 prog_m_1; false)
              handle _ => true);
val _ =
  assert_w_descr
    "append without init exp metadata"
    (fn () => (append_exp_metadata exp_1 exp_m_1; false)
              handle _ => true);

val _ = init_run_metadata  holba_run_1 run_m_1;
val _ = init_prog_metadata prog_1      prog_m_1;
val _ = init_exp_metadata  exp_1       exp_m_1;

val _ =
  assert_w_descr
    "cannot init twice - run metadata"
    (fn () => (init_run_metadata holba_run_1 run_m_1; false)
              handle _ => true);
val _ =
  assert_w_descr
    "cannot init twice - prog metadata"
    (fn () => (init_prog_metadata prog_1 prog_m_1; false)
              handle _ => true);
val _ =
  assert_w_descr
    "cannot init twice - exp metadata"
    (fn () => (init_exp_metadata exp_1 exp_m_1; false)
              handle _ => true);

val _ = append_run_metadata  holba_run_1 run_m_2;
val _ = append_prog_metadata prog_1      prog_m_2;
val _ = append_prog_metadata prog_1      prog_m_2;
val _ = append_exp_metadata  exp_1       exp_m_2;

val run_m_3  = LogsMeta(SOME "ahaa", "meta null 1",  NONE);
val run_m_4  = LogsMeta(NONE, "meta list 1",  SOME "beta\n");
val _ = init_run_metadata  holba_run_1 run_m_3;
val _ = init_run_metadata  holba_run_1 run_m_4;

val _ =
  assert_w_descr
    "cannot append metadata if value is set to NONE"
    (fn () => (append_run_metadata  holba_run_1 run_m_3; false)
              handle _ => true);

val _ =
  assert_w_descr
    "appending metadata requires kind to be SOME"
    (fn () => (append_run_metadata  holba_run_1 run_m_4; false)
              handle _ => true);

val _ = init_run_metadata  holba_run_1 run_m_4;
val _ = init_run_metadata  holba_run_1 run_m_4;

    in () end;




end (* local *)
end (* struct *)
