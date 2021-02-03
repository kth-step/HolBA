open HolKernel Parse boolLib bossLib;

open Json;

(* remove testing database file before testing *)
(* ======================================================================= *)
val embexp_logs_dir =
  case OS.Process.getEnv ("HOLBA_EMBEXP_LOGS") of
     SOME x => x
   | NONE   => raise Fail "cannot find holba embexp logs directory variable";

val logsdb_file = embexp_logs_dir ^ "/data/testing.db";

val r = OS.Process.system ("rm \"" ^ logsdb_file ^ "\"");


(* prepare some testing infrastructure *)
(* ======================================================================= *)
fun assert_w_descr descr f = (
  print ("asserting: \"" ^ descr ^ "\"\n");
  if f () then print ("OK\n") else
  raise Fail ("assert failed"));

fun json_eq v1 v2 =
  case (v1, v2) of
     (OBJECT xs, OBJECT ys) => Portable.list_eq
          (Portable.pair_eq (fn x => fn y => x = y) json_eq) xs ys
   | (ARRAY  xs, ARRAY  ys) => Portable.list_eq json_eq xs ys
   | (NUMBER x , NUMBER y ) => (Arbnum.compare (x,y) = EQUAL)
   | (STRING x , STRING y ) => x = y
   | (BOOL   x , BOOL   y ) => x = y
   | (NULL     , NULL     ) => true
   | _ => false;

datatype json_int =
    JI_OBJECT of (string * json_int) list
  | JI_ARRAY of json_int list
  | JI_NUMBER of int
  | JI_STRING of string
  | JI_BOOL of bool
  | JI_NULL;

fun pair_eq_s eq_f_a eq_f_b (a1,b1) (a2,b2) =
  eq_f_a a1 a2 andalso
  eq_f_b b1 b2;

fun list_eq_s eq_f [] [] = true
  | list_eq_s eq_f (x::xs) (y::ys) = eq_f x y andalso list_eq_s eq_f xs ys
  | list_eq_s _ _ _ = false;

fun json_int_eq v1 v2 =
  case (v1, v2) of
     (OBJECT xs, JI_OBJECT ys) => list_eq_s
          (pair_eq_s (fn x => fn y => x = y) json_int_eq) xs ys
   | (ARRAY  xs, JI_ARRAY  ys) => list_eq_s json_int_eq xs ys
   | (NUMBER x , JI_NUMBER y ) => (Arbnum.toInt x) = y
   | (STRING x , JI_STRING y ) => x = y
   | (BOOL   x , JI_BOOL   y ) => x = y
   | (NULL     , JI_NULL     ) => true
   | _ => false;

fun fromJsonStr s =
  case Json.parse s of
     Json.ERROR e =>
       raise Fail ("script::fromJsonStr::error parsing the json output: " ^ e)
   | Json.OK json =>
       json;

(* prepare python db interface infrastructure *)
(* ======================================================================= *)
val command = embexp_logs_dir ^ "/scripts/db-interface.py";

fun run_db ops arg =
  bir_json_execLib.call_json_exec (command, ["-t", ops], arg);

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


(* make sure that all tables are cleared as expected,
     according to the logsdb version *)
(* ======================================================================= *)
val _ = List.map (fn (table,l) =>
  assert_w_descr
    ("length(" ^ table ^ ") = " ^ (Int.toString l))
    (fn () => (length o get_db_q_a o run_db_q_table) table = l)
) [("holba_runs",              0),
   ("holba_runs_meta",         0),
   ("exp_progs",               0),
   ("exp_progs_meta",          0),
   ("exp_exps",                0),
   ("exp_exps_meta",           0),
   ("exp_progs_lists",         0),
   ("exp_progs_lists_entries", 0),
   ("exp_exps_lists",          0),
   ("exp_exps_lists_entries",  0),
   ("db_meta",                 1)];

val db_meta_expect = JI_ARRAY [JI_ARRAY [JI_NUMBER 0, JI_STRING "logsdb", JI_STRING "version", JI_STRING "1"]];
val _ =
  assert_w_descr
    "db_meta version 1 only"
    (fn () => json_int_eq
                ((get_db_q o run_db_q_table) "db_meta")
                db_meta_expect);


(* run tests *)
(* ======================================================================= *)
open embexp_logsLib;
(* IMPORTANT: work on the testing db *)
val _ = embexp_logsLib.set_testing();


fun assert_w_descr descr f = (
  print ("asserting: \"" ^ descr ^ "\"\n");
  if f () then print ("OK\n") else
  raise Fail ("run_testing::assert failed: " ^ descr));

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

val _ = add_to_prog_list (prog_list_3, prog_1, 3);
val _ = add_to_exp_list (exp_list_2, exp_1, 5);

val _ =
  assert_w_descr
    "match for prog and exp entries result in no unique constraint exception"
    (fn () => (add_to_prog_list (prog_list_3, prog_1, 3);
               add_to_exp_list (exp_list_2, exp_1, 5);
               true));

(* add entries to lists *)
val _ = add_to_prog_list (prog_list_2, prog_1, 1);
val _ = add_to_prog_list (prog_list_2, prog_1, 1);
val _ = add_to_exp_list  (exp_list_2,  exp_1, 5);
val _ = add_to_exp_list  (exp_list_2,  exp_1, 5);


val meta_val_1 = "very important\n";
val meta_val_2 = "very important add\n";

val meta_id_run_1  = mk_run_meta_handle  (holba_run_1, SOME "all", "run meta 1");
val meta_id_prog_1 = mk_prog_meta_handle (prog_1,      SOME "all", "prog meta 1");
val meta_id_exp_1  = mk_exp_meta_handle  (exp_1,       SOME "all", "exp meta 1");

val _ =
  assert_w_descr
    "append without init run metadata"
    (fn () => (append_meta meta_id_run_1  (meta_val_1); false)
              handle _ => true);
val _ =
  assert_w_descr
    "append without init prog metadata"
    (fn () => (append_meta meta_id_prog_1 (meta_val_1); false)
              handle _ => true);
val _ =
  assert_w_descr
    "append without init exp metadata"
    (fn () => (append_meta meta_id_exp_1  (meta_val_1); false)
              handle _ => true);

val _ = init_meta meta_id_run_1  (SOME meta_val_1);
val _ = init_meta meta_id_prog_1 (SOME meta_val_1);
val _ = init_meta meta_id_exp_1  (SOME meta_val_1);

val _ =
  assert_w_descr
    "cannot init twice (no matching) - run metadata"
    (fn () => (init_meta meta_id_run_1  (SOME meta_val_1); false)
              handle _ => true);
val _ =
  assert_w_descr
    "cannot init twice (no matching) - prog metadata"
    (fn () => (init_meta meta_id_prog_1 (SOME meta_val_1); false)
              handle _ => true);
val _ =
  assert_w_descr
    "cannot init twice (no matching) - exp metadata"
    (fn () => (init_meta meta_id_exp_1  (SOME meta_val_1); false)
              handle _ => true);

val _ = append_meta meta_id_run_1  meta_val_2;
val _ = append_meta meta_id_prog_1 meta_val_2;
val _ = append_meta meta_id_prog_1 meta_val_2;
val _ = append_meta meta_id_exp_1  meta_val_2;

val meta_val_3 = "beta\n";

val meta_id_run_2  = mk_run_meta_handle (holba_run_1, SOME "ahaa", "meta null 1");
val meta_id_run_3  = mk_run_meta_handle (holba_run_1, NONE, "meta list 1");

val _ = init_meta meta_id_run_2 NONE;
val _ = init_meta meta_id_run_3 (SOME meta_val_3)

val _ =
  assert_w_descr
    "appending metadata requires kind to be SOME"
    (fn () => (append_meta meta_id_run_3 meta_val_3; false)
              handle _ => true);

val _ = init_meta meta_id_run_3 (SOME meta_val_3);
val _ = init_meta meta_id_run_3 (SOME meta_val_3);


(* tests for retrieval *)
val prog_l_ids = query_all_prog_lists ();
val prog_ls = get_prog_lists prog_l_ids;

val listname = "hello progs 3";

val (_, prog_ls_) = List.foldl (fn (x, (i, l)) => (i+1, ((i, x))::l)) (0, []) prog_ls;
val prog_ls_filt = List.filter (fn (_, LogsList (n, _)) => n = listname) prog_ls_;
val (i, _) = if List.length prog_ls_filt = 1 then hd prog_ls_filt else
             raise Fail ("didn't find exactly one match for prog list " ^ listname);
val prog_l_id = List.nth (prog_l_ids, i);

val prog_ids = List.map snd (get_prog_list_entries prog_l_id);

val progs = get_progs prog_ids;



(* try persistenceLib directly *)
open persistenceLib;
open experimentsLib;

val prog_v_10 = mk_experiment_prog ["asm line 1", "asm line 2"];
val prog_v_10_m = [("meta100", "20"), ("meta23", "abc")];

fun gen_prog_10 () = run_create_prog ArchARM8 prog_v_10 prog_v_10_m;
val prog_10 = gen_prog_10 ();

val _ =
  assert_w_descr
    "can generate the same program with same metadata multiple times, get same handle"
    (fn () => (gen_prog_10 () = prog_10));

val exp_v_10_m = [("meta100", "20"), ("meta23", "abc")];;
fun gen_exp_10 () = run_create_exp prog_10 ExperimentTypeStdTwo "exp_params" [("input a", experimentsLib.machstate_empty (Arbnum.fromInt 125))] exp_v_10_m;
val exp_10 = gen_exp_10 ();

val _ =
  assert_w_descr
    "can generate the same experiment with same metadata multiple times, get same handle"
    (fn () => (gen_exp_10 () = exp_10));

(* log something *)
val _ = run_log_prog "prog log 1";
val _ = run_log_exp  "exp log 1";
val _ = run_log      "run log 1";
val _ = run_log      "run log 2";
val _ = run_log_prog "prog log 2";
val _ = run_log_exp  "exp log 2";

(* finalize the whole run *)
val _ = run_finalize ();

(* find some programs *)
val prog_code_l = List.map (experimentsLib.prog_to_asm_code) (runlogs_load_progs "hello progs 3");

val _ =
  assert_w_descr
    "find the program from before"
    (fn () => (prog_code_l = ["\tpush all\n"]));
