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

val _ = embexp_logsLib.set_testing();
val _ = embexp_logsLib.run_testing();
