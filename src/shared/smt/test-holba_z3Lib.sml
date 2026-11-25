open HolKernel Parse;

open holba_z3Lib;

(* The queries are run with the three protocols of holba_z3Lib:
   non-incremental, incremental, and incremental with the fallback to the
   non-incremental solver, the default. Every query declares its constants,
   so that a query fails if the declarations of a previous query are still
   there. *)

fun check name b =
  if b then print ("ok: " ^ name ^ "\n") else
  raise Fail ("test-holba_z3Lib: " ^ name);

val _ = check "the default protocol is the incremental one with the fallback"
          (!z3_protocol = Z3IncrementalFallback);

val q_sat = "(declare-const x (_ BitVec 8))\n(assert (= x #xFF))\n";
val q_unsat = "(declare-const x (_ BitVec 8))\n(assert (= x #xAA))\n(assert (= x #xFF))\n";

(* queries with the load and store functions of the prelude *)
val q_mem =
  "(declare-const m (Array (_ BitVec 64) (_ BitVec 8)))\n" ^
  "(declare-const a (_ BitVec 64))\n" ^
  "(declare-const v (_ BitVec 32))\n";
val q_mem_unsat =
  q_mem ^ "(assert (not (= (loadfun_LE_64_8_32 (storefun_LE_64_8_32 m a v) a) v)))\n";
val q_mem_sat =
  q_mem ^ "(assert (= (loadfun_LE_64_8_16 m a) #x1234))\n(assert (= a #x0000000000000010))\n";

(* z3 does not answer it within 100 ms: it asks for the two 32-bit prime
   factors of a 64-bit number *)
val q_hard =
  "(declare-const a (_ BitVec 64))\n(declare-const b (_ BitVec 64))\n" ^
  "(assert (= (bvmul a b) #x571e7f8e7cd1aa2b))\n" ^
  "(assert (bvult a #x0000000100000000))\n(assert (bvult b #x0000000100000000))\n" ^
  "(assert (bvugt a #x0000000000000001))\n(assert (bvugt b #x0000000000000001))\n";

(* z3 reports an error: y is not declared *)
val q_error = "(assert (= y #xFF))\n";

(* solver2 of z3, its incremental solver, gives unknown for this query when
   it may not have any conflict, while solver1, the non-incremental one,
   answers it: the product of two numbers below 16 is 143 = 11 * 13 *)
val q_factors =
  "(declare-const a (_ BitVec 8))\n(declare-const b (_ BitVec 8))\n" ^
  "(assert (= (bvmul a b) #x8f))\n(assert (bvugt a #x01))\n" ^
  "(assert (bvult a b))\n(assert (bvult b #x10))\n";
fun without_conflicts q =
  "(set-option :smt.max_conflicts 0)\n" ^ q ^ "(set-option :smt.max_conflicts 4294967295)\n";

(* solver1 answers it at once, and solver2 not within seconds: no positive
   square is twice a square *)
val q_nonlinear =
  "(declare-const x Int)\n(declare-const y Int)\n" ^
  "(assert (<= 0 x 1000))\n(assert (<= 0 y 1000))\n" ^
  "(assert (> x 0))\n(assert (= (* x x) (* 2 y y)))\n";

fun get_value q v =
  querysmt_parse_getmodel (querysmt_raw NONE NONE (q ^ "(check-sat)\n(get-value (" ^ v ^ "))\n"));

(* the model of the wrapper has a line with the name and a line with the
   value of each constant *)
fun model_pairs (n :: v :: l) = (n, v) :: model_pairs l
  | model_pairs _ = [];

fun protocol_name Z3NonIncremental = "non-incremental"
  | protocol_name Z3Incremental = "incremental"
  | protocol_name Z3IncrementalFallback = "incremental with the fallback";

fun test_protocol protocol =
  let
    val _ = z3_protocol := protocol;
    fun chk name b = check (protocol_name protocol ^ ", " ^ name) b;

    (* the options of the fallback are set in the process of its protocol
       only, also after a restart *)
    val options_q =
      "(get-option :combined_solver.solver2_timeout)\n(get-option :combined_solver.solver2_unknown)\n";
    val options_expected =
      if protocol = Z3IncrementalFallback then ["10\n", "2\n"] else ["4294967295\n", "1\n"];
    fun chk_options_gen z3bin_o name = chk ("the options of the protocol " ^ name)
          (querysmt_raw z3bin_o NONE options_q = options_expected);
    val chk_options = chk_options_gen NONE;

    (* the first query after a change of the protocol needs the prelude *)
    val _ = chk "unsat with the prelude" (querysmt_checksat NONE q_mem_unsat = BirSmtUnsat);
    val _ = chk_options "after the change of the protocol";
    val _ = chk "sat with the prelude" (querysmt_checksat NONE q_mem_sat = BirSmtSat);
    val _ = chk "sat" (querysmt_checksat NONE q_sat = BirSmtSat);
    val _ = chk "unsat" (querysmt_checksat NONE q_unsat = BirSmtUnsat);

    (* models of z3 *)
    val _ = querysmt_prepare_getmodel NONE;
    val _ = chk "model" (get_value q_sat "x" = (BirSmtSat, ["((x #xff))"]));
    val _ = chk "model with the prelude"
              (get_value q_mem_sat "a" = (BirSmtSat, ["((a #x0000000000000010))"]));
    val _ = chk "no model for unsat" (get_value q_unsat "x" = (BirSmtUnsat, []));

    (* an unknown of solver2 is answered by solver1, also with a model *)
    val solver2_alone = querysmt_parse_checksat (querysmt_raw NONE NONE (without_conflicts (
          "(set-option :combined_solver.ignore_solver1 true)\n" ^ q_factors ^ "(check-sat)\n" ^
          "(set-option :combined_solver.ignore_solver1 false)\n")));
    val _ = chk "unknown of solver2 alone" (solver2_alone = BirSmtUnknown);
    val _ = chk "model of solver1 after an unknown of solver2"
              (querysmt_parse_getmodel (querysmt_raw NONE NONE (without_conflicts (
                 q_factors ^ "(check-sat)\n(get-value (a))\n(get-value (b))\n"))) =
               (BirSmtSat, ["((a #x0b))", "((b #x0d))"]));
    val _ = chk_options "after the unknown of solver2";

    (* models of the wrapper *)
    val _ = chk "model of the wrapper" (querysmt_getmodel q_sat = (BirSmtSat, ["x", "(0xFFw: 8 word)"]));
    val (res, model) = querysmt_getmodel q_mem_sat;
    val _ = chk "model of the wrapper with the prelude"
              (res = BirSmtSat andalso
               List.exists (fn x => x = ("a", "(0x10w: 64 word)")) (model_pairs model) andalso
               List.exists (fn (n, _) => n = "m") (model_pairs model));
    val _ = chk "no model of the wrapper for unsat" (querysmt_getmodel q_unsat = (BirSmtUnsat, []));

    (* an error of z3 fails the query, and the next query is answered *)
    val failed = (querysmt_checksat NONE q_error; false) handle HOL_ERR _ => true;
    val _ = chk "z3 error" failed;
    val _ = chk "sat after the z3 error" (querysmt_checksat NONE q_sat = BirSmtSat);

    (* a query that stops z3 fails, and the next query starts a new process *)
    val stopped = (querysmt_raw NONE NONE "(exit)\n"; false) handle Z3EXN _ => true;
    val _ = chk "z3 stopped by a query" stopped;
    val _ = chk_options "after z3 stopped";
    val _ = chk "sat after z3 stopped" (querysmt_checksat NONE q_mem_sat = BirSmtSat);

    (* a query that times out gives unknown, also with a timeout shorter
       than the time that the fallback gives solver2, and the timeout
       bounds the time of the query; the next query is answered *)
    val _ = querysmt_raw_query_times := SOME [];
    val _ = chk "timeout" (querysmt_checksat (SOME 100) q_hard = BirSmtUnknown);
    val _ = chk "timeout of 5 ms" (querysmt_checksat (SOME 5) q_hard = BirSmtUnknown);
    val times = valOf (!querysmt_raw_query_times);
    val _ = querysmt_raw_query_times := NONE;
    val _ = chk "the timeouts bound the time of the queries" (List.all (fn t => t < 5000) times);
    val _ = chk "unsat after the timeout" (querysmt_checksat NONE q_mem_unsat = BirSmtUnsat);
    val _ = chk "unsat with a timeout" (querysmt_checksat (SOME 10000) q_mem_unsat = BirSmtUnsat);

    (* with a timeout, the query that only solver1 answers soon is answered
       unless only solver2 runs *)
    val res = querysmt_checksat (SOME 2000) q_nonlinear;
    val _ = chk "unsat by solver1 with a timeout, or unknown with only solver2"
              (res = BirSmtUnsat orelse (protocol = Z3Incremental andalso res = BirSmtUnknown));

    (* with querysmt_raw_unknown_as_timeout, unknown restarts z3 and retries
       the query, and raises Z3TIMEOUT after the last retry *)
    val _ = querysmt_raw_retries := 2;
    val _ = querysmt_raw_unknown_as_timeout := true;
    val timed_out = (querysmt_checksat (SOME 100) q_hard; false) handle Z3TIMEOUT _ => true;
    val _ = querysmt_raw_retries := 0;
    val _ = querysmt_raw_unknown_as_timeout := false;
    val _ = chk "timeout after the retries" timed_out;
    val _ = chk_options "after the retries";
    val _ = chk "unsat after the retries" (querysmt_checksat NONE q_mem_unsat = BirSmtUnsat);

    (* another z3 binary, here another path of the same one, restarts z3 *)
    val z3bin = get_default_z3 ();
    val _ = if not (OS.Path.isAbsolute z3bin) then print "skipped: another z3 binary\n" else
            let
              val z3bin' = OS.Path.concat (OS.Path.dir z3bin, OS.Path.concat (OS.Path.currentArc, OS.Path.file z3bin));
            in
              chk "unsat with another z3 binary" (querysmt_checksat_gen (SOME z3bin') NONE q_mem_unsat = BirSmtUnsat);
              chk_options_gen (SOME z3bin') "with another z3 binary";
              chk "sat with the default z3 binary" (querysmt_checksat NONE q_mem_sat = BirSmtSat);
              chk_options "with the default z3 binary"
            end;
  in
    ()
  end;

val _ = test_protocol Z3IncrementalFallback;
val _ = test_protocol Z3NonIncremental;
val _ = test_protocol Z3Incremental;
val _ = test_protocol Z3IncrementalFallback;
