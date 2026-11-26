structure holba_z3Lib =
struct

local
  open HolKernel boolLib liteLib simpLib Parse bossLib;

  open holba_fileLib;
  open holba_exec_wrapLib;

  val ERR = Feedback.mk_HOL_ERR "holba_z3Lib";

in

(* =========================================================== *)
(*
val z3bin = "/home/andreas/data/hol/HolBA_opt/z3-4.8.4/bin/z3";
*)
fun openz3 z3bin = 
  (Unix.execute (z3bin, ["-in"])) : (TextIO.instream, TextIO.outstream) Unix.proc;

(*
val z3wrap = "/home/andreas/data/hol/HolBA_symbexec/src/shared/smt/z3_wrapper.py";
val prelude_path = "/home/andreas/data/hol/HolBA_symbexec/src/shared/smt/holba_z3Lib_prelude.z3";
*)
fun openz3wrap z3wrap prelude_path = 
  (Unix.execute (z3wrap, [prelude_path, "loop"])) : (TextIO.instream, TextIO.outstream) Unix.proc;

fun endmeexit p = Unix.fromStatus (Unix.reap p);

(* also stops a process that is still working on a query *)
fun stop_proc p =
  let
    val _ = Unix.kill (p, Posix.Signal.kill) handle _ => ();
  in
    endmeexit p
  end;

fun get_streams p = Unix.streamsOf p;

(* How the z3 process is driven, set by z3_protocol. Z3 has a
   non-incremental solver, which it calls solver1 and uses for a query that
   is solved on its own, and an incremental solver, solver2, which it uses
   after the first (push).
   - Z3NonIncremental: each query is sent together with the options and the
     prelude, and is followed by (reset), so that z3 solves it on its own,
     with solver1. Z3 parses the prelude again for every query, which takes
     a few milliseconds.
   - Z3Incremental: the options and the prelude are sent once, when the
     process starts, followed by (push), and each query is followed by (pop)
     and (push). Z3 solves every query with solver2, which can be much
     slower than solver1 on a large query; it uses solver1 only when solver2
     gives unknown for a query without quantifiers.
   - Z3IncrementalFallback, the default: as Z3Incremental, but the process
     starts with z3_fallback_options, so that z3 gives solver2 10
     milliseconds and solves the query with solver1 when solver2 has not
     answered sat or unsat by then. A query that solver2 answers within 10
     milliseconds, as most small queries are, is answered without parsing the
     prelude again, and any other query is solved by solver1.
   With every protocol, a timeout of querysmt_raw bounds the whole query,
   both solvers included, and z3 gives unknown when it is reached. A
   process that was started with another protocol is restarted, and every
   new process, also the one that replaces a process stopped after a
   failed query or a timeout, is prepared for the protocol. The wrapper,
   which gives the models of querysmt_getmodel, solves each query on its
   own with every protocol. *)
datatype z3_protocol =
    Z3NonIncremental
  | Z3Incremental
  | Z3IncrementalFallback;
val z3_protocol = ref Z3IncrementalFallback;

(* the options of Z3IncrementalFallback: solver2_timeout is the time in
   milliseconds that z3 gives solver2 before it uses solver1, and with
   solver2_unknown 2, z3 also uses solver1 when solver2 gives unknown for a
   query with quantifiers *)
val z3_fallback_options =
  "(set-option :combined_solver.solver2_timeout 10)\n" ^
  "(set-option :combined_solver.solver2_unknown 2)\n";

(* option commands for z3, such as the model compaction setting of
   querysmt_prepare_getmodel; they are sent before the prelude, with every
   query with Z3NonIncremental, and when the process starts with the other
   protocols *)
val z3proc_options = ref ([] : string list);

val z3proc_bin_o = ref (NONE : string option);
val z3proc_o = ref (NONE : ((TextIO.instream, TextIO.outstream) Unix.proc) option);
val z3proc_protocol = ref Z3NonIncremental;
(* The prelude is located and read on first use, not at load time: under
   holbuild, $(HOLBADIR) is not registered in holpathdb, so fall back to the
   HOLBADIR environment variable. *)
fun prelude_z3_path () =
  let
    val rel = "src/shared/smt/holba_z3Lib_prelude.z3";
    val p = holpathdb.subst_pathvars ("$(HOLBADIR)/" ^ rel);
  in
    if not (String.isPrefix "$(" p) then p else
    case OS.Process.getEnv "HOLBADIR" of
       SOME d => OS.Path.concat (d, rel)
     | NONE => raise ERR "prelude_z3_path" "cannot locate HolBA: $(HOLBADIR) is not a known HOL path and HOLBADIR is not set"
  end;
val prelude_z3_o = ref (NONE : string option);
fun prelude_z3 () =
  case !prelude_z3_o of
     SOME x => x
   | NONE => let val x = read_from_file (prelude_z3_path ()) in (prelude_z3_o := SOME x; x) end;
fun prelude_z3_n () = prelude_z3 () ^ "\n";
val debug_print = ref false;
fun kill_z3proc z3p =
  let
    val _ = z3proc_o := NONE;
    val _ = z3proc_bin_o := NONE;
    val _ = stop_proc z3p;
  in
    ()
  end;
fun get_z3proc z3bin =
  case !z3proc_o of
      SOME z3p =>
        if !z3proc_bin_o = SOME z3bin andalso !z3proc_protocol = !z3_protocol then z3p else
          (kill_z3proc z3p; get_z3proc z3bin)
    | NONE =>
      let
        val _ = if not (!debug_print) then () else
                print ("starting: " ^ z3bin ^ "\n");
        val p = openz3 z3bin;
        val _ = z3proc_o := SOME p;
        val _ = z3proc_bin_o := SOME z3bin;
        val protocol = !z3_protocol;
        val _ = z3proc_protocol := protocol;
        val (_,s_out) = get_streams p;
        (* prepare the options, the prelude and push *)
        val _ = case protocol of
                    Z3NonIncremental => ()
                  | Z3Incremental =>
                      TextIO.output (s_out, String.concat (!z3proc_options) ^ prelude_z3_n () ^ "(push)\n")
                  | Z3IncrementalFallback =>
                      TextIO.output (s_out, z3_fallback_options ^ String.concat (!z3proc_options) ^ prelude_z3_n () ^ "(push)\n");
        val _ = TextIO.flushOut s_out;
      in
        p
      end;

fun reset_z3proc () =
  case !z3proc_o of
      SOME z3p =>
        (kill_z3proc z3p
        handle _ => ())
    | NONE => ();

val z3wrapproc_o = ref (NONE : ((TextIO.instream, TextIO.outstream) Unix.proc) option);
fun get_z3wrapproc () =
  let
   val z3wrapproc_ = !z3wrapproc_o;
   val p = if isSome z3wrapproc_ then valOf z3wrapproc_ else
      let
        val z3wrap = case OS.Process.getEnv "HOL4_Z3_WRAPPED_EXECUTABLE" of
           SOME x => x
         | NONE => raise ERR "get_z3wrapproc" "variable HOL4_Z3_WRAPPED_EXECUTABLE not defined";
        val _ = if not (!debug_print) then () else
                print ("starting: " ^ z3wrap ^ "\n");
        val p = openz3wrap z3wrap (prelude_z3_path ());
      in (z3wrapproc_o := SOME p; p) end;
  in
    p
  end;

fun reset_z3wrapproc () =
  case !z3wrapproc_o of
      SOME p =>
        ((z3wrapproc_o := NONE; stop_proc p; ())
        handle _ => ())
    | NONE => ();

(* =========================================================== *)

fun inputLines_until m ins acc =
  let
    val line_o = TextIO.inputLine ins;
    val _ = if isSome line_o then () else
            raise ERR "inputLines_until" "stream ended before reaching the marker";
    val line = valOf line_o;
    val _ = if not (!debug_print) then () else
            (print "collecting: "; print line);
  in
    if line = m then
      rev acc
    else
      inputLines_until m ins (line::acc)
  end

exception Z3EXN of exn;
(* a query that fails, for example when it is interrupted, also stops the
   process, so that the next query starts with a new one *)
fun sendreceive_query z3bin q =
 let
   val _ = if not (!debug_print) then () else
           (print q; print "\n");
   val p = get_z3proc z3bin;
   val (s_in,s_out) = get_streams p;
   val incremental = !z3proc_protocol <> Z3NonIncremental;
   val _ = if incremental then () else
           TextIO.output (s_out, String.concat (!z3proc_options) ^ prelude_z3_n ());

   val timer = holba_miscLib.timer_start 0;
   val z3_done_marker = "holba_z3 qdm";
   val () = TextIO.output (s_out, q ^ "(echo \"" ^ z3_done_marker ^ "\")\n");
   val () = TextIO.flushOut s_out;
   val out_lines = inputLines_until (z3_done_marker ^ "\n") s_in [];
   val _ = if !debug_print then holba_miscLib.timer_stop
     (fn delta_s => print ("  query took " ^ delta_s ^ "\n")) timer else ();

   val _ = if not (!debug_print) then () else
           (map print out_lines; print "\n\n");
   (* https://microsoft.github.io/z3guide/docs/logic/basiccommands/ *)
   val () = TextIO.output (s_out, if incremental then "(pop)\n(push)\n" else "(reset)\n");
   val () = TextIO.flushOut s_out;
 in
   out_lines
 end
 handle e => (reset_z3proc (); raise Z3EXN e);

fun sendreceive_wrap_query q =
 let
   val p = get_z3wrapproc ();
   val (s_in,s_out) = get_streams p;

   val q_fixed = String.concat (List.map (fn c => if c = #"\n" then "\\n" else str c) (String.explode q));
   val _ = if not (!debug_print) then () else
           (print "sending: "; print q_fixed; print "\n");

   val timer = holba_miscLib.timer_start 0;
   val z3wrap_done_marker = "z3_wrapper query done";
   val () = TextIO.output (s_out, q_fixed ^ "\n");
   val () = TextIO.flushOut s_out;
   val out_lines = inputLines_until (z3wrap_done_marker ^ "\n") s_in [];
   val _ = if !debug_print then holba_miscLib.timer_stop
     (fn delta_s => print ("  wrapped query took " ^ delta_s ^ "\n")) timer else ();

   val _ = if not (!debug_print) then () else
           (map print out_lines; print "\n\n");
 in
   out_lines
 end
 handle e => (reset_z3wrapproc (); raise e);
(*
  val q = "(declare-const x (_ BitVec 8))\n(assert (= x #xFF))\n";
  val q = "(declare-const x (_ BitVec 8))\n(assert (= x #xAA))\n(assert (= x #xFF))\n";
  
  sendreceive_wrap_query q;
*)
(* =========================================================== *)

  datatype bir_smt_result =
      BirSmtSat
    | BirSmtUnsat
    | BirSmtUnknown;

  fun get_default_z3 () =
    case OS.Process.getEnv "HOL4_Z3_EXECUTABLE" of
      SOME z3bin => z3bin
    | NONE =>
      raise ERR "get_default_z3"
        "Z3 not configured: set the HOL4_Z3_EXECUTABLE environment variable to point to the Z3 executable file.";

  fun querysmt_raw_retry retries is_nok do_if_nok sendrec_qf q =
    let
      val timer = holba_miscLib.timer_raw_start ();
      val out_lines = sendrec_qf q;
      val time = Int.fromLarge (holba_miscLib.timer_raw_stop_ms timer);
      val is_nok_res = is_nok out_lines;
      (*val _ = List.app print out_lines;*)
    in
      if is_nok_res andalso retries > 0 then (
        do_if_nok ();
        querysmt_raw_retry (retries-1) is_nok do_if_nok sendrec_qf q
      ) else
        (time, out_lines, not is_nok_res)
    end;

  val querysmt_raw_timeout_override = ref (NONE: int option);
  val querysmt_raw_retries = ref 0;
  val querysmt_raw_query_times = ref (NONE: int list option);
  val querysmt_raw_unknown_as_timeout = ref false;
  exception Z3TIMEOUT of int * string; (* time of query, query string *)
  fun is_timeout out_lines = out_lines = ["unknown\n"];
  fun querysmt_raw z3bin_o timeout_o q =
    let
      val z3bin = case z3bin_o of
          NONE => get_default_z3 ()
        | SOME x => x;
      val timeout_o =
        case !querysmt_raw_timeout_override of
            NONE => timeout_o
          | SOME x => SOME x;
      val (timeout_s_before, timeout_s_after) =
        case timeout_o of
                NONE => ("", "")
              | SOME timeout => ("(set-option :timeout " ^ (Int.toString timeout) ^ ")\n\n", "(set-option :timeout 4294967295)\n");
      val q_wto =
        (timeout_s_before ^
              q ^
        timeout_s_after);

      val retries = (!querysmt_raw_retries);
      val (time, out_lines) =
        case querysmt_raw_retry retries is_timeout reset_z3proc (sendreceive_query z3bin) q_wto of
            (time, x, is_ok) =>
              if is_ok orelse (not (!querysmt_raw_unknown_as_timeout)) then
                (time, x)
              else
                raise Z3TIMEOUT (time, q);

      val querysmt_raw_query_times_o = !querysmt_raw_query_times;
      val _ = case querysmt_raw_query_times_o of
          NONE => ()
        | SOME x => querysmt_raw_query_times := SOME (time::x);
    in
      out_lines
    end;

  local
    val model_compact_off = "(set-option :model.compact false)\n";
  in
    (* the option also holds for the queries that follow *)
    fun querysmt_prepare_getmodel z3bin_o =
      let
        val _ = if List.exists (fn x => x = model_compact_off) (!z3proc_options) then () else
                z3proc_options := !z3proc_options @ [model_compact_off];
      in
        querysmt_raw z3bin_o NONE model_compact_off
      end;
  end;

(*
querysmt_raw NONE NONE "(simplify ((_ extract 3 2) #xFC))";

querysmt_raw NONE NONE "(simplify (bvor #x6 #x3))"

querysmt_raw NONE NONE "(display (_ bv20 16))"
*)

  fun querysmt_parse_checksat out_lines =
        if out_lines = ["sat\n"] then
          BirSmtSat
        else if out_lines = ["unsat\n"] then
          BirSmtUnsat
        else if out_lines = ["unknown\n"] then
          BirSmtUnknown
        else
          (print "\n============================\n";
           map print out_lines;
           print "\n============================\n";
           raise ERR "querysmt_parse_checksat" "unknown output from z3");

  fun querysmt_parse_getmodel out_lines =
        if hd out_lines = "sat\n" then
          let
            val model_lines = tl out_lines;
            val model_lines_fix = map (fn line => if (hd o rev o explode) line = #"\n" then (implode o rev o tl o rev o explode) line else line) model_lines;
          in
            (BirSmtSat, model_lines_fix)
          end
        else if hd out_lines = "unsat\n" then
          (BirSmtUnsat, [])
        else if hd out_lines = "unknown\n" then
          (BirSmtUnknown, [])
        else
          (print "\n============================\n";
           map print out_lines;
           print "\n============================\n";
           raise ERR "querysmt_parse_getmodel" "unknown output from z3");

  (* https://rise4fun.com/z3/tutorial *)
  (*
  val q = "(declare-const a Int)\n" ^
          "(declare-fun f (Int Bool) Int)\n" ^
          "(assert (> a 10))\n" ^
          "(assert (< (f a true) 100))\n" ^
          "(check-sat)\n";

  val q = "(declare-const a Int)\n" ^
          "(declare-fun f (Int Bool) Int)\n" ^
          "(assert (> a 10))\n" ^
          "(assert (< (f a true) 100))\n" ^
          "(assert (>= (f a true) 100))\n" ^
          "(check-sat)\n";

  val q = "(declare-const a Int)\n" ^
          "(declare-const b Real)\n" ^
          "(declare-const c Real)\n" ^
          "(assert (> ("^"* a a) 3))\n" ^
          "(assert (= (+ ("^"* b b b) ("^"* b c)) 3.0))\n" ^
          "(check-sat)\n";

  val q = "(echo \"Z3 does not always find solutions to non-linear problems\")\n";

  val q = "(check-sat)\n";

  val result = querysmt_parse_checksat (querysmt_raw NONE NONE q);
  val result = (querysmt_raw NONE NONE (q^"(get-model)\n"));
  *)

  fun querysmt_checksat_gen z3bin_o timeout_o q =
        querysmt_parse_checksat (querysmt_raw z3bin_o timeout_o (q ^ "(check-sat)\n"));
  val querysmt_checksat = querysmt_checksat_gen NONE;
  
  fun querysmt_getmodel q =
        querysmt_parse_getmodel (sendreceive_wrap_query q);

  (*
  val q = "(declare-const x (_ BitVec 8))\n(assert (= x #xFF))\n";
  val q = "(declare-const x (_ BitVec 8))\n(assert (= x #xAA))\n(assert (= x #xFF))\n";

  querysmt_checksat NONE q
  querysmt_getmodel q
  *)

(* ------------------------------------------------------------------------ *)

  datatype bir_smt_type =
      SMTTY_Bool
    | SMTTY_BV   of int
    | SMTTY_ARR  of (int * int);

  fun smt_type_to_smtlib SMTTY_Bool          = "Bool"
    | smt_type_to_smtlib (SMTTY_BV  i)       = "(_ BitVec " ^ (Int.toString i) ^ ")"
    | smt_type_to_smtlib (SMTTY_ARR (ad, v)) = "(Array " ^ (smt_type_to_smtlib (SMTTY_BV ad)) ^
                                                     " " ^ (smt_type_to_smtlib (SMTTY_BV v)) ^ ")";

  fun smt_type_is_bv (SMTTY_BV _) = true
    | smt_type_is_bv _            = false;

  fun smt_type_is_bool SMTTY_Bool = true
    | smt_type_is_bool _          = false;

  fun smt_type_is_mem (SMTTY_ARR _) = true
    | smt_type_is_mem _             = false;

  fun smt_vars_to_smtlib vars =
    Redblackset.foldr (fn ((vn, vty), str) => str ^ (
          "(declare-const " ^ vn ^ " " ^ (smt_type_to_smtlib vty) ^ ")"
        ) ^ "\n") "" vars;

  fun smtlib_exp_compare ((an, aty),(bn, bty)) =
    if an = bn then
      String.compare (smt_type_to_smtlib aty, smt_type_to_smtlib bty)
    else
      String.compare (an, bn);

  fun get_smtlib_type_args probfun args =
    let
      val _   = if length(args) > 0 then () else
                  (print "\n!!!\nneed at least one argument for type unification!!!\n"; probfun ());
      val sty = snd (hd args);
      val _   = if List.all (fn x => snd x = sty) args then () else
                  probfun ();
    in
      sty
    end;

  fun gen_smtlib_expr opstr args sty =
    let
      val argstr = List.foldl (fn ((s,_),str) => str ^ " " ^ s) "" args;
    in
      ("(" ^ opstr ^ argstr ^ ")", sty)
    end;

  fun apply_smtlib_op wrapfun (str, sty) =
     (wrapfun str, sty);

  (* supporting functions for memory operations via smt arrays (SMTTY_ARR) *)

  datatype bir_smt_mem_endianness =
      SMTMEM_LittleEndian
    | SMTMEM_BigEndian
    | SMTMEM_NoEndian;

  fun bir_smt_mem_endianness_to_string SMTMEM_LittleEndian = "LE"
    | bir_smt_mem_endianness_to_string SMTMEM_BigEndian = "BE"
      (* NoEndian only applies if load/store operation value size matches exactly with memory cell size *)
    | bir_smt_mem_endianness_to_string SMTMEM_NoEndian = "NE";

  val gen_smt_as_funcall_endis = [SMTMEM_LittleEndian];
  val gen_smt_as_funcall_szadis = [32, 64];
  val gen_smt_as_funcall_szcis = [8];
  val gen_smt_as_funcall_szis = [8, 16, 32, 64];

fun gen_smt_as_funcall_validate_input funname (endi, szadi, szci, szi) =
  let
          (* parameter based restrictions *)
          val () = if List.exists (fn x => x = endi) gen_smt_as_funcall_endis then () else
                    raise ERR funname ("unsupported endianness: " ^ bir_smt_mem_endianness_to_string endi);
          val () = if List.exists (fn x => x = szadi) gen_smt_as_funcall_szadis then () else
                    raise ERR funname ("unsupported memory address size: " ^ Int.toString szadi);
          val () = if List.exists (fn x => x = szci) gen_smt_as_funcall_szcis then () else
                    raise ERR funname ("unsupported memory cell size: " ^ Int.toString szci);
          val () = if List.exists (fn x => x = szi) gen_smt_as_funcall_szis then () else
                    raise ERR funname ("unsupported load/store value size: " ^ Int.toString szi);
  in
    ()
  end;

(*
fun problem_exp s = raise ERR "some problem" s;
val (szadi, szci, szi) = (64,8,32);
val valm = ("mem1", SMTTY_ARR (szadi, szci));
val valad = ("mem_ad1", SMTTY_BV szadi);
val valv = ("mem_v1", SMTTY_BV szi);
*)
fun gen_smt_load_as_exp valm valad (endi, szadi, szci, szi) =
  (* special case for szci = szi *)
  if szci = szi then
    gen_smtlib_expr "select" [valm, valad] (SMTTY_BV szi)
  else
  let
          val revfun =
            if endi = SMTMEM_LittleEndian then List.rev else
            if endi = SMTMEM_BigEndian then I else
            raise ERR "gen_smt_load_as_exp" "unsupported combination of endianness and memory dimension";

          fun gen_addr_const i = "(_ bv" ^ (Int.toString i) ^ " " ^ (Int.toString szadi) ^ ")";
          fun gen_addr_val i = ("(bvadd " ^ (fst valad) ^ " " ^ (gen_addr_const i) ^ ")", SMTTY_BV szadi);
          
          val selects = List.tabulate (szi div 8, fn i => gen_smtlib_expr "select" [valm, gen_addr_val i] (SMTTY_BV szci));
          val loadval = gen_smtlib_expr "concat" (revfun selects) (SMTTY_BV szi);
  in
    loadval
  end;

fun gen_smt_store_as_exp valm valad valv (endi, szadi, szci, szi) =
  (* special case for szci = szi *)
  if szci = szi then
    gen_smtlib_expr "store" [valm, valad, valv] (snd valm)
  else
  let
          val revfun =
            if endi = SMTMEM_LittleEndian then List.rev else
            if endi = SMTMEM_BigEndian then I else
            raise ERR "gen_smt_load_as_exp" "unsupported combination of endianness and memory dimension";

          fun gen_addr_const i = "(_ bv" ^ (Int.toString i) ^ " " ^ (Int.toString szadi) ^ ")";
          fun gen_addr_val i = ("(bvadd " ^ (fst valad) ^ " " ^ (gen_addr_const i) ^ ")", SMTTY_BV szadi);

          fun gen_extract_val i = ("((_ extract "^(Int.toString ((i+1)*szci-1))^" "^(Int.toString (i*szci))^") " ^ (fst valv) ^ ")", SMTTY_BV szci);

          fun gen_store a i = gen_smtlib_expr "store" [a, gen_addr_val i, gen_extract_val i] (snd valm);
          val idxs = List.tabulate (szi div 8, I);
          
          val storeval = List.foldl (fn (i,a) => gen_store a i) valm (revfun idxs);
  in
    storeval
  end;

fun gen_smt_loadstore_funname opstr (endi, szadi, szci, szi) =
  opstr ^ "fun_" ^ (bir_smt_mem_endianness_to_string endi) ^
             "_" ^ (Int.toString szadi) ^
             "_" ^ (Int.toString szci) ^
             "_" ^ (Int.toString szi);

fun get_opparam_endi (endi, szadi, szci, szi) = endi;
fun get_opparam_szi (endi, szadi, szci, szi) = szi;

fun gen_smt_load_as_funcall valm valad opparam =
  if get_opparam_endi opparam = SMTMEM_NoEndian then
    gen_smt_load_as_exp valm valad opparam
  else
  let
          val _ = gen_smt_as_funcall_validate_input "gen_smt_load_as_funcall" opparam;

          val z3funname = gen_smt_loadstore_funname "load" opparam;

          val loadval = gen_smtlib_expr z3funname [valm, valad] (SMTTY_BV (get_opparam_szi opparam));
  in
    loadval
  end;

fun gen_smt_store_as_funcall valm valad valv opparam =
  if get_opparam_endi opparam = SMTMEM_NoEndian then
    gen_smt_store_as_exp valm valad valv opparam
  else
  let
          val _ = gen_smt_as_funcall_validate_input "gen_smt_store_as_funcall" opparam;

          val z3funname = gen_smt_loadstore_funname "store" opparam;

          val storeval = gen_smtlib_expr z3funname [valm, valad, valv] (snd valm);
  in
    storeval
  end;

(* ------------------------------------------------------------------------ *)

  fun querysmt_mk_q (vars, asserts) =
    if List.exists (fn (qs,qt) => let val res = qt <> SMTTY_Bool in (if res then print ("problem: " ^ qs ^ "\n") else (); res) end) asserts then
      raise ERR "querysmt_mk_q" "don't know how to handle expression type. must be bool"
    else
      let
        val decls = smt_vars_to_smtlib vars;
        val asserts_str =
          List.foldr (fn ((q,_), str) => str ^ (
            "(assert " ^ q ^ ")\n"
          )) "" asserts;
      in
          (decls       ^ "\n" ^
           asserts_str ^ "\n")
      end;

  (*
  val q = querysmt_mk_q (Redblackset.fromList smtlib_exp_compare [("x", SMTTY_BV 8)],
                         [("(= x #xFF)", SMTTY_Bool)]);
  val q = querysmt_mk_q (Redblackset.fromList smtlib_exp_compare [("x", SMTTY_BV 8)],
                         [("(= x #xFF)", SMTTY_Bool), ("(= x #xAA)", SMTTY_Bool)]);

  querysmt_checksat NONE q
  querysmt_getmodel q
  *)

end (* local *)

end (* struct *)
