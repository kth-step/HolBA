structure holba_z3Lib =
struct

local

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

fun endmeexit p = Unix.fromStatus (Unix.reap p);

fun get_streams p = Unix.streamsOf p;

val z3proc_bin_o = ref (NONE : string option);
val z3proc_o = ref (NONE : ((TextIO.instream, TextIO.outstream) Unix.proc) option);
val bir_smtLib_z3_prelude = read_from_file (holpathdb.subst_pathvars "$(HOLBADIR)/src/shared/smt/bir_smtlibLib.z3_prelude");
val bir_smtLib_z3_prelude_n = bir_smtLib_z3_prelude ^ "\n";
val use_stack = true;
val debug_print = false;
fun get_z3proc z3bin =
  let
   val z3proc_ = !z3proc_o;
   fun check_and_restart z3p =
     if z3bin = valOf (!z3proc_bin_o) then z3p else
       let
         val _ = endmeexit z3p;
         val _ = z3proc_o := NONE;
       in
         get_z3proc z3bin
       end;
   val p = if isSome z3proc_ then check_and_restart (valOf z3proc_) else
      let
        val _ = if not debug_print then () else
	        print ("starting: " ^ z3bin ^ "\n");
        val p = openz3 z3bin;
	val _ = z3proc_bin_o := SOME z3bin;
	val _ = if not use_stack then () else
	 let
          val (_,s_out) = get_streams p;
          (* prepare prelude and push *)
          val () = TextIO.output (s_out, bir_smtLib_z3_prelude ^ "\n");
          val () = TextIO.output (s_out, "(push)\n");
	 in
	  ()
	 end;
      in (z3proc_o := SOME p; p) end;
  in
    p
  end;

fun inputLines_until m ins acc =
  let
    val line_o = TextIO.inputLine ins;
    val _ = if isSome line_o then () else
            raise ERR "inputLines_until" "stream ended before reaching the marker";
    val line = valOf line_o;
    val _ = if not debug_print then () else
            (print "collecting: "; print line);
  in
    if line = m then
      rev acc
    else
      inputLines_until m ins (line::acc)
  end

fun sendreceive_query z3bin q =
 let
   val _ = if not debug_print then () else
           (print q; print "\n");
   val p = get_z3proc z3bin;
   val (s_in,s_out) = get_streams p;
   val _ = if not use_stack then
            TextIO.output (s_out, bir_smtLib_z3_prelude_n)
           else ();

   val timer = holba_miscLib.timer_start 0;
   val z3_done_marker = "holba_z3 qdm";
   val () = TextIO.output (s_out, q ^ "(echo \"" ^ z3_done_marker ^ "\")\n");
   val out_lines = inputLines_until (z3_done_marker ^ "\n") s_in [];
   val _ = if debug_print then holba_miscLib.timer_stop
     (fn delta_s => print ("  query took " ^ delta_s ^ "\n")) timer else ();

   val _ = if not debug_print then () else
           (map print out_lines; print "\n\n");
   (* https://microsoft.github.io/z3guide/docs/logic/basiccommands/ *)
   val _ = if not use_stack then
            TextIO.output (s_out, "(reset)\n")
	   else
	    (TextIO.output (s_out, "(pop)\n");
	     TextIO.output (s_out, "(push)\n"));
 in
   out_lines
 end;
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

  fun querysmt_raw z3bin_o timeout_o q =
      let
        val z3bin = case z3bin_o of
	     NONE => get_default_z3 ()
	   | SOME x => x;
	val (timeout_s_before, timeout_s_after) =
	  case timeout_o of
             NONE => ("", "")
           | SOME timeout => ("(set-option :timeout " ^ (Int.toString timeout) ^ ")\n\n", "(set-option :timeout 4294967295)\n");
	val q_wto =
	  (timeout_s_before ^
           q ^
	   timeout_s_after)
        val out_lines = sendreceive_query z3bin q_wto;
      in
        out_lines
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
  *)

  fun querysmt_checksat_gen z3bin_o timeout_o q =
        querysmt_parse_checksat (querysmt_raw z3bin_o timeout_o (q ^ "(check-sat)\n"));
  val querysmt_checksat = querysmt_checksat_gen NONE;
  
  (* TODO: add querysmt_getmodel *)

  datatype bir_smt_type =
      SMTTY_Bool
    | SMTTY_BV   of int
    | SMTTY_MEM  of (int * int);

  fun smt_type_to_smtlib SMTTY_Bool          = "Bool"
    | smt_type_to_smtlib (SMTTY_BV  i)       = "(_ BitVec " ^ (Int.toString i) ^ ")"
    | smt_type_to_smtlib (SMTTY_MEM (ad, v)) = "(Array " ^ (smt_type_to_smtlib (SMTTY_BV ad)) ^
						     " " ^ (smt_type_to_smtlib (SMTTY_BV v)) ^ ")";

  fun smt_type_is_bv (SMTTY_BV _) = true
    | smt_type_is_bv _            = false;

  fun smt_type_is_bool SMTTY_Bool = true
    | smt_type_is_bool _          = false;

  fun smt_type_is_mem (SMTTY_MEM _) = true
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
  *)

end (* local *)

end (* struct *)
