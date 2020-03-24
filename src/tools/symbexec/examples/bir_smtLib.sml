structure bir_smtLib =
struct
local

open bir_scamv_helpersLib;

(* directory creation helper *)
  fun makedir makepath path =
    let
      val r = OS.Process.system ("mkdir " ^ (if makepath then "-p " else "") ^ path);
      val _ = if not (OS.Process.isSuccess r) then
                raise ERR "makedir" ("couldn't create the following directory: " ^ path)
              else
                ();
    in
      ()
    end;

fun get_tempfile prefix =
  let
    val tempdir = "tempdir";
    val _ = makedir true tempdir;
    val date = Date.fromTimeLocal (Time.now ());
    val datestr = Date.fmt "%Y-%m-%d_%H-%M-%S" date;
  in
    tempdir ^ "/" ^ prefix ^ "_" ^ datestr
  end;

fun writeToFile str file_name =
  let
    val outstream = TextIO.openOut file_name;
    val _ = TextIO.output (outstream, str) before TextIO.closeOut outstream;
  in
    () 
  end;


in

datatype bir_smt_result =
    BirSmtSat
  | BirSmtUnsat
  | BirSmtUnknown;

fun querysmt q =
  let
    val tempfile = get_tempfile "smtquery";
    val _ = writeToFile q tempfile;

    val out = get_exec_output ("z3 " ^ tempfile);
  in
    if out = "sat\n" then
      BirSmtSat
    else if out = "unsat\n" then
      BirSmtUnsat
    else if out = "unknown\n" then
      BirSmtUnknown
    else
      (print "\n============================\n";
       print out;
       print "\n============================\n";
       raise ERR "querysmt" "unknown output from z3")
  end;

(* https://rise4fun.com/z3/tutorial *)

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
        "(assert (> (* a a) 3))\n" ^
        "(assert (= (+ (* b b b) (* b c)) 3.0))\n" ^
        "(check-sat)\n";

val q = "(echo \"Z3 does not always find solutions to non-linear problems\")\n";

val q = "(check-sat)\n";

val result = querysmt q;

end (* local *)
end (* struct *)
