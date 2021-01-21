structure bir_json_execLib =
struct
local
  val ERR = Feedback.mk_HOL_ERR "bir_json_execLib"
  val wrap_exn = Feedback.wrap_exn "bir_json_execLib"

(*
val cmd  = "/usr/bin/echo";
val args = ["hello there!"];
val str_in_o = NONE;

val cmd  = "/usr/bin/cat";
val args = [];
val str_in_o = SOME "another one!\n";

val input = (cmd, args, str_in_o);

get_exec_output_gen true  input
get_exec_output_gen false input
*)

  fun get_exec_output_gen do_print (cmd, args, str_in_o) =
    let
      val pr = Unix.execute (cmd, args) : (TextIO.instream, TextIO.outstream) Unix.proc;

      val (instream, outsteam) = Unix.streamsOf pr;

      val _ = if isSome str_in_o then
                TextIO.output (outsteam, (valOf str_in_o))
              else
                ();
      val _ = TextIO.closeOut outsteam;

      val str_out = TextIO.inputAll instream;
      val _ = if not do_print then () else
                print str_out;

      val pr_r = Unix.fromStatus (Unix.reap pr);
      val res_o =
        case pr_r of
           Unix.W_EXITED       => NONE
         | Unix.W_EXITSTATUS x => SOME (Word8.toInt x)
         | _ => raise ERR "get_exec_output_gen" ("process not done: " ^ cmd);
    in
      (res_o, str_out)
    end;

  fun get_exec_output input = get_exec_output_gen false input;

  val serialize = Json.serialise;
in

  (* calls command with operation as command line argument *)
  (* serializes jsonarg structure to stdin *)
  (* returns deserialized json from stdout *)
  (*
    open Json;

    val cmd  = (* (OS.FileSys.getDir ()) ^ "/" ^ *)
               "examples/try_deserialize_serialize_json.py";
    val oper = "wrong";
    val oper = "test";
    val args = ["-v", oper];
    val jsonarg =
      OBJECT
        [("1", STRING "hello 123"),
         ("2", ARRAY [NUMBER (Arbnum.fromInt 1),
                      NUMBER (Arbnum.fromInt 2),
                      NUMBER (Arbnum.fromInt 3),
                      NUMBER (Arbnum.fromInt 4)]),
         ("3", OBJECT [("hello",  NUMBER (Arbnum.fromInt 123)),
                       ("hello2", NUMBER (Arbnum.fromInt 1234))])];

    val _ = print (serialize jsonarg);

    call_json_exec (cmd, args, jsonarg)
  *)
  fun call_json_exec_2 (cmd, args, jsonarg) =
    let
      val str_in_o = SOME (serialize jsonarg);

      val (res_o, str_out) = get_exec_output (cmd, args, str_in_o);

      val _ = if res_o = NONE orelse res_o = SOME 0 then () else
              raise ERR "call_json_exec" "command did not terminate with exit code 0";
    in
      case Json.parse str_out of
            Json.ERROR e => (
              print str_out;
              raise ERR "call_json_exec" ("error parsing the json output: " ^ e))
          | Json.OK json =>
              json
    end;

local
  open bir_fileLib;
  open bir_exec_wrapLib;

  fun call_json_exec_old command jsonarg =
    let
      val argfile = get_tempfile "call_json_exec_jsonarg" ".txt";
      val _ = write_to_file argfile (serialize jsonarg);

      val s = get_exec_output ("cat \"" ^ argfile ^ "\" | " ^
                               command);

      val _ = OS.Process.system ("rm " ^ argfile);
    in
      case Json.parse s of
            Json.ERROR e =>
              raise ERR "call_json_exec" ("error parsing the json output: " ^ e)
          | Json.OK json =>
              json
    end;
in
  fun call_json_exec_1 (cmd, args, jsonarg) =
    let
      val command = cmd ^ (List.foldl (fn (x,s) => s ^ " \"" ^ x ^ "\"") "" args);
      val r = call_json_exec_old command jsonarg;
    in
      r
    end;
end

  val call_json_exec = call_json_exec_1;

end (* local *)
end (* struct *)
