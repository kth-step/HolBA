structure bir_json_execLib =
struct
local
  val ERR = Feedback.mk_HOL_ERR "bir_json_execLib"
  val wrap_exn = Feedback.wrap_exn "bir_json_execLib"

  open bir_fileLib;
  open bir_exec_wrapLib;

  val serialize = Json.serialiseIndented;
in

  (* calls command with operation as command line argument *)
  (* serializes jsonarg structure to stdin *)
  (* returns deserialized json from stdout *)
  (*
    val command = "examples/try_deserialize_serialize_json.py -v";
    val operation = "wrong";
    val operation = "test";
    val jsonarg = Json.OBJECT
        [("1", Json.STRING "hello 123"),
         ("2", Json.ARRAY [Json.NUMBER 1.0, Json.NUMBER 2.0, Json.NUMBER 3.0, Json.NUMBER 4.0]),
         ("3", Json.OBJECT [("hello", Json.NUMBER 123.0), ("hello2", Json.NUMBER 1234.0)])];
    val _ = print (serialize jsonarg);
  *)
  fun call_json_exec command operation jsonarg =
    let
      val argfile = get_tempfile "call_json_exec_jsonarg" ".txt";
      val _ = write_to_file argfile (serialize jsonarg);

      val s = get_exec_output ("cat \"" ^ argfile ^ "\" | " ^
                               command ^ " \"" ^ operation ^ "\"");

      val _ = OS.Process.system ("rm " ^ argfile);
    in
      case Json.parse s of
            Json.ERROR e =>
              raise ERR "call_json_exec" ("error parsing the json output: " ^ e)
          | Json.OK json =>
              json
    end;

end (* local *)
end (* struct *)
