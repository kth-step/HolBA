
(*
val _ = load "sml-simplejson/jsonparse";
*)

fun processFile filename =
    let val input = String.concat (bir_fileLib.read_file_lines filename)
    val serialise = Json.serialiseIndented
    in
        case Json.parse input of
            Json.ERROR e =>
            (TextIO.output (TextIO.stdErr, "Error: " ^ e ^ "\n");
             OS.Process.exit OS.Process.failure)
          | Json.OK json =>
            (print (serialise json ^ "\n");
             json)
    end


val path = "../sml-simplejson/testfiles/test_parsing/"

val filename = "y_object_duplicated_key_and_value.json";

val json = processFile (path^filename)
