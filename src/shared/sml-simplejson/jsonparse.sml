
(* Take an input file and pass it through the JSON parser and
   serialiser, writing the result to stdout. Used for integrity
   checks. *)

fun contents filename =
    let val stream = TextIO.openIn filename
        fun read_all str acc =
            case TextIO.inputLine str of
                SOME line => read_all str (line :: acc)
              | NONE => rev acc
        val contents = read_all stream []
        val _ = TextIO.closeIn stream
    in
        String.concat contents
    end

val serialise = ref Json.serialise
        
fun processFile filename =
    let val input = contents filename
    in
        case Json.parse input of
            Json.ERROR e =>
            (TextIO.output (TextIO.stdErr, "Error: " ^ e ^ "\n");
             OS.Process.exit OS.Process.failure)
          | Json.OK json =>
            (print (!serialise json ^ "\n");
             OS.Process.exit OS.Process.success)
    end

fun usage () =
    (TextIO.output
         (TextIO.stdErr,
          "\nUsage: " ^ (CommandLine.name ()) ^
          " [-i] file.json\n\n" ^
          "Parse the named JSON file and serialise it again to stdout.\n\n" ^
          "  -i   Indent the output for readability by humans. The default\n" ^
          "       is to serialise it in a single line.\n\n");
     OS.Process.exit OS.Process.failure)

fun handleArgs args =
    case args of
        "-i"::rest => (serialise := Json.serialiseIndented; handleArgs rest)
      | [infile] => processFile infile
      | _ => usage ()
        
fun main () =
    handleArgs (CommandLine.arguments ())

                 
