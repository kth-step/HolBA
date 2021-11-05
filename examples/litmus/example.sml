open litmusInterfaceLib


(* compile and disassemble the program, returns the filename of the .da file *)
fun find_tests () =
    let
	val proc = Unix.execute("/usr/bin/find", ["-iname", "*.litmus"])
	val inStream = Unix.textInstreamOf proc
    in
	String.tokens Char.isSpace (TextIO.inputAll inStream) before TextIO.closeIn inStream
    end

val filenames = find_tests ()

datatype status = OK of string | ERROR of string * string

fun lift_test_and_save filename =
    (save_litmus (filename ^ ".json", lift_herd_litmus filename); print ("OK " ^filename ^ "\n"); OK filename)
    handle e => (print ("\nERROR " ^filename^"\n"); print (exnMessage e ^"\n"); ERROR (filename, exnMessage e))
		    
val basic = List.filter (String.isSubstring "size/BASIC") filenames

val s = map lift_test_and_save basic

fun get_errors [] = []
  | get_errors (x::xs) = 
    case x of
	ERROR (s1,s2) => (s1 ^ ": " ^s2)::get_errors xs
      | _ => get_errors xs 


val errors = String.concatWith "\n" (get_errors s)
open bir_fileLib;

val _ = write_to_file "errors.txt" errors


(*
open litmusInterfaceLib
load_litmus "tests/non-mixed-size/BASIC_2_THREAD/MP.litmus.json"
lift_test_and_save "tests/non-mixed-size/BASIC_2_THREAD/MP.litmus"
*)
 
