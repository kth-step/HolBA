signature litmusInterfaceLib =
sig
    type litmus = herdLitmusLib.litmus
    (* 
    Argument: path to a herdtools litmus test
    Returns: BIR litmus test
     *)
    val lift_herd_litmus : string -> litmus
    (*
    Argument: Path to save file
	      Litmus test to be saved
    *)
    val save_litmus : string * litmus -> unit
    (*
    Argument: Path to saved file with litmus test
    Returns: Litmus test
    *)
    val load_litmus : string -> litmus
end
    
structure litmusInterfaceLib : litmusInterfaceLib =
struct

open HolKernel Parse
open Json JsonUtil

val ERR = Feedback.mk_HOL_ERR "litmusInterfaceLib"

type litmus = herdLitmusLib.litmus

val lift_herd_litmus = herdLitmusLib.parse

fun save_litmus (filename,l:litmus) =

    let
	val json = OBJECT [
		("arch", STRING (#arch l)),
		("name", STRING (#name l)),
		("info", ARRAY (map STRING (#info l))),
		("inits", ARRAY (map (STRING o term_to_string) (op:: (#inits l)))),
		("progs", ARRAY (map (STRING o term_to_string) (#progs l))),
		("final", (STRING o term_to_string) (#final l))]
    in
	bir_fileLib.write_to_file filename (Json.serialise json)
    end

fun load_litmus (filename: string) =
    let
	fun term_of_string s = Term [QUOTE s]
	val json = case Json.parse (bir_fileLib.read_from_file filename)
		    of OK json => json
		     | ERROR e => raise ERR "load_litmus" e
	val lookup = lookupField json
	val arch = asString (lookup "arch")
	val name = asString (lookup "name")
	val info = arrayMap asString (lookup "info")
	val inits = arrayMap (term_of_string o asString) (lookup "inits")
	val progs = arrayMap (term_of_string o asString) (lookup "progs")
	val final = (term_of_string o asString) (lookup "final")
    in
	{
	  arch=arch,
	  name=name,
	  info=info,
	  inits=(hd inits,tl inits),
	  progs=progs,
	  final=final
	} : litmus
    end
end
