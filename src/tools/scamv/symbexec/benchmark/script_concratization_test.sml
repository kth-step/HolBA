open HolKernel Parse boolLib bossLib;

open bir_inst_liftingLib;
open bir_inst_liftingLibTypes;
open bir_inst_liftingHelpersLib;
open gcc_supportLib;
open PPBackEnd Parse;

open bir_programSyntax;

open bir_miscLib;

open bslSyntax;



     
fun lift_prog dafilename =
    let
	val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
	val _ = set_trace "bir_inst_lifting.DEBUG_LEVEL" 2;

	val _ = print_with_style_ [Bold, Underline] ("Lifting " ^ dafilename ^ "\n");

	val (region_map, sections) = read_disassembly_file_regions dafilename;

	val (thm_arm8, errors) = bmil_arm8.bir_lift_prog_gen ((Arbnum.fromInt 0), (Arbnum.fromInt 0x1000000)) sections;

	val prog = (snd o dest_comb o concl) thm_arm8;
	val _ = print "\nLifting done.\n\n";
    in
	(prog, region_map, sections)
    end;

fun unpack_code x =
    case x of
	(str: string, BILME_code s) => (str, s)
      | (str: string, BILME_data) => (str, NONE)  
      | (str: string, BILME_unknown) => (str, NONE)
      | _ => raise ERR "unpack_code" "";  
fun unpack_sections x =
    case x of
	(BILMR (addr, l)) => (addr, (List.map unpack_code l))
      | _ => raise ERR "unpack_sections" "section not as expected";

fun define_entry_and_exits section =
    let
	val (addr, code) = section;
	val instructions = List.map (fn (hex_code, str_inst) =>
					if isSome str_inst then valOf str_inst else "") code;

	fun find_ret (instructions: string list, count: int ref, rets: int list) =
	    let
		fun count_ret_addr (instructions: string list, count: int ref, rets: int list) =
		    if null instructions
		    then rets
		    else (
			count := (!count + 4);
			if ((hd instructions) = "ret")
			then
			    count_ret_addr (tl instructions, count, rets@[((Arbnum.toInt addr)+(!count-4))])
			else count_ret_addr (tl instructions, count, rets));
	    in
		count_ret_addr (instructions, count, rets)
	    end
    in
	(addr, find_ret (instructions, ref 0, []))
    end;

fun entry_json binfilename magicinputfilename entry exits =
    let
	val addIndents = true;
	val serialize = if addIndents then Json.serialiseIndented else Json.serialise;
    in
	serialize (Json.OBJECT
			[("bin", Json.STRING binfilename),
			 ("birprogram", Json.STRING magicinputfilename),
			 ("entry", Json.NUMBER entry),
			 ("exits", Json.ARRAY (List.map Json.NUMBER exits))])
    end;

fun set_birprogjson bprog_t =
    let
	val magicinputfilename = (bir_angrLib.get_pythondir()) ^ "/magicinput.bir";
	val (bprog_t_m, obsrefmap) = bir_angrLib.obsrefmap_conv_prog bprog_t;
	val bprog_json_str = birprogjsonexportLib.birprogtojsonstr bprog_t_m;
	val _ = bir_fileLib.write_to_file magicinputfilename bprog_json_str;
    in magicinputfilename end;

fun run_angr_symbexecc entryjsonfilename =
    let
	open bir_angrLib;
	val pythonscript = (get_pythondir()) ^ "/symbolic_execution_wrapper.py";
	val usePythonPackage = not (Option.getOpt(OS.Process.getEnv("HOLBA_ANGR_USE_PYTHONDIR"), "") = "1");

	val output =
            if usePythonPackage then (
		print "... using python package of bir_angr ...\n";
		print "... metadata of package:\n";
		if OS.Process.isSuccess (OS.Process.system "python3 -m pip show bir_angr") then () else
		raise ERR "do_symb_exec" "python package bir_angr is not installed";
		print "... metadata end.\n";
		bir_exec_wrapLib.get_exec_output ("python3 -E -m bir_angr.symbolic_execution \"" ^ entryjsonfilename)
		) else (
            print "... using symbolic_execution_wrapper.py in python subdirectory ...\n";
            bir_exec_wrapLib.get_exec_output ("python3 -E " ^ pythonscript ^ " " ^ entryjsonfilename)
            );
	val _ = if false then print output else ();
    in output end;



val dafilename = "aes.da";
val (prog, region_map, sections) = lift_prog dafilename;
val unpack_sections = List.map unpack_sections sections;
val list_entries_and_exits = List.map define_entry_and_exits unpack_sections;


val binfilename = (bir_angrLib.get_pythondir()) ^ "/aes.out";
val magicinputfilename = set_birprogjson prog;
val dir_name = "result" ^ "-" ^ (String.extract(dafilename, 0, SOME (String.size dafilename-3)));
val make_dir = bir_fileLib.makedir true dir_name;
 

fun run_tests region_map entries_and_exits =
    ListPair.map (fn ((region_map_section, region_map_name, region_map_addr),(entry,exits)) =>
		     if region_map_section = ".text" andalso region_map_addr = entry
		     then (   
			 let
			     val entryjsonfilename = (bir_angrLib.get_pythondir()) ^ "/entry.json";
			     val exits = List.map Arbnum.fromInt exits;
			     val entry_json_str = entry_json binfilename magicinputfilename entry exits;
			     val _ = bir_fileLib.write_to_file entryjsonfilename entry_json_str;
			     val out_symbexec = run_angr_symbexecc entryjsonfilename;
			     val to_save = String.isSubstring "ConcretizationException" out_symbexec;
			     val _ = if to_save then bir_fileLib.write_to_file (dir_name ^ "/" ^ region_map_name ^ ".log") out_symbexec else ();
			 in () end)
		     else ()) (region_map, entries_and_exits);


val _ = run_tests region_map list_entries_and_exits;
    
