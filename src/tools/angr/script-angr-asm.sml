open scamvcopyLib;


(*val bprog = lift_asm_code "\tadd x0,x1,x2\n\tsub x1,x0,x2";*)
val bprog = lift_asm_file "test-angr-asm.asm";



val _ = bir_angrLib.do_symb_exec bprog;


(*
val bprog_json_str = birprogjsonexportLib.birprogtojsonstr bprog;
val _ = print bprog_json_str;
*)

