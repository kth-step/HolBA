structure bir_prog_slingLib :> bir_prog_slingLib =
struct

  open HolKernel boolLib liteLib simpLib Parse bossLib;
  open bir_prog_genLib;
  open bir_inst_liftingLib;
  open gcc_supportLib;
  open bir_gccLib;

  open bir_embexp_driverLib;

  open listSyntax;

  (* for arm8 *)
  val (bmil_bir_lift_prog_gen, disassemble_fun) = (bmil_arm8.bir_lift_prog_gen, arm8AssemblerLib.arm8_disassemble);

  (* this was copied -----> *)
  fun disassembly_section_to_minmax section =
      case section of
          BILMR(addr_start, entries) =>
          let
            val data_strs = List.map fst entries;
	          (* val _ = List.map (fn x => print (x ^ "\r\n")) data_strs; *)
            val lengths_st = List.map String.size data_strs;
            val _ = List.map (fn x => ()) lengths_st;
            val lengths = List.map (fn x => Arbnum.fromInt (x div 2)) lengths_st;
            val length = List.foldr (Arbnum.+) Arbnum.zero lengths;
          in
            (addr_start, Arbnum.+(addr_start, length))
          end;

  fun minmax_fromlist ls = List.foldl (fn ((min_1,max_1),(min_2,max_2)) =>
                                          ((if Arbnum.<(min_1, min_2) then min_1 else min_2),
                                           (if Arbnum.>(max_1, max_2) then max_1 else max_2))
                                      ) (hd ls) (tl ls);

  fun da_sections_minmax sections = minmax_fromlist (List.map disassembly_section_to_minmax sections);
  (* <---- this was copied *)

  fun lift_program_from_sections sections =
    let
        val prog_range = da_sections_minmax sections;
        val (thm_prog, errors) = bmil_bir_lift_prog_gen prog_range sections;
        val lifted_prog = (snd o dest_comb o concl) thm_prog;
        val lifted_prog_typed =
            inst [Type`:'observation_type` |-> Type`:bir_val_t`]
                 lifted_prog;
    in
        lifted_prog_typed
    end

  fun process_asm_code asm_code =
      let
	val da_file = bir_gcc_assembe_disassemble asm_code "./tempdir"

	val (region_map, sections) = read_disassembly_file_regions da_file;
      in
	  (asm_code, sections)
      end

  fun print_asm_code asm_code = (
                print "---------------------------------\n";
                print "=================================\n";
                print asm_code;
                print "=================================\n";
                print "---------------------------------\n");

  fun gen_until_liftable prog_gen_fun =
    let
      val prog = prog_gen_fun ();
      val prog_len = length prog;
      val asm_code_ = bir_prog_gen_asm_lines_to_code prog;
      val _ = print_asm_code asm_code_;
      val compile_opt = SOME (process_asm_code asm_code_)
	     handle HOL_ERR x => (print_asm_code asm_code_; NONE);
    in
      case compile_opt of
	  NONE => gen_until_liftable prog_gen_fun
	| SOME (asm_code, sections) => 
    let
      val lifted_prog = lift_program_from_sections sections;
      val blocks = (fst o dest_list o dest_BirProgram) lifted_prog;
      (* val labels = List.map (fn t => (snd o dest_eq o concl o EVAL) ``(^t).bb_label``) blocks; *)
      val lift_worked = (List.length blocks = prog_len);
      val _ = if lift_worked then ()
	      else print_asm_code asm_code;
    in
      if lift_worked then (prog, lifted_prog) else (gen_until_liftable prog_gen_fun)
    end
    end;


  fun prog_gen_store prog_gen_id prog_gen_fun () =
    let
      val (asm_lines, lifted_prog) = gen_until_liftable prog_gen_fun;

      val prog_id = bir_embexp_prog_create ("arm8", prog_gen_id) asm_lines;
    in
      (prog_id, lifted_prog)
    end;


(* instances of program generators *)
val prog_gen_store_mock = prog_gen_store "prog_gen_mock" bir_prog_gen_arm8_mock;
fun prog_gen_store_rand sz = prog_gen_store "prog_gen_rand" (fn () => bir_prog_gen_arm8_rand sz);


end (* struct *)
