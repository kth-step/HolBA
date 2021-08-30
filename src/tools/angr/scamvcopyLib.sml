structure scamvcopyLib =
struct

(* ============================================== *)
(* =============== bir_gccLib     =============== *)
(* ============================================== *)

local
  open bir_fileLib;

  val libname = "scamvcopyLib.bir_gccLib"
  val ERR = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname
in

  fun gcc_prefix () =
      case Option.mapPartial (fn p => if p <> "" then SOME p else NONE)
                             (OS.Process.getEnv("HOLBA_GCC_ARM8_CROSS")) of
          NONE => raise ERR "scamv_gcc_prefix" "the environment variable HOLBA_GCC_ARM8_CROSS is not set"
        | SOME p => p;


(*
val lines = "";
*)
  fun bir_gcc_assembe_disassemble input_code =
    let
      val gcc_prefix = gcc_prefix ();

      val path_asm_s  = get_simple_tempfile "asm.s";
      val path_asm_o  = get_simple_tempfile "asm.o";
      val path_asm_da = get_simple_tempfile "asm.da";

      val _ = write_to_file path_asm_s input_code;

      val commandline = (gcc_prefix ^ "gcc -o " ^ path_asm_o ^ " -c " ^ path_asm_s ^
                         " && " ^
                         gcc_prefix ^ "objdump -d " ^ path_asm_o ^ " > " ^ path_asm_da);
      val _ = if OS.Process.isSuccess (OS.Process.system commandline) then ()
              else raise ERR "bir_gcc_assembe_disassemble" "compilation failed somehow";
    in
      path_asm_da
    end;

end (* local *)



(* ============================================== *)
(* =============== bir_prog_genLib ============== *)
(* ============================================== *)

local
  val libname = "scamvcopyLib.bir_prog_genLib"
  val ERR = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname

  open HolKernel Parse boolLib bossLib;

  open bir_inst_liftingLib;
  open bir_inst_liftingLibTypes;

  open gcc_supportLib;
in

  (* for arm8 *)
  val bmil_bir_lift_prog_gen = bmil_arm8.bir_lift_prog_gen;

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
	val da_file = bir_gcc_assembe_disassemble asm_code

	val (region_map, sections) = read_disassembly_file_regions da_file;
      in
	  sections
      end

end (* local *)


(* ============================================== *)
(* =============== composition     ============== *)
(* ============================================== *)

  fun lift_asm_code asm_code =
    let
      val sections = process_asm_code asm_code;
      val lifted_prog = lift_program_from_sections sections;
    in lifted_prog end;

local
  open bir_fileLib;
in
  fun lift_asm_file asm_file =
    let
      val asm_code = read_from_file asm_file;
      val sections = process_asm_code asm_code;
      val lifted_prog = lift_program_from_sections sections;
    in lifted_prog end;
end;

end (* struct *)
