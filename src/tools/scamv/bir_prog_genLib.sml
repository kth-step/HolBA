structure bir_prog_genLib :> bir_prog_genLib =
struct

  open HolKernel boolLib liteLib simpLib Parse bossLib;
  open bir_inst_liftingLib;
  open gcc_supportLib;
  open bir_gccLib;

  open bir_embexp_driverLib;

  open listSyntax;

  open bir_prog_gen_randLib;
  open asm_genLib;

  open bir_scamv_helpersLib;

(* lifting infrastructure (handles retry of program generation also, in case of failure) *)
(* ========================================================================================= *)

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
	val da_file = bir_gcc_assembe_disassemble asm_code

	val (region_map, sections) = read_disassembly_file_regions da_file;
      in
	  sections
      end

  fun print_asm_code asm_code = (
                print "---------------------------------\n";
                print "=================================\n";
                print asm_code;
                print "=================================\n";
                print "---------------------------------\n");

  fun gen_until_liftable retry_on_liftfail prog_gen_fun args =
    let
      val prog = prog_gen_fun args;
      val prog_len = length prog;
      val asm_code = bir_embexp_prog_to_code prog;
      val _ = print_asm_code asm_code;
      val compile_opt = SOME (process_asm_code asm_code)
	     handle HOL_ERR x => if retry_on_liftfail then NONE else
                                   raise HOL_ERR x;
    in
      case compile_opt of
	  NONE => gen_until_liftable retry_on_liftfail prog_gen_fun args
	| SOME sections => 
    let
      val lifted_prog = lift_program_from_sections sections;
      val blocks = (fst o dest_list o dest_BirProgram) lifted_prog;
      (* val labels = List.map (fn t => (snd o dest_eq o concl o EVAL) ``(^t).bb_label``) blocks; *)
      (* TODO: this is not correct! we have to compare the labels *)
      val lift_worked = (List.length blocks = prog_len);
    in
      if lift_worked then (asm_code, lifted_prog) else
      if retry_on_liftfail then (gen_until_liftable retry_on_liftfail prog_gen_fun args) else
      raise ERR "gen_until_liftable" "lifting failed"
    end
    end;


  fun prog_gen_store retry_on_liftfail prog_gen_id prog_gen_fun args () =
    let
      val (asm_code, lifted_prog) = gen_until_liftable retry_on_liftfail prog_gen_fun args;

      val prog_id = bir_embexp_prog_create ("arm8", prog_gen_id) asm_code;
    in
      (prog_id, lifted_prog)
    end;


(* load file to asm_lines (assuming it is correct assembly code with only forward jumps and no use of labels) *)
(* ========================================================================================= *)
  fun load_asm_lines filename =
    let
      val asm_lines = read_from_file_lines filename;
      val asm_lines = List.map (strip_ws_off true) asm_lines;
      val asm_lines = List.filter (fn x => not (x = "")) asm_lines;
    in
      asm_lines
    end

(* fixed programs for mockup *)
(* ========================================================================================= *)
  val mock_progs_i = ref 0;
  val mock_progs = ref [["ldr x2, [x1]"]];
  val wrap_around = ref false;

  fun bir_prog_gen_arm8_mock_set progs =
    let
      val _ = mock_progs_i := 0;
      val _ = mock_progs := progs;
    in
      ()
    end;

  fun bir_prog_gen_arm8_mock_propagate files =
    mock_progs := (!mock_progs)@(List.map load_asm_lines files);

  fun bir_prog_gen_arm8_mock_set_wrap_around b =
    let
      val _ = wrap_around := b;
      val _ = if not (!wrap_around) then ()
	      else mock_progs_i := Int.mod(!mock_progs_i, length (!mock_progs));
    in
      ()
    end;

  fun bir_prog_gen_arm8_mock () =
    let
      val _ = if !mock_progs_i < length (!mock_progs) then ()
	      else raise ERR "bir_prog_gen_arm8_mock" "no more programs";

      val prog = List.nth(!mock_progs, !mock_progs_i);

      val _ = mock_progs_i := (!mock_progs_i) + 1;
      val _ = if not (!wrap_around) then ()
	      else mock_progs_i := Int.mod(!mock_progs_i, length (!mock_progs));
    in
      prog
    end;



(* instances of program generators *)
(* ========================================================================================= *)
val prog_gen_store_mock = prog_gen_store false "prog_gen_mock" bir_prog_gen_arm8_mock ();
fun prog_gen_store_fromfile filename = prog_gen_store false "prog_gen_fromfile" load_asm_lines filename;
fun prog_gen_store_rand sz = prog_gen_store true "prog_gen_rand" bir_prog_gen_arm8_rand sz;
fun prog_gen_store_a_la_qc sz =
    prog_gen_store true "prog_gen_a_la_qc" prog_gen_a_la_qc sz;

(*
val filename = "examples/asm/branch.s";
val (prog_id, lifted_prog) = prog_gen_store_fromfile filename ();

val _ = bir_prog_gen_arm8_mock_set_wrap_around true;
val _ = bir_prog_gen_arm8_mock_set [["b #0x80"]];
val _ = bir_prog_gen_arm8_mock_set [["subs w12, w12, w15, sxtb #1"]];
val (prog_id, lifted_prog) = prog_gen_store_mock ();

val (prog_id, lifted_prog) = prog_gen_store_rand 5 ();

val prog = lifted_prog;
*)


end; (* struct *)


