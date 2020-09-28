structure bir_prog_genLib :> bir_prog_genLib =
struct

  open HolKernel boolLib liteLib simpLib Parse bossLib;
  open bir_inst_liftingLib;
  open gcc_supportLib;
  open bir_gccLib;

  open bir_embexp_driverLib;

  open listSyntax;
  open wordsSyntax;

  open bir_prog_gen_randLib;
  open bir_prog_gen_sliceLib;
  open asm_genLib;
  open armv8_prefetch_genLib;

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
	     handle HOL_ERR x => if retry_on_liftfail then (print ("not liftable:\n" ^ PolyML.makestring x); NONE) else
                                   raise HOL_ERR x;
    in
      case compile_opt of
	  NONE => gen_until_liftable retry_on_liftfail prog_gen_fun args
	| SOME sections => 
    let
      (*
      val SOME sections = compile_opt;
      *)
      val lifted_prog = lift_program_from_sections sections;
      val blocks = (fst o dest_list o dest_BirProgram) lifted_prog;
      val labels = List.map (fn t => (snd o dest_eq o concl o EVAL) ``(^t).bb_label``) blocks;
      fun lbl_exists idx = List.exists (fn x => x = ``BL_Address (Imm64 ^(mk_wordi (Arbnum.fromInt (idx*4), 64)))``) labels;
      val lift_worked = List.all lbl_exists (List.tabulate (prog_len, fn x => x));
    in
      if lift_worked then (asm_code, lifted_prog, prog_len) else
      if retry_on_liftfail then (gen_until_liftable retry_on_liftfail prog_gen_fun args) else
      raise ERR "gen_until_liftable" "lifting failed"
    end
    end;

  fun prog_gen_store prog_gen_id retry_on_liftfail prog_gen_fun args () =
    let
      val (asm_code, lifted_prog, len) = gen_until_liftable retry_on_liftfail prog_gen_fun args;


      val prog_with_halt =
        let
          val (blocks,ty) = dest_list (dest_BirProgram lifted_prog);
          val obs_ty = (hd o snd o dest_type) ty;
          val lbl = ``BL_Address (Imm64 ^(mk_wordi (Arbnum.fromInt (len*4), 64)))``;
          val new_last_block =  bir_programSyntax.mk_bir_block
                    (lbl, mk_list ([], mk_type ("bir_stmt_basic_t", [obs_ty])),
                     ``BStmt_Halt (BExp_Const (Imm32 0x000000w))``);
        in
          (mk_BirProgram o mk_list) (blocks@[new_last_block],ty)
        end;

      val prog_id = bir_embexp_prog_create ("arm8", prog_gen_id) asm_code;
    in
      (prog_id, prog_with_halt)
    end;


(* load file to asm_lines (assuming it is correct assembly code with only forward jumps and no use of labels) *)
(* ========================================================================================= *)
  fun load_asm_lines filename =
    bir_embexp_code_to_prog (read_from_file filename);


(* load from embexp progs listfile *)
(* ========================================================================================= *)
local
  val last_filelist  = ref "";
  val last_prog_list = ref [];
  val last_cur_idx   = ref 0;
in
  fun load_next_fromlistfile filename =
    let
      val _ =
        if !last_filelist = filename then
          (last_cur_idx   := !last_cur_idx + 1)
        else
          (last_filelist  := filename;
           last_prog_list := [];
           last_cur_idx   := 0;
           last_prog_list := bir_embexp_load_progs filename);

      val (prog_list, cur_idx) = (!last_prog_list, !last_cur_idx);
    in
      if cur_idx < List.length prog_list then
        List.nth (prog_list, cur_idx)
      else
        raise ERR "load_next_fromlistfile" "end of progs listfile reached"
    end
end;


(* instances of program generators *)
(* ========================================================================================= *)
fun prog_gen_store_fromfile filename   = prog_gen_store "prog_gen_fromfile"          false load_asm_lines                 filename;
fun prog_gen_store_fromlines asmlines  = prog_gen_store "prog_gen_fromlines"         false (fn x => x)                    asmlines;

fun prog_gen_store_listfile filename   = prog_gen_store "prog_gen_listfile"          false load_next_fromlistfile         filename;

fun prog_gen_store_rand param sz       = prog_gen_store ("prog_gen_rand::"^param)    true  (bir_prog_gen_arm8_rand param) sz;

fun pgen_qc_param param =
  case param of
     "xld"      => prog_gen_a_la_qc arb_program_load
   | "previct1" => prog_gen_a_la_qc arb_program_previct1
   | "previct2" => prog_gen_a_la_qc arb_program_previct2
   | "previct3" => prog_gen_a_la_qc arb_program_previct3
   | "previct4" => prog_gen_a_la_qc arb_program_previct4
   | "previct5" => prog_gen_a_la_qc arb_program_previct5
   | "spectre"  => prog_gen_a_la_qc_noresize arb_program_spectre
   | _          => raise ERR "prog_gen_store_a_la_qc" "unknown qc generator";

fun prog_gen_store_a_la_qc param sz    = prog_gen_store ("prog_gen_a_la_qc::"^param) true  (pgen_qc_param param)          sz;
    
fun prog_gen_store_rand_slice sz       = prog_gen_store "prog_gen_rand_slice"        true  bir_prog_gen_arm8_slice        sz;
fun prog_gen_store_prefetch_stride sz  = prog_gen_store "prog_gen_prefetch_stride"   true  prog_gen_prefetch_stride       sz;

(*
val filename = "examples/asm/branch.s";
val retry_on_liftfail = false
val prog_gen_fun = load_asm_lines
val args = filename
val (prog_id, lifted_prog) = prog_gen_store_fromfile filename ();

val (prog_id, lifted_prog) = prog_gen_store_rand "" 6 ();

val prog = lifted_prog;
*)

end; (* struct *)
