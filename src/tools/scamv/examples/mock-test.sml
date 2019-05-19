open HolKernel Parse boolLib bossLib;
open bir_exp_to_wordsLib;
open bir_rel_synthLib;
open bslSyntax;
open wordsSyntax;
open bir_embexp_driverLib;
open bir_symb_execLib;
open bir_prog_genLib;
open bir_inst_liftingLib;
open bir_gccLib;
open gcc_supportLib;
open listSyntax;

(* Load the dependencies in interactive sessions *)
val _ = if !Globals.interactive then (
  load "../Z3_SAT_modelLib"; (* ../ *)
  load "../bir_exp_to_wordsLib"; (* ../ *)
  ()) else ();

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = Globals.show_tags := true;

(*
val _ = Globals.linewidth := 100;
val _ = wordsLib.add_word_cast_printer ();
val _ = Feedback.set_trace "HolSmtLib" 4;
val _ = Globals.show_assums := true;
val _ = Globals.show_types := true;
*)



(* --------------------------------------- *)
(* program generation                      *)
(* --------------------------------------- *)

(*
val _ = bir_prog_gen_arm8_mock_set [];
val _ = bir_prog_gen_arm8_mock_set_wrap_around true;
*)

val asm_lines = bir_prog_gen_arm8_mock ();

val da_file = bir_gcc_assembe_disassemble asm_lines "./tempdir"

  fun readFromFile file_name =
    let
      val file = TextIO.openIn file_name;
      val s    = TextIO.inputAll file before TextIO.closeIn file;
    in
      s 
    end;

val asm_file_contents = List.foldl (fn (l, s) => s ^ "\t" ^ l ^ "\n") "\n" asm_lines;


(* --------------------------------------- *)
(* lifting                                 *)
(* --------------------------------------- *)

val (region_map, sections) = read_disassembly_file_regions da_file;
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

val prog_range = da_sections_minmax sections;
val (thm_prog, errors) = bmil_bir_lift_prog_gen prog_range sections;

val lifted_prog = (snd o dest_comb o concl) thm_prog;


(* --------------------------------------- *)
(* observation augmentation                *)
(* --------------------------------------- *)

(* this is the memory constraint for cached access *)
val cond1 = bandl [ble (bconst64 (0x30000 + 0x80000000),
                       bden (bvarimm64 "R1")),
                  ble (bden (bvarimm64 "R1"), bconst64 (0x42ff8 + 0x80000000))
                 ];


(* TODO: this is manual for now *)
val prog_w_obs = ``BirProgram
      [<|bb_label := BL_Address_HC (Imm64 0w) "F9400023 (ldr x3, [x1])";
         bb_statements :=
         [BStmt_Assert
              (^cond1);
	   BStmt_Assert
              (BExp_Aligned Bit64 3 (BExp_Den (BVar "R1" (BType_Imm Bit64))));
            BStmt_Assign (BVar "R3" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_Den (BVar "R1" (BType_Imm Bit64))) BEnd_LittleEndian
                 Bit64);
            BStmt_Observe (BExp_Const (Imm1 1w))
                          ([BExp_BinExp BIExp_And
                                        (BExp_Const (Imm64 0x1FC0w))
                                        (BExp_Den (BVar "R1" (BType_Imm Bit64)))])
                          (\x. x)];
         bb_last_statement := BStmt_Halt (BExp_Const (Imm64 4w))|>]``;



(* --------------------------------------- *)
(* symbolic execution (& determine paths)  *)
(* --------------------------------------- *)

val tree = symb_exec_program prog_w_obs;

(* leaf list *)
val leafs = symb_exec_leaflist tree;

(* retrieval of path condition and observation expressions *)
(*
val s = hd leafs;
*)
fun extract_cond_obs s =
  let
    val (_,_,cond,_,obs) = dest_bir_symb_state s;
    val obss = ((List.map dest_bir_symb_obs) o fst o dest_list) obs;
  in
    (* this converts BIR consts to HOL4 variables *)
    (bir_exp_hvar_to_bvar cond, List.map (fn (ec,eo) =>
         (bir_exp_hvar_to_bvar ec, bir_exp_hvar_to_bvar eo)) obss)
  end;

val leaf_cond_obss = List.map extract_cond_obs leafs;


(* --------------------------------------- *)
(* relation generation                     *)
(* --------------------------------------- *)

(* generate the input structure for the relation generation *)
(*
 TODO: interface mismatch to relation genration
 why SOME and NONE?
 why no lists of observations?
 *)
val prog_obss_paths = List.map (fn (patc,obsl) => (patc,
      if obsl = [] then NONE else
        SOME (List.map (fn (cond,obslt) => (cond,
          let
            val (obstl, obstt) = dest_list obslt;
          in
            if length obstl <> 1 then
              raise ERR "prog_obss_paths" "currently we support only singleton observations"
            else
              hd obstl
          end)) obsl)
       )) leaf_cond_obss;

val relation = mkRel prog_obss_paths;


(* --------------------------------------- *)
(* test generation                         *)
(* --------------------------------------- *)

(* Prints a model, one variable per line. *)
fun print_model model = List.foldl
  (fn ((name, tm), _) => (print (" - " ^ name ^ ": "); Hol_pp.print_term tm))
  () (rev model);

fun to_sml_ints model = List.map (fn (name, tm) => (name, uint_of_word tm)) model;

(*val word_relation = bir2bool relation;*)
val word_relation = ``^(bir2bool relation) /\ (R1 <> R1')``;
val model = Z3_SAT_modelLib.Z3_GET_SAT_MODEL word_relation;
val _ = (print "SAT model:\n"; print_model model(*; print "\n"*));

val sml_model = to_sml_ints model;
fun isPrimedRun s = String.isSuffix "_" s;
val (s2,s1) = List.partition (isPrimedRun o fst) sml_model;


(* --------------------------------------- *)
(* test execution                          *)
(* --------------------------------------- *)

val test_result =  bir_embexp_run_cache_indistinguishability asm_file_contents s1 s2;

val _ = print ("result = " ^ (if test_result then "ok!" else "failed") ^ "\n\n");
