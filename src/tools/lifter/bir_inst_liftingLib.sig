(* The main structure provided by bir_inst_liftingLib is
   "bir_inst_lifting". It contains functions for lifting machine
   instructions and whole programs to bir programs.

   A module with this signature is provided for multiple architectures. *)

open Abbrev
open bir_inst_liftingLibTypes

signature bir_inst_lifting = sig

  (* ------------------- *)
  (* Single instructions *)
  (* ------------------- *)

  (* bir_inst_lifting (mem_unchanged_begin, mem_unchanged_end) pc hexcode hexcode-human

     tries to lift the given hexcode. It assumes this code is stored at location
     of "pc" in memory and tries to guarantee that the memory addresses in
     interval [mem_unchanged_begin, mem_unchanged_end) are not changed.
     The pc has be be inside this unchanged memory region.
     The label created from the resulting bir-program stores the string "hexcode-human",
     but does not use it in any way. It is supposed to be an annotation for human readers
     explained the HEX-code (e.g. containing a readable representation).
  *)
  val bir_lift_instr : (Arbnum.num * Arbnum.num) -> Arbnum.num -> string -> string -> thm


  (* Sometimes we want to lift many instructions that all use the same
     unchanged memory region. For this, it is convenient to
     use a lower-level interface. This computes some facts about the unchanged memory
     region only once and caches hex-codes that occur multiple times. The
     work-flow is:

     val mu_thms = bir_lift_instr_prepare_mu_thms (mem_unchanged_begin, mem_unchanged_end);
     val cache0 = lift_inst_cache_empty;
     val (lift_thm1, cache1, cache_used1) = bir_lift_instr_mu (mem_unchanged_begin, mem_unchanged_end) mu_thms cache0 pc1 hex_code1
     val (lift_thm2, cache2, cache_used2) = bir_lift_instr_mu (mem_unchanged_begin, mem_unchanged_end) mu_thms cache1 pc2 hex_code2
     ...
     val (lift_thm_n, cache_n, cache_used_n) = bir_lift_instr_mu (mem_unchanged_begin, mem_unchanged_end) mu_thms cache_(n-1) pc_n hex_code_n

  *)
  type lift_inst_cache
  val lift_inst_cache_empty : lift_inst_cache

  (* The machine record used *)
  val mr : bir_lifting_machinesLib.bmr_rec

  val bir_lift_instr_prepare_mu_thms : (Arbnum.num * Arbnum.num) -> thm * thm;
  val bir_lift_instr_mu : (Arbnum.num * Arbnum.num) -> (thm * thm) -> lift_inst_cache -> Arbnum.num -> string -> string ->
    (thm * lift_inst_cache * bool);


  (* --------------------------- *)
  (* Whole programs instructions *)
  (* --------------------------- *)

  (* A whole program is given as a list of hex-codes. Moreover, the unchanged memory region
     and the start memory address need to be provided. Caches are used automatically.
     Some debugging can be enabled by setting the trace "bir_inst_lifting.DEBUG_LEVEL".
     "0" means no-output, "1" minimal output and "2" verbose output. The default is "1".
     It returns the theorem that describes the lifted program as well as
     a list of instructions that could not be lifted. If the list of
     hex-codes contains data entries that are not supposed to be interpreted as instructions,
     this can happen without making the result less useful.

     Example:


     set_trace "bir_inst_lifting.DEBUG_LEVEL" 2

     bir_lift_prog (Arbnum.fromInt 0, Arbnum.fromInt 0x1000)
                   (Arbnum.fromInt 0x100) ["D10143FF","F9000FE0","B90017E1"];
  *)

  val bir_lift_prog : (Arbnum.num * Arbnum.num) (* memory unchanged begin, end *) ->
                      Arbnum.num (* initial address *) ->
                      string list (* hex-codes *) ->
                      (thm (* resulting theorem *) *
                       (* Errors in from: (PC, hex-code, error_data option),
                          where error_data is always bir_inst_liftingExn_data  *)
                       ((Arbnum.num * string *
                         bir_inst_liftingExn_data option) list))

  (* Sometimes we want to lift a program that contains more than one code region.
     Or we want explicitly mark data in the hex-codes. bir_lift_prog_gen allows to
     do this. It gets a list of regions to translate. Regions are described in
     bir_inst_liftingLibTypes. *)

  val bir_lift_prog_gen : (Arbnum.num * Arbnum.num) (* memory unchanged begin, end *) ->
                          (bir_inst_lifting_mem_region list) (* list of regions *) ->
                          (thm * ((Arbnum.num * string * bir_inst_liftingExn_data option) list))


  (* Reading and Writing code to and from intel hex files. The HEX files unluckily
     do not store whether it is a code or a data section. Therefore we always assume code. *)
  val read_hex_file : string -> bir_inst_lifting_mem_region list
  val write_hex_file : string -> bir_inst_lifting_mem_region list -> unit

end

(* Instances for different machine types *)
signature bir_inst_liftingLib = sig

  (* ARM 8 instance *)
  structure bmil_arm8 : bir_inst_lifting

  (* M0 instance, little endian, process SP *)
  structure bmil_m0_LittleEnd_Process : bir_inst_lifting;

  (* M0 instance, little endian, main SP *)
  structure bmil_m0_LittleEnd_Main : bir_inst_lifting;

  (* M0 instance, big endian, process SP *)
  structure bmil_m0_BigEnd_Process : bir_inst_lifting;

  (* M0 instance, big endian, main SP *)
  structure bmil_m0_BigEnd_Main : bir_inst_lifting;

end
