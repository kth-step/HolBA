(* The main structure provided by bir_inst_liftingLib is
   "bir_inst_lifting". It contains functions for lifting machine
   instructions and whole programs to bir programs.

   A module with this signature is provided for multiple architectures. *)

signature bir_inst_lifting = sig

  (* ------------------- *)
  (* Single instructions *)
  (* ------------------- *)

  (* bir_inst_lifting (mem_unchanged_begin, mem_unchanged_end) pc hexcode

     tries to lift the given hexcode. It assumes this code is stored at location
     of "pc" in memory and tries to guarantee that the memory addresses in
     interval [mem_unchanged_begin, mem_unchanged_end) are not changed. *)
  val bir_lift_instr : (Arbnum.num * Arbnum.num) -> Arbnum.num -> string -> Abbrev.thm


  (* Often we want to lift whole programs. For this, it is convenient to
     use a lower-level interface. This computes some facts about the unchanged memory
     region only once and caches hex-codes that occur multiple times. The
     work-flow is:

     val mu_thms = bir_lift_instr_prepare_mu_thms (mem_unchanged_begin, mem_unchanged_end);
     val cache0 = lift_inst_cache_empty;
     val (lift_thm1, cache1, cache_used1) = bir_lift_instr_mu mu_thms cache0 pc1 hex_code1
     val (lift_thm2, cache2, cache_used2) = bir_lift_instr_mu mu_thms cache1 pc2 hex_code2
     ...
     val (lift_thm_n, cache_n, cache_used_n) = bir_lift_instr_mu mu_thms cache_(n-1) pc_n hex_code_n

  *)
  type lift_inst_cache
  val lift_inst_cache_empty : lift_inst_cache

  (* The machine record used *)
  val mr : bir_lifting_machinesLib.bmr_rec

  val bir_lift_instr_prepare_mu_thms : (Arbnum.num * Arbnum.num) -> Abbrev.thm * Abbrev.thm;
  val bir_lift_instr_mu : (Abbrev.thm * Abbrev.thm) -> lift_inst_cache -> Arbnum.num -> string ->
    (Abbrev.thm * lift_inst_cache * bool);


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
                      (Abbrev.thm (* resulting theorem *) *
                       (* Errors in from: (PC, error_desc option),
                          where the exeption is always a bir_inst_liftingExn contain the
                          hex-code *)
                       ((Arbnum.num * exn option) list))

  (* Sometimes we want to lift a program that contains more than one code region.
     Or we want explicitly mark data in the hex-codes. bir_lift_prog_gen allows to
     do this. It gets a list of regions to translate. Each region is of the form

     (pc, is-code-region-flag, hex-codes). *)

  val bir_lift_prog_gen : (Arbnum.num * Arbnum.num) (* memory unchanged begin, end *) ->
                          (Arbnum.num * bool * string list) list (* list of regions *) ->
                          (Abbrev.thm * ((Arbnum.num * exn option) list))


  (* Reading and Writing code to and from intel hex files. The HEX files unluckily
     do not store whether it is a code or a data section. Therefore we always assume code. *)
  val read_hex_file : string -> (Arbnum.num * bool * string list) list
  val write_hex_file : string -> (Arbnum.num * bool * string list) list -> unit

end


(* Instances for different machine types *)
signature bir_inst_liftingLib = sig

  (* Errors are reported via the exception bir_inst_liftingExn (hex_code, reason)
     which indicates that lifting of the given hex-code failed for the given reason. *)
  datatype bir_inst_liftingExn_data =
     BILED_msg of string
   | BILED_msg_term of string * Abbrev.term
   | BILED_lifting_failed of Abbrev.term

  exception bir_inst_liftingExn of string * bir_inst_liftingExn_data;

  (* For debugging a printer *)
  val bir_inst_liftingExn_data_to_string : bir_inst_liftingExn_data -> string;

  (* ARM 8 instance *)
  structure bmil_arm8 : bir_inst_lifting;

end


(* Tests for ARM 8

   open bir_inst_liftingLib;
   open bmil_arm8

   fun hex_code_of_asm asm = hd (arm8AssemblerLib.arm8_code asm)

   val mu_b = Arbnum.fromInt 0;
   val mu_e = Arbnum.fromInt 0x100000;
   val pc = Arbnum.fromInt 0x10000;

   fun lift_instr hex_code = let
      val timer = (Time.now())
      val thm = bir_lift_instr (mu_b, mu_e) pc hex_code
      val d_time = Time.- (Time.now(), timer);
      val d_s = (Time.toString d_time);
   in
     (thm, d_s)
   end;

   fun lift_instr_asm asm =
     lift_instr (hex_code_of_asm asm)

   val lift_prog =
     bir_lift_prog (mu_b, mu_e) pc

   fun lift_prog_asm asm =
     lift_prog (map hex_code_of_asm asm)

   val (res, time) = lift_instr_asm `add x0, x1, x2`;
   val (res, time) = lift_instr_asm `add x1, x1, x1`;
   val (res, time) = lift_instr_asm `adds x0, x1, x2`;
   val (res, time) = lift_instr_asm `add x0, x0, x2`;
   val (res, time) = lift_instr_asm `sub x0, x1, x2`;
   val (res, time) = lift_instr_asm `mul x0, x1, x2`;
   val (res, time) = lift_instr_asm `mul w0, w1, w1`;
   val (res, time) = lift_instr_asm `cmp w0, #0`;
   val (res, time) = lift_instr_asm `cmn w0, #0`;
   val (res, time) = lift_instr_asm `cmn w0, w1`;
   val (res, time) = lift_instr_asm `cmn x0, x9`;
   val (res, time) = lift_instr_asm `ret`;
   val (res, time) = lift_instr_asm `adds x0, pc, #8`;
   val (res, time) = lift_instr_asm `adds x0, x2, #8`;
   val (res, time) = lift_instr_asm `subs x0, x2, #8`;
   val (res, time) = lift_instr_asm `adds x0, x1, x2`;
   val (res, time) = lift_instr_asm `add x0, x0, x2`;
   val (res, time) = lift_instr_asm `sub x0, x1, x2`;
   val (res, time) = lift_instr_asm `add x4, SP, #8`;
   val (res, time) = lift_instr_asm `adds x1, x1, #0`;
   val (res, time) = lift_instr_asm `ldr x0, [x2, #8]`;
   val (res, time) = lift_instr_asm `lsr x0, x2, x3`;
   val (res, time) = lift_instr_asm `lsl x0, x2, x3`;
   val (res, time) = lift_instr_asm `asr x0, x2, x3`;
   val (res, time) = lift_instr_asm `lsr x0, x1, #0`;

   val (res, time) = lift_instr_asm `str x0, [x2, #8]`;
   val (res, time) = lift_instr "A9B97BFD"
   val (res, time) = lift_instr "540002E1"
   val (res, time) = lift_instr "54000089"
   val (res, time) = lift_instr "B4000040"

   val (res, time) = lift_prog ["13047C00", "a9b97bfd", "eb1f001f"]

*)
