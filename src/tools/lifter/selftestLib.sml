(**************************)
(* Testing infrastructure *)
(**************************)

(* Dummy so that we don't have to make separate Holmake stuff for test_bmr*)
structure selftestLib :> selftestLib = struct

  open PPBackEnd;

  (* TODO: Put test instances here? *)
  val sty_OK     = [FG Green];
  val sty_CACHE  = [FG Yellow];
  val sty_FAIL   = [FG OrangeRed];
  val sty_HEADER = [Bold, Underline];

end;

(* Struct for lifter testing *)
functor test_bmr (structure MD : bir_inst_lifting; structure log_name_str : sig val log_name: string end) = struct
(* For debugging:
  open bir_lifting_machinesLib_instances;
  structure MD = bmil_riscv;
structure log_name_str =
struct
  val log_name = "selftest_riscv.log";
end;

*)
  local

  open HolKernel boolLib liteLib simpLib Parse bossLib;
  open PPBackEnd;
  open bir_inst_liftingLibTypes bir_inst_liftingHelpersLib;

  (* TODO: Ideally, these should not be defined twice *)
  val sty_OK     = [FG Green];
  val sty_CACHE  = [FG Yellow];
  val sty_FAIL   = [FG OrangeRed];
  val sty_HEADER = [Bold, Underline];

  in
  (* Error at this point is only due to REPL not knowing difference between struct and module *)
  open MD;
  datatype lift_inst_cache = datatype MD.lift_inst_cache;

  open log_name_str;
  val log = TextIO.openOut log_name;

  (* Used internally for storing failed and succeeding hexcodes *)
  val failed_hexcodes_list = ref ([]:(string * string option * bir_inst_liftingExn_data option) list);
  val success_hexcodes_list = ref ([]: (string * string option * thm) list);

  (* Prints a string s to the log and to REPL (if f is true), using the style sty *)
  fun print_log_with_style sty f s = let
    val _ = if f then TextIO.output (log, s) else ();
    val _ = print_with_style_ sty s;
  in () end;
  (* The above with no style *)
  fun print_log s = print_log_with_style [] s;

  fun lift_instr_cached log_f mu_be mu_thms cache pc hex_code desc = let
    val hex_code = String.map Char.toUpper hex_code
    val _ = print_log log_f hex_code;
    val d' = case desc of
	      NONE => hex_code
	    | SOME d => (print_log log_f (" (" ^ d ^")"); d)
    val _ = print_log log_f (" @ 0x" ^ (Arbnum.toHexString pc));
    val timer = (Time.now())
    val (res, ed) = (SOME (bir_lift_instr_mu mu_be mu_thms cache pc hex_code d'), NONE) handle
		     bir_inst_liftingExn (_, d)  => (NONE, SOME d)
		   | HOL_ERR _ => (NONE, NONE);

    val d_time = Time.- (Time.now(), timer);
    val d_s = (Time.toString d_time);

    val _ = print_log log_f (" - ");
    val _ = print (d_s ^ " s - ");
    val (res', cache') = case res of
	       SOME (thm, cache', _) => ((SOME thm), cache')
	     | NONE => (NONE, cache)
    val _ = case res of
	       SOME (thm, _, cache_used) =>
		   (success_hexcodes_list := (hex_code, desc, thm)::(!success_hexcodes_list);
		   (print_log_with_style sty_OK log_f "OK");
		   (if cache_used then (print_log log_f " - "; print_log_with_style sty_CACHE log_f "cached") else ());
		   (print_log log_f "\n");
		   (if log_f then ((TextIO.output (log, thm_to_string thm));
				   (TextIO.output (log, "\n"))) else ()))
	     | NONE =>
	       (failed_hexcodes_list := (hex_code, desc, ed)::(!failed_hexcodes_list);
	       (print_log_with_style sty_FAIL log_f "FAILED\n"));
    val _ = case ed of
	NONE => ()
      | SOME d => (let
	  val s = ("   "^(bir_inst_liftingExn_data_to_string d) ^ "\n");
	in print_log_with_style sty_FAIL log_f s end)
    val _ = if log_f then TextIO.output (log, "\n") else ();
  in
    (res', ed, d_s, cache')
  end;

  fun lift_instr mu_b mu_e pc hex_code desc = let
    val mu_thms = bir_lift_instr_prepare_mu_thms (mu_b, mu_e)
    val (res, ed, d_s, _) = lift_instr_cached true (mu_b, mu_e) mu_thms lift_inst_cache_empty pc hex_code desc
  in
    (res, ed, d_s)
  end;


  (* And a list version *)

  fun lift_instr_list mu_b mu_e pc hex_codes = let
    val timer = (Time.now())
    val len_codes = (length hex_codes);

    val _ = print ("running " ^ (Int.toString (len_codes)) ^ " instrutions; first pc 0x" ^
		(Arbnum.toHexString pc) ^ "\n\n");

    val mu_thms = bir_lift_instr_prepare_mu_thms (mu_b, mu_e)

    fun run_inst (i, (c, pc, res, cache)) = let
      val _ = print ((Int.toString c) ^ "/" ^ (Int.toString (length hex_codes)) ^ ": ");
      val (r', ed, d_s, cache') = lift_instr_cached false (mu_b, mu_e) mu_thms cache pc i NONE
      val c' = c+1;
      val pc' = Arbnum.+ (pc, (#bmr_hex_code_size mr) i);
      val r = (r', ed, d_s);
    in (c+1, pc', r::res, cache') end

    val (_, _, resL, _) = foldl run_inst (1, pc, [], lift_inst_cache_empty) hex_codes

    val d_time = Time.- (Time.now(), timer);
    val d_s = (Time.toString d_time);
    val success_c = foldl (fn ((res, _, _), c) =>
	 if (is_some res) then c+1 else c) 0 resL
    val fail_c = len_codes - success_c

    val _ = print "\n";
    val _ = print ("Instructions OK    : " ^ (Int.toString success_c) ^ "\n");
    val _ = print ("Instructions FAILED: " ^ (Int.toString fail_c) ^ "\n");

    val _ = print ("Time needed        : " ^ d_s ^ " s\n\n");
  in
    (fail_c, success_c, resL)
  end;


  fun final_results name expected_failed_hexcodes = let
    val _ = print_log_with_style sty_HEADER true ("\n\n\nSUMMARY FAILING HEXCODES " ^ name ^ "\n\n");
    val _ = print_log true "\n";
    val failing_l = op_mk_set (fn (x, _, _) => fn (y, _, _) => (x = y)) (!failed_hexcodes_list)
    val ok_l = op_mk_set (fn (x, _, _) => fn (y, _, _) => (x = y)) (!success_hexcodes_list)

    (* look for freshly failing ones *)
    val failing_l' = map (fn (hc, d, edo) =>
       (hc, d, edo, not (Lib.mem hc expected_failed_hexcodes))) failing_l;
    val fixed_l = List.filter (fn hc => List.exists (fn (e, _, _) => e = hc) ok_l) expected_failed_hexcodes

    (* Show all failing instructions and format them such that they can be copied
       in the code of selftest.sml
       as content of list expected_failed_hexcodes *)
    val _ = print_log true ("Instructions FAILED: " ^ (Int.toString (length failing_l)) ^ "/" ^
	   (Int.toString (length failing_l + length ok_l)) ^ "\n\n");

    fun comment_of_failing desc ed_opt =
      case (desc, ed_opt) of
	   (NONE, NONE) => ""
	 | (SOME d, NONE) => (" (* " ^ d ^ " *)")
	 | (NONE, SOME d') => (" (* " ^ (bir_inst_liftingExn_data_to_string d') ^ " *)")
	 | (SOME d, SOME d') => (" (* " ^ d ^ "; "^(bir_inst_liftingExn_data_to_string d')  ^ " *)");

    fun print_failed [] = ()
      | print_failed ((hex_code, desc, ed_opt, broken)::l) =
    let
      (* print the ones that failed, but were not excepted to in red *)
      val st = if broken then sty_FAIL else [];
      val _ = print_log true "   ";
      val _ = print_log_with_style st true ("\""^hex_code^"\"");

      val _ = print_log_with_style st true (comment_of_failing desc ed_opt)

    in if List.null l then (print_log true "\n]\n\n") else
	   (print_log true ",\n"; print_failed l)
    end;
    val _ = if List.null failing_l' then () else (print "[\n"; print_failed failing_l');


    (* Show the hex-codes that were expected to fail, but succeeded. These
       are the ones fixed by recent changes. *)
    val _ = print_log true ("Instructions FIXED: " ^ (Int.toString (length fixed_l)) ^ "\n\n");
    val _ = List.map (fn s => print_log_with_style sty_OK true ("   " ^ s ^"\n")) fixed_l;
    val _ = print_log true "\n\n";

    (* Show the hex-codes that were expected to succeed, but failed. These
       are the ones broken by recent changes. *)
    val broken_l = List.filter (fn (hc, d, edo, br) => br) failing_l';
    val _ = print_log true ("Instructions BROKEN: " ^ (Int.toString (List.length broken_l)) ^ "\n\n");
    val _ = List.map (fn (hc, desc, ed_opt, _) => print_log_with_style sty_FAIL true ("   " ^ hc ^
	 (comment_of_failing desc ed_opt) ^ "\n")) broken_l;
    val _ = print_log true "\n\n";

  in
    ()
  end;

  fun close_log () =
    let
      val _ = TextIO.closeOut log
    in
      ()
    end;

  end
end;
