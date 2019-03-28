structure m0_mod_stepLib =
struct

  open HolKernel Parse boolLib bossLib;

  open m0_mod_stepTheory;

(*
open m0Theory m0_stepTheory;
open m0_stepLib;


val hex_code = "b510"
val hex_code = "f000f858"
val hex_code = "3202"
val hex_code = "4A15"

val hex_code = "635C"
val hex_code = "70E8"
val hex_code = "B570"
val hex_code = "BD70"
val hex_code = "B510"
val hex_code = "4770"
val hex_code = "0100"

val hex_code = "B285"
val hex_code = "8028"
val hex_code = "4182"
val hex_code = "4088";
val hex_code = "BA18";
val hex_code = "BDF7";
val hex_code = "B5F7"
val hex_code = "2200";
val hex_code = "2204";
val hex_code = "4084"
val hex_code = "40C4"
val hex_code = "1ACC";
val hex_code = "1E08"
val hex_code = "4251"
val hex_code = "40C4"
val hex_code = "4088"
val hex_code = "BA51";
val hex_code = "BAD1"
val hex_code = "41C8"


val endian_fl = false;
val sel_fl = true;

val thms = m0_stepLib.thumb_step_hex (endian_fl, sel_fl) hex_code;


NextStateM0_def


Next_def

Fetch_def
Decode_def
Run_def

DecodeThumb_def

dfn'Undefined_def
*)
(*
bir_is_lifted_prog_def
*)

  (* step function *)
  fun thumb_mod_step_hex (endian_fl, sel_fl) =
    let
      val thumb_step_hex' = m0_stepLib.thumb_step_hex (endian_fl, sel_fl);

      (*
      val [thm] = thms;
      *)
      open optionSyntax;
      open numSyntax;
      open wordsSyntax;
      val m0_state_count_tm = ``m0_state_count``;
      val var_s_tm = ``s:m0_state``;
      val s_tm = ``m0_mod_inv sm``;
      val n64_ty = Type `:64`;
      val m0_state_type_ss = rewrites (type_rws ``:m0_state``);
      val m0_mod_state_type_ss = rewrites (type_rws ``:m0_mod_state``);
      fun mod_thm thm =
	let
	  val new_state = (dest_some o snd o dest_eq o concl) thm;
	  val new_count = (snd o dest_eq o concl o EVAL o mk_comb) (m0_state_count_tm, new_state);
	  val d_tm = (snd o dest_eq o concl o (SIMP_CONV arith_ss []))
		     (mk_minus (new_count, mk_comb (m0_state_count_tm,var_s_tm)));
	  val d_n2w_tm = (snd o dest_eq o concl o EVAL) (mk_n2w (d_tm, n64_ty));

	  val thm' = INST [var_s_tm |-> s_tm] thm;
	  val thm_mod_gen = SPEC d_n2w_tm (MATCH_MP m0_mod_step_gen_thm thm');

	  val thm_mod1 = CONV_RULE ((LAND_CONV (EVAL)) THENC (REWRITE_CONV [])) thm_mod_gen;
	  val thm_mod2 = CONV_RULE ((LAND_CONV (EVAL)) THENC (REWRITE_CONV [])) thm_mod1;
	  val thm_mod3 = CONV_RULE ((LAND_CONV (EVAL)) THENC (REWRITE_CONV [])) thm_mod2;
	  val thm_mod4 = UNDISCH thm_mod3;

	  val thm_mod5 = (UNDISCH_ALL o
			  (SIMP_RULE (std_ss++m0_state_type_ss++m0_mod_state_type_ss)
				     [m0_mod_inv_def]) o
			  DISCH_ALL) thm_mod4;
	in
	  thm_mod5
	end;
    in
      fn hex_code =>
      let
	val thms = thumb_step_hex' hex_code;

	val thms_mod = List.map mod_thm thms;
      in
	thms_mod
      end
    end;

  (*
  val hex_code = "41C8"

  val endian_fl = false;
  val sel_fl = true;

  val thumb_mod_step_hex' = thumb_mod_step_hex (endian_fl, sel_fl);

  val thms_mod = thumb_mod_step_hex' hex_code;
  *)


end
