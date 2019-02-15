open HolKernel boolLib liteLib simpLib Parse bossLib;

structure bir_exec_auxLib =
struct


(*
  fun GEN_check_conv bir_exec_exp_conv_help var_eq_thm t =
    if not (is_bir_eval_exp t) then
      raise UNCHANGED
    else
      let
        val thm = ((bir_exec_env_read_conv var_eq_thm) THENC EVAL) t;
(*      SIMP_CONV (list_ss++HolBACoreSimps.holBACore_ss) [] t; *)
      in
        if not (((fn t => is_BVal_Imm t orelse is_BVal_Mem t) o snd o dest_eq o concl) thm) then (
          print "----------------";
          print_term t;
          print "----------------";
          raise ERR "bir_exec_exp_conv_help" "could not evaluate expression to value"
        ) else
          thm
      end;
*)

  fun GEN_match_conv is_tm_fun conv tm =
    if is_tm_fun tm then
      conv tm
    else if is_comb tm then
        ((RAND_CONV  (GEN_match_conv is_tm_fun conv)) THENC
         (RATOR_CONV (GEN_match_conv is_tm_fun conv))) tm
    else
      raise UNCHANGED
    ;


end
