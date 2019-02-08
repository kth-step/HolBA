open HolKernel boolLib liteLib simpLib Parse bossLib;

open bir_expSyntax;
open bir_valuesSyntax;

open bir_exec_envLib;

structure bir_exec_expLib =
struct

(*
  val env = ``BEnv (FEMPTY |+ ("bit1", (BType_Bool,      SOME (BVal_Imm (Imm1  0w))))
                           |+ ("R1",   (BType_Imm Bit32, SOME (BVal_Imm (Imm32 3w))))
                           |+ ("R2",   (BType_Imm Bit32, SOME (BVal_Imm (Imm32 4w))))
                           |+ ("R3",   (BType_Imm Bit32, SOME (BVal_Imm (Imm32 5w))))
                   )``;
  val env = ``BEnv (FEMPTY |+ ("bit1", (BType_Bool,      SOME (BVal_Imm (Imm1  0w))))
                           |+ ("R1",   (BType_Imm Bit32, SOME (BVal_Imm (Imm32 3w))))
                           |+ ("R2",   (BType_Imm Bit32, SOME (BVal_Imm (Imm32 4w))))
                           |+ ("R3",   (BType_Imm Bit32, SOME (BVal_Imm (Imm8 5w))))
                   )``;

  val exp = ``(BExp_MSB Bit32 (BExp_Den (BVar "R1" (BType_Imm Bit32))))``;
  val exp = ``(BExp_BinExp BIExp_Plus
                   (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                   (BExp_Den (BVar "R3" (BType_Imm Bit32))))``;


  val t = ``(bir_eval_bin_exp BIExp_Plus
                   (bir_env_read (BVar "R2" (BType_Imm Bit32))
                      (BEnv
                         (FEMPTY |+
                          ("R1",BType_Imm Bit32,
                           SOME (BVal_Imm (Imm32 0w))) |+
                          ("bit1",BType_Imm Bit1,
                           SOME (BVal_Imm (Imm1 0w))) |+
                          ("R3",BType_Imm Bit32,
                           SOME (BVal_Imm (Imm32 25w))) |+
                          ("R2",BType_Imm Bit32,
                           SOME (BVal_Imm (Imm32 7w))))))
                   (bir_env_read (BVar "R3" (BType_Imm Bit32))
                      (BEnv
                         (FEMPTY |+
                          ("R1",BType_Imm Bit32,
                           SOME (BVal_Imm (Imm32 0w))) |+
                          ("bit1",BType_Imm Bit1,
                           SOME (BVal_Imm (Imm1 0w))) |+
                          ("R3",BType_Imm Bit32,
                           SOME (BVal_Imm (Imm32 25w))) |+
                          ("R2",BType_Imm Bit32,
                           SOME (BVal_Imm (Imm32 7w)))))))``;


  val t = ``bir_eval_exp ^exp ^env``;
*)


  fun bir_exec_exp_conv_help var_eq_thm t =
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


  fun GEN_bir_eval_exp_conv conv tm =
    if is_bir_eval_exp tm then
      conv tm
    else if is_comb tm then
        ((RAND_CONV  (GEN_bir_eval_exp_conv conv)) THENC
         (RATOR_CONV (GEN_bir_eval_exp_conv conv))) tm
    else
      raise UNCHANGED
    ;


  val bir_exec_exp_conv = (GEN_bir_eval_exp_conv o bir_exec_exp_conv_help);


end
