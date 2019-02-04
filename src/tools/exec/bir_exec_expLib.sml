
open bir_expSyntax;

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

  val t = ``bir_eval_exp ^exp ^env``;
*)


  fun bir_exec_exp_conv_help t =
    if not (is_bir_eval_exp t) then
      raise UNCHANGED
    else
      EVAL t;
(*      SIMP_CONV (list_ss++HolBACoreSimps.holBACore_ss) [] t; *)

(*
bir_exec_exp_conv t
*)


  fun GEN_bir_eval_exp_conv conv tm =
    if is_bir_eval_exp tm then
      conv tm
    else if is_comb tm then
        ((RAND_CONV  (GEN_bir_eval_exp_conv conv)) THENC
         (RATOR_CONV (GEN_bir_eval_exp_conv conv))) tm
    else
      raise UNCHANGED
    ;


  val bir_exec_exp_conv = GEN_bir_eval_exp_conv bir_exec_exp_conv_help;


end
