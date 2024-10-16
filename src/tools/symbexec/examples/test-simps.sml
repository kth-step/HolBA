open HolKernel Parse boolLib bossLib;


open birs_simpLib;
open birs_simp_instancesLib;

val default_exp_simp = birs_simp_default_core_exp_simp;
val armcm0_simp = birs_simp_default_armcm0_gen false;



val test_cases = [
  (default_exp_simp,
  ``BExp_BinExp BIExp_And
            (BExp_BinExp BIExp_And
               (BExp_BinExp BIExp_And
                  (BExp_UnaryExp BIExp_Not
                     (BExp_Den (BVar "sy_ModeHandler" (BType_Imm Bit1))))
                  (BExp_BinExp BIExp_And
                     (BExp_BinPred BIExp_Equal
                        (BExp_BinExp BIExp_And
                           (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)))
                           (BExp_Const (Imm32 3w))) (BExp_Const (Imm32 0w)))
                     (BExp_BinExp BIExp_And
                        (BExp_BinExp BIExp_And
                           (BExp_BinPred BIExp_LessThan
                              (BExp_Const (Imm32 0x10001FE0w))
                              (BExp_Den
                                 (BVar "sy_SP_process" (BType_Imm Bit32))))
                           (BExp_BinPred BIExp_LessOrEqual
                              (BExp_Den
                                 (BVar "sy_SP_process" (BType_Imm Bit32)))
                              (BExp_Const (Imm32 0x10001FF0w))))
                        (BExp_BinPred BIExp_LessOrEqual
                           (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
                           (BExp_Const (Imm64 0xFFFFF38w))))))
               (BExp_Den (BVar "syp_gen" (BType_Imm Bit1))))
            (BExp_UnaryExp BIExp_Not
               (BExp_BinPred BIExp_LessOrEqual
                  (BExp_BinExp BIExp_LeftShift (BExp_Const (Imm32 1w))
                     (BExp_Const (Imm32 16w)))
                  (BExp_Den (BVar "sy_R0" (BType_Imm Bit32)))))``,
  ``BExp_IfThenElse
                (BExp_BinPred BIExp_LessOrEqual
                   (BExp_BinExp BIExp_LeftShift (BExp_Const (Imm32 1w))
                      (BExp_Const (Imm32 16w)))
                   (BExp_Den (BVar "sy_R0" (BType_Imm Bit32))))
                (BExp_BinExp BIExp_Plus
                   (BExp_BinExp BIExp_Plus
                      (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
                      (BExp_Const (Imm64 4w))) (BExp_Const (Imm64 1w)))
                (BExp_BinExp BIExp_Plus
                   (BExp_BinExp BIExp_Plus
                      (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
                      (BExp_Const (Imm64 4w))) (BExp_Const (Imm64 3w)))``,
  ``(BExp_BinExp BIExp_Plus (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
       (BExp_Const (Imm64 (4w + 3w))))``)
];

(*
val (simp_fun, pcond, bexp, expected) = hd test_cases;
*)

fun test (simp_fun, pcond, bexp, expected) =
  let
    val simp_tm = birs_simp_gen_term pcond bexp;
    (*val _ = print_term simp_tm;*)
    val expected_thm_concl = subst [``symbexp':bir_exp_t`` |-> expected] simp_tm;
    val res_thm = simp_fun simp_tm;
    (*val _ = print_thm res_thm;*)
    val is_expected = identical expected_thm_concl (concl res_thm);

    val _ = if is_expected then () else (
        print "\nexpected:\n";
        print_term expected_thm_concl;
        print "\nwe have\n";
        print_thm res_thm;
        raise Fail "not as expected"
    );
  in () end;

val _ = List.app test test_cases;
