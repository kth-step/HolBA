structure bir_exec_expLib =
struct

  open HolKernel boolLib liteLib simpLib Parse bossLib;

  open bir_expTheory;
  open bir_expSyntax;
  open bir_valuesSyntax;

  open bir_exec_auxLib;
  open bir_exec_envLib;

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


  val t = ``(bir_eval_exp
                   (BExp_Store
                      (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                      (BExp_BinExp BIExp_Plus
                         (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 24w))) BEnd_LittleEndian
                      (BExp_Den (BVar "R0" (BType_Imm Bit64))))
                   <|bst_pc :=
                       <|bpc_label := BL_Address (Imm64 0x400524w);
                         bpc_index := 2|>;
                     bst_environ :=
                       BEnv
                         (FEMPTY |+
                          ("R30",BType_Imm Bit64,
                           SOME (BVal_Imm (Imm64 0w))) |+
                          ("ProcState_Z",BType_Imm Bit1,
                           SOME (BVal_Imm (Imm1 0w))) |+
                          ("ProcState_V",BType_Imm Bit1,
                           SOME (BVal_Imm (Imm1 0w))) |+
                          ("ProcState_N",BType_Imm Bit1,
                           SOME (BVal_Imm (Imm1 0w))) |+
                          ("ProcState_C",BType_Imm Bit1,
                           SOME (BVal_Imm (Imm1 0w))) |+
                          ("R3",BType_Imm Bit64,
                           SOME (BVal_Imm (Imm64 0w))) |+
                          ("R2",BType_Imm Bit64,
                           SOME (BVal_Imm (Imm64 0w))) |+
                          ("R1",BType_Imm Bit64,
                           SOME (BVal_Imm (Imm64 0w))) |+
                          ("R0",BType_Imm Bit64,
                           SOME (BVal_Imm (Imm64 0w))) |+
                          ("MEM",BType_Mem Bit64 Bit8,
                           SOME (BVal_Mem Bit64 Bit8 (K 0))) |+
                          ("SP_EL0",BType_Imm Bit64,
                           SOME
                             (BVal_Imm (Imm64 0xFFFFFFFFFFFFFF90w))));
                     bst_status := BST_Running|>.bst_environ)``;

bir_exec_exp_conv var_eq_thms t

open bir_exp_memTheory;
bir_update_mmap_def

*)


(* TODO: improve evaluation completion checks and generalize these functions everywhere *)
(* TODO: generally: improve rewriting, select proper theorems and organize reusably in separate lists according to respective goals *)
  fun bir_exec_exp_conv var_eq_thms =
    let
      val is_tm_fun = is_bir_eval_exp;
      val check_tm_fun = (fn t => is_BVal_Imm t orelse is_BVal_Mem t);
      val conv = ((REWRITE_CONV [bir_eval_exp_def]) THENC (bir_exec_env_read_conv var_eq_thms) THENC
                  (computeLib.RESTR_EVAL_CONV [``bir_store_in_mem``]) THENC
                  (REWRITE_CONV [bir_exp_memTheory.bir_store_in_mem_REWRS]) THENC EVAL);
(*      (SIMP_CONV (list_ss++HolBACoreSimps.holBACore_ss) []); *)
    in
      GEN_selective_conv is_tm_fun check_tm_fun conv
    end;

end
