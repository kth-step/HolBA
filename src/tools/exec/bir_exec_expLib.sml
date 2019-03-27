structure bir_exec_expLib =
struct

  open HolKernel boolLib liteLib simpLib Parse bossLib;

  open bir_expTheory;
  open bir_expSyntax;
  open bir_valuesSyntax;

  open bir_exec_auxLib;
  open bir_exec_envLib;
  open bir_exp_memTheory;

  open optionTheory;
  open combinTheory;
  open combinSyntax;

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

  val t = ``(bir_eval_exp
                     (BExp_Store
                        (BExp_Den (BVar "Mem" (BType_Mem Bit64 Bit8)))
                        (BExp_Const (Imm64 25w)) BEnd_LittleEndian
                        (BExp_Const (Imm64 25w)))
                     <|bst_pc :=
                         <|bpc_label := BL_Label "entry"; bpc_index := 1|>;
                       bst_environ :=
                         BEnv
                           (FEMPTY |+
                            ("R0",BType_Imm Bit64,SOME (BVal_Imm (Imm64 0w))) |+
                            ("Mem",BType_Mem Bit64 Bit8,
                             SOME
                               (BVal_Mem Bit64 Bit8
                                  ((32 =+ 0)
                                     ((31 =+ 0)
                                        ((30 =+ 0)
                                           ((29 =+ 0)
                                              ((28 =+ 0)
                                                 ((27 =+ 0)
                                                    ((26 =+ 0)
                                                       ((25 =+ 26) (K 0))))))))))));
                       bst_status := BST_Running|>.bst_environ)``;

bir_exec_exp_conv var_eq_thms t

val t = ``(bir_update_mmap Bit64
          ((32 =+ 0:num)
             ((31 =+ 0)
                ((30 =+ 0)
                   ((29 =+ 0)
                      ((28 =+ 0) ((27 =+ 0) ((26 =+ 0) ((25 =+ 26) (K 0)))))))))
          25
          [SEG 8 56 (w2v (25w:word64)); SEG 8 48 (w2v (25w:word64)); SEG 8 40 (w2v (25w:word64));
           SEG 8 32 (w2v (25w:word64)); SEG 8 24 (w2v (25w:word64)); SEG 8 16 (w2v (25w:word64));
           SEG 8 8 (w2v (25w:word64)); SEG 8 0 (w2v (25w:word64))])``;

bir_exec_bir_update_mmap_conv t

val ct = ``((25:num =+ 25:num)
          ((32 =+ 0)
             ((31 =+ 0)
                ((30 =+ 0)
                   ((29 =+ 0)
                      ((28 =+ 0) ((27 =+ 0) ((26 =+ 0) ((25 =+ 26) (K 0))))))))))``;

open bir_exp_memTheory;
bir_update_mmap_def

*)



(*
  val bir_update_mmap_purge_thm = prove(``
    (!mmap aty a. bir_update_mmap aty mmap a [] = mmap) /\
    (!mmap aty a v vs. bir_update_mmap aty mmap a (v::vs) =
                       bir_update_mmap aty ((bir_mem_addr aty a =+ v2n v) mmap) (SUC a) vs)
  ``,
    REWRITE_TAC [bir_update_mmap_def]
  );
UPDATE_COMMUTES
UPDATE_EQ

is_bir_update_mmap t
*)


val UPDATE_COMMUTES_num = prove(``
  !f:num->num a:num b:num c:num d:num. (a <> b) ==>
                                       ((a =+ c) ((b =+ d) f) = (b =+ d) ((a =+ c) f))
``,
  REWRITE_TAC [UPDATE_COMMUTES]
);

val UPDATE_EQ_num = prove(``
  !f:num->num a:num b:num c:num d:num. (a = b) ==>
                                       ((a =+ c) ((b =+ d) f) = (a =+ c) f)
``,
  SIMP_TAC std_ss [UPDATE_EQ]
);

fun syntax_fns n d m = HolKernel.syntax_fns {n = n, dest = d, make = m} "bir_exp_mem";
val (bir_update_mmap_tm,  mk_bir_update_mmap, dest_bir_update_mmap, is_bir_update_mmap)  =
  (syntax_fns 5 HolKernel.dest_quadop HolKernel.mk_quadop) "bir_update_mmap";

  val bir_exec_bir_update_mmap_conv =
    let
      val is_tm_fun = is_bir_update_mmap;
      val check_tm_fun = K true;
      fun conv t =
        let
          fun combin_purge_conv ct =
            if is_update_comb ct then
              let val ((a1,v1),ct2) = dest_update_comb ct; in
                if is_update_comb ct2 then
                  let
                    val ((a2,v2), ct3) = dest_update_comb ct2;
                    val a_eq_thm = (EVAL o mk_eq) (a1, a2);
                    val a_eq_thm' = SIMP_RULE pure_ss [boolTheory.EQ_CLAUSES] a_eq_thm;
                    val a_is_eq = (snd o dest_eq o concl) a_eq_thm;

                    val ct_thm =
                      if a_is_eq = F then
                        MP (SPECL [ct3, a1, a2, v1, v2] UPDATE_COMMUTES_num) a_eq_thm'
                      else if a_is_eq = T then
                        MP (SPECL [ct3, a1, a2, v1, v2] UPDATE_EQ_num) a_eq_thm'
                      else
                        raise UNCHANGED;
                    (*val _ = print "\n------------\n";
                    val _ = print_term (concl ct_thm);*)
                  in
                    CONV_RULE (RAND_CONV (RAND_CONV combin_purge_conv)) ct_thm
                  end
                else
                  raise UNCHANGED
              end
            else
              raise UNCHANGED;

(*
val ct = ``((25:num =+ 25:num) ((25 =+ 26) (K 0)))``;
combin_purge_conv ``((25:num =+ 25:num) ((25 =+ 26) (K 0)))``

val ct_thm = (ASSUME ``(25:num =+ 25:num) ((26 =+ 0) ((25 =+ 26) (K 0))) =
(26 =+ 0) ((25 =+ 25) ((25 =+ 26) (K 0)))``)

CONV_RULE (RAND_CONV (RAND_CONV (fn x => (print_term (x); REFL x)   ))) ct_thm
*)

(*
          val thm1 = REWRITE_CONV [Once bir_update_mmap_def] t;
          val thm2 = if not (is_bir_update_mmap ((snd o dest_eq o concl) thm1)) then thm1 else
                CONV_RULE (RAND_CONV (
                  (RATOR_CONV (LAND_CONV (EVAL THENC combin_purge_conv))) THENC
                  (bir_exec_bir_update_mmap_conv)
                )) thm1;
          val thm2 = REPEATC (
                  (REWRITE_CONV [Once bir_update_mmap_def]) THENC
                  (RATOR_CONV (LAND_CONV (EVAL THENC combin_purge_conv)))
                ) t;
*)


          val thm2 = REPEATC (
                  (fn x => REWRITE_CONV [Once bir_update_mmap_def] x) THENC
                  (fn x => if is_bir_update_mmap x then
                             RATOR_CONV (LAND_CONV (EVAL THENC combin_purge_conv)) x
                           else
                             raise UNCHANGED)
                ) t;

        in
          thm2
        end;
    in
      GEN_selective_conv is_tm_fun check_tm_fun conv
    end;

(* TODO: improve evaluation completion checks and generalize these functions everywhere *)
(* TODO: generally: improve rewriting, select proper theorems and organize reusably in separate lists according to respective goals *)
  fun bir_exec_exp_conv var_eq_thms =
    let
      val is_tm_fun = is_bir_eval_exp;
      val check_tm_fun = (fn t => is_BVal_Imm t orelse is_BVal_Mem t);
      fun conv t =
        let
          val preproc_conv =
                (REWRITE_CONV [bir_eval_exp_def]) THENC
                (bir_exec_env_read_conv var_eq_thms) THENC
                (computeLib.RESTR_EVAL_CONV [``bir_store_in_mem``]) THENC
                (REWRITE_CONV [bir_store_in_mem_REWRS]) THENC
                (REWRITE_CONV [option_CLAUSES]);

          val thm1 = preproc_conv t;

          val thm2 = CONV_RULE (RAND_CONV (
                  (bir_exec_bir_update_mmap_conv) THENC
                  (EVAL)
                )) thm1;
(*
          val thm2 = CONV_RULE (RAND_CONV (
                  (REWRITE_CONV [Once bir_update_mmap_purge_thm]) THENC
                  (REWRITE_CONV [EVAL ``bir_mem_addr Bit64 25``]) THENC
                  (SIMP_CONV (arith_ss++combinSimps.COMBIN_ss) [])
                )) thm1;
*)
(*
          val thm2 = CONV_RULE (RAND_CONV (
                  (REWRITE_CONV [bir_update_mmap_purge_thm]) THENC
                  EVAL
                )) thm1;
          (* val thm3 = CONV_RULE (RAND_CONV EVAL) thm1; *)
          (*      (SIMP_CONV (list_ss++HolBACoreSimps.holBACore_ss) []); *)
*)
        in
          thm2
        end;
    in
      GEN_selective_conv is_tm_fun check_tm_fun conv
    end;

end
