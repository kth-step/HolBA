open bir_exp_memTheory;

fun simp_conv_load_store match_tm =
  let
    val store_tm = (el 1 o snd o strip_comb) match_tm;
    val eval_store_thm =
      computeLib.RESTR_EVAL_CONV [``bir_store_in_mem``] store_tm;
    val bir_store_in_mem_thm =
      EVAL (#2 ((TypeBase.dest_case o rhs o concl) eval_store_thm));
    val bir_load_thm =
      REWRITE_RULE [type_of_bir_imm_def]
	(HO_MATCH_MP bir_store_load_mem_THM bir_store_in_mem_thm);
    val final_thm1 =
      computeLib.RESTR_EVAL_CONV [``bir_load_from_mem``] match_tm
  in
    SIMP_RULE std_ss [bir_load_thm] final_thm1
  end
;

val bir_load_store_ss =
  SSFRAG {ac = [],
          congs = [],
          convs = [{conv = K (K simp_conv_load_store),
                    key= SOME ([],
                               ``bir_eval_load
                                   (bir_eval_store (SOME (BVal_Mem at vt mmap))
                                     (SOME (BVal_Imm addr))
                                     en
                                     (SOME (BVal_Imm va))
                                   )
                                   (SOME (BVal_Imm load_addr))
                                   en
                                   t``),
                    name = "simp_conv_load_store",
                    trace = 2}],
          dprocs = [],
          filter = NONE,
          name = SOME "bir_load_store_ss",
          rewrs = []};


(* USAGE:
 
val e2 = ``(BExp_UnaryExp BIExp_Not
         (BExp_BinPred BIExp_Equal
            (BExp_Load
               (BExp_Store (BExp_MemConst Bit64 Bit8 MM)
                  (BExp_BinExp BIExp_Plus
                     (BExp_Const (Imm64 (0x800003FFFFFFFFCBw :word64)))
                     (BExp_Const (Imm64 (45w :word64)))) BEnd_LittleEndian
                  (BExp_Const (Imm64 (0x8000000000000000w :word64))))
               (BExp_BinExp BIExp_Plus
                  (BExp_Const (Imm64 (0x800003FFFFFFFFCBw :word64)))
                  (BExp_Const (Imm64 (45w :word64)))) BEnd_LittleEndian Bit64)
            (BExp_Const (Imm64 (0w :word64)))))
``;

val restr_eval_tm = computeLib.RESTR_EVAL_CONV [``bir_eval_load``, ``bir_eval_store``] ``bir_eval_exp ^e2 (BEnv (K NONE))``;

SIMP_RULE (std_ss++bir_load_store_ss) [] restr_eval_tm;
*)
