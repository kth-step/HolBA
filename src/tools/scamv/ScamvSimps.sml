structure ScamvSimps :> ScamvSimps =
struct

open HolKernel boolLib liteLib simpLib Parse bossLib;
open bir_auxiliaryTheory bir_immTheory bir_valuesTheory;
open bir_exp_immTheory bir_exp_memTheory bir_envTheory;
open bir_expTheory bir_programTheory bir_typing_progTheory;
open bir_typing_expTheory;

open HolBACoreSimps;

(* TODO: These should only be defined once in HolBA... *)

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
    end;

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

end
