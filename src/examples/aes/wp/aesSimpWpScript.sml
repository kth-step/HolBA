open HolKernel Parse;

open aesWpsTheory;

open bir_wp_expLib;
open bir_wp_simpLib;



val _ = new_theory "aesSimpWp";



(* ----------- measurement start ----------- *)
val runMeasurement = true;
val timer_start = Lib.start_time ();


val lbl_list = (gen_lbl_list o snd o dest_eq o concl) aes_wps1_def;


val varexps_thms = preproc_vars [] (tl (rev lbl_list));


(* provide the number of arm instructions to take for the simplification, counted from the end of the computed block *)
val take_all = true;
val i = 100; (*60 - 230;*)

val i_min = 1;
val i_max = (List.length lbl_list) - 1;
val i = if take_all then
          i_max
        else
          Int.max (i_min, Int.min (i_max, i));

val lbl_str = List.nth (lbl_list, (List.length lbl_list) - 2 - i + 1);

val def_thm = lookup_def ("bir_wp_comp_wps_iter_step2_wp_" ^ lbl_str);
val def_const = (fst o dest_eq o concl) def_thm;




(*val btautology = ``BExp_Const (Imm1 1w)``;*)
(* translated from roberto's z3 precondition *)
val prem_init = ``BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_And
                      (BExp_BinPred BIExp_Equal (BExp_BinExp BIExp_And
                                                   (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                                                   (BExp_Const (Imm64 7w)))
                                                (BExp_Const (Imm64 0w)))
                      (BExp_UnaryExp BIExp_Not (BExp_BinPred BIExp_LessOrEqual
                                                  (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                                                  (BExp_Const (Imm64 33554432w)))))
                    (BExp_BinPred BIExp_LessOrEqual
                                                  (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                                                  (BExp_Const (Imm64 43554432w)))``;

val prem_init = ``BExp_BinExp BIExp_And ^prem_init (
                    (BExp_BinPred BIExp_Equal (BExp_BinExp BIExp_And
                                                   (BExp_Den (BVar "R0_post" (BType_Imm Bit64)))
                                                   (BExp_Const (Imm64 3w)))
                                                (BExp_Const (Imm64 0w)))
                  )``;


val aes_prem_def = Define `aes_prem = ^prem_init`;
val varexps_thms = (preproc_vars_thm true [] aes_prem_def)::varexps_thms;


val goalterm = ``bir_exp_is_taut (bir_exp_imp aes_prem (bir_exp_varsubst FEMPTY ^def_const))``;


(*ASSUME (simp_construct_wt (simp_extract goalterm) NONE);*)
val wt0_thm = prove (``^(simp_construct_wt (simp_extract goalterm) NONE)``,
  CONV_TAC (well_typed_conv varexps_thms)
);



(* ----------- measurement preprocessing ----------- *)
val _ = if not runMeasurement then () else
        Lib.end_time timer_start;
val timer_start = Lib.start_time ();


val (simp_thm,wt_thm) = bir_wp_simp_CONV varexps_thms goalterm wt0_thm;


(* ----------- measurement end ----------- *)
val _ = if not runMeasurement then () else
        Lib.end_time timer_start;



val wp_simp_term = (snd o dest_comb o snd o dest_comb o snd o dest_eq o concl) simp_thm;
val wp_simp_def = Define `wp_simp = ^wp_simp_term`;


val aes_wp_taut_thm = save_thm("aes_wp_taut_thm", REWRITE_RULE [GSYM wp_simp_def] simp_thm);
val aes_wp_wt_thm = save_thm("aes_wp_wt_thm", REWRITE_RULE [GSYM wp_simp_def] wt_thm);




val _ = export_theory();

