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



val btautology = ``BExp_Const (Imm1 1w)``;
val prem_init = ``^btautology``; (*``BExp_Const (Imm1 precond_v)``;*) (* have another premise here *)

val goalterm = ``bir_exp_is_taut (bir_exp_imp ^prem_init (bir_exp_varsubst FEMPTY ^def_const))``;



(* ----------- measurement overhead ----------- *)
val _ = if not runMeasurement then () else
        Lib.end_time timer_start;
val timer_start = Lib.start_time ();


val simp_thm = bir_wp_simp_CONV varexps_thms goalterm;
(*
val timer_start = Lib.start_time ();
val simp_thm = bir_wp_simp_CONV varexps_thms goalterm;
val _ = Lib.end_time timer_start;
*)


(* ----------- measurement end ----------- *)
val _ = if not runMeasurement then () else
        Lib.end_time timer_start;



val aes_wp_taut_thm = save_thm("aes_wp_taut_thm", simp_thm);




val _ = export_theory();

