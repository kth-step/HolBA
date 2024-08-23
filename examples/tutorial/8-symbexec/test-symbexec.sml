open HolKernel Parse boolLib bossLib;

open birs_auxLib;
open bir_symbLib;
open birsSyntax;
open bslSyntax;

open bir_prog_add_regTheory;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;

val _ = print "loading...\n";

(* ----------------------------------------- *)
(* input selection                           *)
(* ----------------------------------------- *)
val progname = "add_reg";
val prog_def = bir_add_reg_prog_def;
val lift_thm = bir_add_reg_arm8_lift_THM;

(* define binary inputs *)
val get_x = bden (bvarimm64 "R0");
val get_sp = bden (bvarimm64 "SP_EL0");

(* predefined preconditions *)
val precond_0 = btrue;
val precond_1 = beq(bconst64 5, bconst64 7);
val precond_2 = beq(bconst64 5, bconst64 5);
val precond_3 = bslt(get_x, bconst64 2);
val precond_4 = bandl [precond_3, beq(get_sp,bconst64 0x80000000)];
val precond_5 = bandl [bnot (bslt(get_x, bconst64 0)), precond_3, beq(get_sp,bconst64 0x80000000)];
val precond_6 = bandl [beq(get_x, bconst64 0), beq(get_sp,bconst64 0x80000000)];
val precond_7 = bandl [beq(get_x, bconst64 1), beq(get_sp,bconst64 0x80000000)];

(* select precondition *)
val precond = precond_7;


(* endpoint *)
val endpoint_0 = ``0x3cw:word64``; (* before loop back *)
val endpoint_1 = ``0x4cw:word64``; (* after loop back, at the function return, practically an endless loop *)

(* select endpoint *)
val endpoint = endpoint_0;

(* ----------------------------------------- *)
(* Program variable definitions and theorems *)
(* ----------------------------------------- *)

val bir_tutorial_prog_def = prog_def;
val _ = gen_prog_vars_birenvtyl_defthms progname bir_tutorial_prog_def;
val tutorial_birenvtyl_def = DB.fetch "scratch" (progname^"_birenvtyl_def");;

(* --------------------------- *)
(* prepare program lookups     *)
(* --------------------------- *)

val bir_lift_thm = lift_thm;
val _ = birs_auxLib.prepare_program_lookups bir_lift_thm;

(* ------------------ *)
(* Program boundaries *)
(* ------------------ *)

val tutorial_init_addr_def = Define `tutorial_init_addr : word64 = 0x0w`;

(* TODO: fix multiple endpoints here *)
val tutorial_end_addr_def = Define `tutorial_end_addr : word64 = ^endpoint`;

(* -------------- *)
(* BSPEC contract *)
(* -------------- *)

val bspec_tutorial_pre_def = Define `bspec_tutorial_pre : bir_exp_t = ^precond`;

(* --------------------------- *)
(* Symbolic analysis execution *)
(* --------------------------- *)

val (bsysprecond_thm, symb_analysis_thm) =
 bir_symb_analysis_thm
  bir_tutorial_prog_def
  tutorial_init_addr_def [tutorial_end_addr_def]
  bspec_tutorial_pre_def tutorial_birenvtyl_def;


(* ============================================================= *)

(* the result of running the symbolic execution *)
val _ = print "^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n"
val _ = print "^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n"
val _ = print_thm symb_analysis_thm;

(* ============================================================= *)

(* check leafs *)
val (sys_i, L_s, Pi_f) = (symb_sound_struct_get_sysLPi_fun o concl) symb_analysis_thm;
val leafs = (pred_setSyntax.strip_set o snd o dest_comb) Pi_f;
val _ = print "^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n"
val _ = print "^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n"
val _ = print ("number of leafs: " ^ (Int.toString (length leafs)) ^ "\n\n");


(* ============================================================= *)

(* TODO: move this away from here *)
fun model_t2s model =
  let
    fun pair_t2s (name,tm) = (name, term_to_string tm);
  in
    List.map pair_t2s model
  end;
fun get_init_vals wtm =
  let
    val model = ((Z3_SAT_modelLib.Z3_GET_SAT_MODEL wtm)
                       handle HOL_ERR e => []);
    val model_w_strs = model_t2s model
  in
    model_w_strs
  end;

(* compute concrete states from path conditions using SMT-solver *)
val wtms = List.map (bir_exp_to_wordsLib.bir2bool o (fn (_,_,_,pcond_tm) => pcond_tm) o dest_birs_state) leafs;
val states = List.map get_init_vals wtms;


(* print states *)
val _ = print "^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n"
val _ = print "^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n"
val _ = PolyML.print_depth 10;
val _ = List.foldl (fn (st,_) => (PolyML.print st; print "\n")) () states;

