open HolKernel Parse boolLib bossLib;
open bslSyntax;
open pretty_exnLib;

(* Load the dependencies in interactive sessions *)
val _ = if !Globals.interactive then (
  load "easy_noproof_wpLib"; (* ../lib *)
  load "HolSmtLib"; (* HOL/src/HolSmt *)
  ()) else ();

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = Globals.show_tags := true;

val _ = if !Globals.interactive then () else (
  Feedback.set_trace "HolSmtLib" 0;
  Feedback.set_trace "bir_wpLib.DEBUG_LEVEL" 0;
  Feedback.set_trace "easy_noproof_wpLib" 1;
  Feedback.set_trace "Define.storage_message" 0;
  Feedback.emit_WARNING := false;
  ());

(*
val _ = Globals.linewidth := 100;
val _ = Globals.show_types := true;
val _ = Globals.show_assums := true;
val _ = wordsLib.add_word_cast_printer ();
val _ = Feedback.set_trace "HolSmtLib" 0;
val _ = Feedback.set_trace "HolSmtLib" 4;
val _ = Feedback.set_trace "bir_wpLib.DEBUG_LEVEL" 2;
val _ = Feedback.set_trace "easy_noproof_wpLib" 2;
val _ = Feedback.set_trace "Define.storage_message" 1;
*)

fun timer_start () = Time.now();
fun timer_stop tm = let
     val d_time = Time.- (Time.now(), tm);
     in (Time.toString d_time) end;

(* C code:
 *
 * int16_t gauss(int16_t x) {
 *   int16_t ret = 0;
 *   while (x > 0) {
 *     ret += x;
 *     x--;
 *   }
 *   return ret;
 * }
 *
 * C code with invariants, pre- and post-conditions:
 *
 * int gauss(int x) {
 *   {P3: X=X0}
 *   {WP3: (X0*(X0+1)) = (X*(X+1)) + 0}
 *   int ret = 0;
 *   {Q3: (X0*(X0+1)) = (X*(X+1)) + ret*2}
 *   while (x > 0) {
 *     {P2:  (X0*(X0+1)) = (X*(X+1)) + ret*2 /\ x>0}
 *     {WP2: (X0*(X0+1)) = ((X-1)*X) + ret*2 + x}
 *     ret += x;
 *     {(X0*(X0+1)) = ((X-1)*X) + ret*2}
 *     x--;
 *     {Q2: (X0*(X0+1)) = (X*(X+1)) + ret*2}
 *   }
 *   {P1: (X0*(X0+1)) = (X*(X+1)) + ret*2 /\ x=0}
 *   {WP1: Q1}
 *   {Q1: ret*2 = (X0*(X0+1))}
 *   return ret;
 * }
 *
 * Programs:
 * - S3:
 *   1. ret := 0;
 * - S2:
 *   1. ret := ret + x;
 *   2. x := x - 1;
 * - S1: empty
*)

(* Generates the term (var*(var+1)) *)
fun gen_frac var_name =
  bmult ((bden o bvarimm16) var_name, bplus ((bden o bvarimm16) var_name, bconst16 1))

(* P3, S3, Q3 *)
val s3_thm =
  let
    (* S3 *)
    val s3_prog_def = bdefprog_list alpha "s3_prog" [
      (blabel_str "entry", [], (bjmp o belabel_str) "ret_eq_0"),
      (blabel_str "ret_eq_0", [
        bassign (bvarimm16 "ret", bconst16 0)
      ], (bjmp o belabel_str) "end"),
      (blabel_str "end", [], bhalt (bconst32 0))
    ];

    (* prog + P + Q => ``P ==> WP`` *)
    val p_imp_wp_bir_tm = easy_noproof_wpLib.compute_p_imp_wp_tm "S3"
      (* prog_def *) s3_prog_def
      (* P3 *) (
        blabel_str "entry",
        beq ((bden o bvarimm16) "x", (bden o bvarimm16) "x0")
      )
      (* Q3 *) (
        [blabel_str "end"],
        beq (gen_frac "x0", bplus (gen_frac "x", bmult ((bden o bvarimm16) "ret", bconst16 2)))
      )
      handle e => raise pp_exn_s "compute_p_imp_wp_tm failed" e

    (* BIR expr => SMT-ready expr*)
    val smt_ready_tm = bir_exp_to_wordsLib.bir2bool p_imp_wp_bir_tm
      handle e => raise pp_exn_s "bir2bool failed" e

    (* Prove it using an SMT solver *)
    val start_time = timer_start ();
    val smt_thm = HolSmtLib.Z3_ORACLE_PROVE smt_ready_tm
      handle e => raise pp_exn_s "Z3_ORACLE_PROVE failed" e
    val _ = print ("SMT solver took: " ^ (timer_stop start_time) ^ " sec\n");
  in
    smt_thm
  end;
val _ = (Hol_pp.print_thm s3_thm; print "\n");

(* P2, S2, Q2 *)
val s2_thm =
  let
    (* S2 *)
    val s2_prog_def = bdefprog_list alpha "s2_prog" [
      (blabel_str "entry", [], (bjmp o belabel_str) "ret_add_x"),
      (blabel_str "ret_add_x", [
        bassign (bvarimm16 "ret", bplus ((bden o bvarimm16) "ret", (bden o bvarimm16) "x"))
      ], (bjmp o belabel_str) "x_dec"),
      (blabel_str "x_dec", [
        bassign (bvarimm16 "x", bminus ((bden o bvarimm16) "x", bconst16 1))
      ], (bjmp o belabel_str) "end"),
      (blabel_str "end", [], bhalt (bconst32 0))
    ];
    (* prog + P + Q => ``P ==> WP`` *)
    val p_imp_wp_bir_tm = easy_noproof_wpLib.compute_p_imp_wp_tm "S2"
      (* prog_def *) s2_prog_def
      (* P2 *) (
        blabel_str "entry",
        bandl [
          beq (gen_frac "x0", bplus (gen_frac "x", bmult ((bden o bvarimm16) "ret", bconst16 2))),
          blt (bconst16 0, (bden o bvarimm16) "x")
        ]
      )
      (* Q2 *) (
        [blabel_str "end"],
        beq (gen_frac "x0", bplus (gen_frac "x", bmult ((bden o bvarimm16) "ret", bconst16 2)))
      )
      handle e => raise pp_exn_s "compute_p_imp_wp_tm failed" e

    (* BIR expr => SMT-ready expr*)
    val smt_ready_tm = bir_exp_to_wordsLib.bir2bool p_imp_wp_bir_tm
      handle e => raise pp_exn_s "bir2bool failed" e

    (* Prove it using an SMT solver *)
    val start_time = timer_start ();
    val smt_thm = HolSmtLib.Z3_ORACLE_PROVE smt_ready_tm
      handle e => raise pp_exn_s "Z3_ORACLE_PROVE failed" e
    val _ = print ("SMT solver took: " ^ (timer_stop start_time) ^ " sec\n");
  in
    smt_thm
  end;
val _ = (Hol_pp.print_thm s2_thm; print "\n");

