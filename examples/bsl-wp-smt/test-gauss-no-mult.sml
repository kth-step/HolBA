open HolKernel Parse boolLib bossLib;
open bslSyntax;
open pretty_exnLib;

(* Load dependencies in interactive sessions *)
val _ = if !Globals.interactive then (
  load "easy_noproof_wpLib"; (* ../lib *)
  load "HolSmtLib"; (* HOL/src/HolSmt *)
  ()) else ();

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = Globals.show_tags := true;

val _ = if !Globals.interactive then () else (
  Feedback.set_trace "HolSmtLib" 0;
  Feedback.set_trace "bir_wpLib.DEBUG_LEVEL" 0;
  Feedback.set_trace "easy_noproof_wpLib" logLib.INFO;
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
val _ = Feedback.set_trace "easy_noproof_wpLib" logLib.TRACE;
val _ = Feedback.set_trace "Define.storage_message" 1;
*)

fun timer_start () = Time.now();
fun timer_stop tm = let
     val d_time = Time.- (Time.now(), tm);
     in (Time.toString d_time) end;

(* Refer to no_mem_gauss_example.sml and substitute like this:
 *  - X0=X0
 *  - X=mem[0]
 *  - ret=mem[48]
*)

fun prove_mem_gauss addr_len val_len =
  let
    val len_name = "addr" ^ (Int.toString addr_len) ^ "_"
      ^ "val" ^ (Int.toString val_len);

    (* BIR helpers *)
    val bvarmem = bvarmem (addr_len, 8)
    val bdenmem = (bden o bvarmem)
    val bconsti = bconstii val_len
    val bvar = bvarimm val_len
    fun bload_be mem addr = bloadi_be mem addr val_len

    fun gen_load addr = bload_be (bdenmem "memory") (bconstii addr_len addr)
    fun gen_store addr val_tm = bstore_be (bdenmem "memory") (bconstii addr_len addr) val_tm

    fun gen_1 bir_tm = bmult (bir_tm, bplus (bir_tm, bconsti 1))
    fun gen_1_mem addr = gen_1 (gen_load addr)
    fun gen_1_var var_name = gen_1 ((bden o bvar) var_name)

    (* P3, S3, Q3 *)
    val s3_thm =
      let
        (* S3 *)
        val s3_prog_def = bdefprog_list alpha "s3_prog" [
          (blabel_str "entry", [], (bjmp o belabel_str) "ret_eq_0"),
          (blabel_str "ret_eq_0", [
            bassign (bvarmem "memory", gen_store 48 (bconsti 0))
          ], (bjmp o belabel_str) "workaround"),
          (blabel_str "workaround", [], (bjmp o belabel_str) "end"),
          (blabel_str "end", [], bhalt (bconst32 0))
        ];
        (* prog + P + Q => ``P ==> WP`` *)
        val p_imp_wp_bir_tm = easy_noproof_wpLib.compute_p_imp_wp_tm ("S3_" ^ len_name)
          (* prog_def *) s3_prog_def
          (* P3 *) (
            blabel_str "entry",
            beq (gen_load 0, (bden o bvarimm val_len) "x0")
          )
          (* Q3 *) (
            [blabel_str "end"],
            beq (gen_1_var "x0", bplus (gen_1_mem 0, bmult (gen_load 48, bconsti 2)))
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
    (* P2, S2, Q2 *)
    val s2_thm =
      let
        (* S2 *)
        val s2_prog_def = bdefprog_list alpha "s2_prog" [
          (blabel_str "entry", [], (bjmp o belabel_str) "ret_add_x"),
          (blabel_str "ret_add_x", [
            bassign (bvarmem "memory", gen_store 48 (bplus (gen_load 48, gen_load 0)))
          ], (bjmp o belabel_str) "x_dec"),
          (blabel_str "x_dec", [
            bassign (bvarmem "memory", gen_store 0 (bminus (gen_load 0, (bconsti 1))))
          ], (bjmp o belabel_str) "workaround"),
          (blabel_str "workaround", [], (bjmp o belabel_str) "end"),
          (blabel_str "end", [], bhalt (bconst32 0))
        ];
        (* prog + P + Q => ``P ==> WP`` *)
        val p_imp_wp_bir_tm = easy_noproof_wpLib.compute_p_imp_wp_tm ("S2_" ^ len_name)
          (* prog_def *) s2_prog_def
          (* P2 *) (
            blabel_str "entry",
            (* 0<x && x<2^16 && ret<2^16 && x=x0 && ret=ret0 *)
            bandl [
              beq (gen_load 0, (bden o bvar) "x0"),
              beq (gen_load 48, (bden o bvar) "ret0"),
              blt (bconsti 0, gen_load 0), blt (gen_load 0, bconsti 0xF),
              blt (gen_load 48, bconsti 0xF)
            ]
          )
          (* Q2 *) (
            [blabel_str "end"],
            (* ret0 + x0 <= ret + x *)
            ble (bplus ((bden o bvar) "ret0", (bden o bvar) "x0"), bplus (gen_load 0, gen_load 48))
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
  in
    (s3_thm, s2_thm)
  end;

val times = List.map
  (fn (addr_len, val_len) =>
    let
      val start_time = timer_start ();
      val _ = prove_mem_gauss addr_len val_len;
      val params = "("
        ^ "addr: " ^ (Int.toString addr_len) ^ ", "
        ^ "val: " ^ (Int.toString val_len) ^ ")";
      val time = (timer_stop start_time) ^ " sec";
      val msg = "prove_mem_no-mult_gauss " ^ params ^ " took: " ^ time;
      val _ = print (msg ^ "\n");
    in
      msg
    end)
  (if !Globals.interactive then
    [(  8, 8), (  8, 16), (  8, 32), (  8, 64), (  8, 128),
     ( 16, 8), ( 16, 16), ( 16, 32), ( 16, 64), ( 16, 128),
     ( 32, 8), ( 32, 16), ( 32, 32), ( 32, 64), ( 32, 128),
     ( 64, 8), ( 64, 16), ( 64, 32), ( 64, 64), ( 64, 128),
     (128, 8), (128, 16), (128, 32), (128, 64), (128, 128)]
  else (* Only run some of them in CI tests *)
    [(8, 8), (8, 128), (16, 32), (128, 64)])

val _ = print "Times:\n";
val _ = List.map (fn t => (print " - "; print t; print "\n")) times;

(* Times:
 *  - prove_mem_no-mult_gauss (addr:   8, val:   8) took: 7.946 sec
 *  - prove_mem_no-mult_gauss (addr:   8, val:  16) took: 7.264 sec
 *  - prove_mem_no-mult_gauss (addr:   8, val:  32) took: 7.558 sec
 *  - prove_mem_no-mult_gauss (addr:   8, val:  64) took: 7.844 sec
 *  - prove_mem_no-mult_gauss (addr:   8, val: 128) took: 8.444 sec
 *  - prove_mem_no-mult_gauss (addr:  16, val:   8) took: 8.208 sec
 *  - prove_mem_no-mult_gauss (addr:  16, val:  16) took: 7.526 sec
 *  - prove_mem_no-mult_gauss (addr:  16, val:  32) took: 8.102 sec
 *  - prove_mem_no-mult_gauss (addr:  16, val:  64) took: 8.058 sec
 *  - prove_mem_no-mult_gauss (addr:  16, val: 128) took: 8.599 sec
 *  - prove_mem_no-mult_gauss (addr:  32, val:   8) took: 7.835 sec
 *  - prove_mem_no-mult_gauss (addr:  32, val:  16) took: 7.879 sec
 *  - prove_mem_no-mult_gauss (addr:  32, val:  32) took: 7.639 sec
 *  - prove_mem_no-mult_gauss (addr:  32, val:  64) took: 7.650 sec
 *  - prove_mem_no-mult_gauss (addr:  32, val: 128) took: 8.081 sec
 *  - prove_mem_no-mult_gauss (addr:  64, val:   8) took: 7.585 sec
 *  - prove_mem_no-mult_gauss (addr:  64, val:  16) took: 7.948 sec
 *  - prove_mem_no-mult_gauss (addr:  64, val:  32) took: 7.857 sec
 *  - prove_mem_no-mult_gauss (addr:  64, val:  64) took: 7.532 sec
 *  - prove_mem_no-mult_gauss (addr:  64, val: 128) took: 7.759 sec
 *  - prove_mem_no-mult_gauss (addr: 128, val:   8) took: 8.081 sec
 *  - prove_mem_no-mult_gauss (addr: 128, val:  16) took: 7.561 sec
 *  - prove_mem_no-mult_gauss (addr: 128, val:  32) took: 7.755 sec
 *  - prove_mem_no-mult_gauss (addr: 128, val:  64) took: 8.121 sec
 *  - prove_mem_no-mult_gauss (addr: 128, val: 128) took: 7.903 sec
 *)
