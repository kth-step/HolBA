open HolKernel Parse boolLib bossLib;

open resolveFullyLib;
open generationLib;

fun timer_start () = Time.now();
fun timer_stop tm = (Time.- (Time.now(), tm));
fun timer_stop_str tm = Time.toString (Time.- (Time.now(), tm));

fun test_resolve_indirect_jumps(middle_blocks_n) =
    let
      val exit_addr = 10 * middle_blocks_n
      val prog_def = gen_program("prog", middle_blocks_n)
      val prog_tm = (lhs o concl) prog_def
      val args = gen_args_program(middle_blocks_n, 1)
      val start = timer_start()
      val (prog'_tm, prog'_def, prog'_thm) = resolve_indirect_jumps("resolved_gen_prog", prog_tm, args)
      val stop = timer_stop start
    in
      (middle_blocks_n, stop)
    end

fun test_partial_resolve_indirect_jumps(middle_blocks_n) =
    let
      val exit_addr = 10 * middle_blocks_n
      val prog_def = gen_program("prog", middle_blocks_n)
      val prog_tm = (lhs o concl) prog_def
      val args = gen_partial_args_program(middle_blocks_n, 100)
      val start = timer_start()
      val (prog'_tm, prog'_def, prog'_thm) = resolve_indirect_jumps("resolved_gen_prog", prog_tm, args)
      val stop = timer_stop start
    in
      (middle_blocks_n, stop)
    end

fun test_transfer_contract (middle_blocks_n) =
    let
      val exit_addr = 10 * middle_blocks_n
      val prog_def = gen_program("prog", middle_blocks_n)
      val prog_tm = (lhs o concl) prog_def

      val prog'_thm = prove(“resolve_fully_n prog args = SOME prog'”, cheat)

      val entry_label_tm = “BL_Label "entry1"”
      val ending_labels_tm = “{^(blabel_addr64 exit_addr)}”
      val post_tm = “\l. if (l = ^(blabel_addr64 exit_addr))
                   then bir_exp_true
                   else bir_exp_false”
      val ht_thm' = prove(
        “bir_exec_to_labels_triple prog' ^entry_label_tm ^ending_labels_tm bir_exp_true ^post_tm”, 
        cheat)

      val start = timer_start()
      val ht'_thm = transfer_contract(prog_tm, prog'_thm, ht_thm')
      val stop = timer_stop start
    in
      (middle_blocks_n, stop)
    end

fun print_test_result(middle_blocks_n, time) = 
    let 
      val res = "size: " ^ Int.toString middle_blocks_n ^
                ", time: " ^ Time.toString(time) ^ "s\n"
    in
      print(res)
    end

fun write_test_result file (n, time) =
     TextIO.output (file, Int.toString n ^ ", " ^ Time.toString(time) ^ "\n")

fun write_test_results(filename, results) =
    let
      val file = TextIO.openOut (filename)
      val _ = List.map (write_test_result file) results
    in
      TextIO.closeOut file
    end;

fun range(start, step, stop) = 
    List.tabulate(((stop-start) div step) + 1, fn i => start + step * i)

fun linspace(start, n, stop) = range(start, (stop - start) div n, stop)


(*200 64s*)
val resolve_middle_blocks_ns = range(10, 10, 200)
val resolve_results = List.map (test_resolve_indirect_jumps) resolve_middle_blocks_ns
val _ = List.map print_test_result resolve_results
val _ = write_test_results("resolve", resolve_results)

(*val _ = Posix.Process.sleep (Time.fromSeconds (Int.toLarge 60))*)

val partial_resolve_middle_blocks_ns = range(100, 100, 2000)
val partial_resolve_results = List.map (test_partial_resolve_indirect_jumps) partial_resolve_middle_blocks_ns
val _ = List.map print_test_result partial_resolve_results
val _ = write_test_results("partial_resolve", partial_resolve_results)

(*val _ = Posix.Process.sleep (Time.fromSeconds (Int.toLarge 60))*)

(*80000 53s*)
val transfer_middle_blocks_ns = range(1000, 2000, 38000)
val transfer_results = List.map test_transfer_contract transfer_middle_blocks_ns
val _ = List.map print_test_result transfer_results
val _ = write_test_results("transfer", transfer_results)
