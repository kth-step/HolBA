open HolKernel Parse boolLib bossLib;
open bslSyntax;

open bir_obs_modelLib;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = Globals.show_types := true;


val mem_bounds =
      let
        open wordsSyntax;
        val (mem_base, mem_len) = (Arbnum.fromHexString "0xFFCC0000",
                                   Arbnum.fromHexString  "0x10000");
        val mem_end = (Arbnum.- (Arbnum.+ (mem_base, mem_len), Arbnum.fromInt 128));
      in
        pairSyntax.mk_pair
            (mk_wordi (mem_base, 64),
             mk_wordi (mem_end, 64))
      end;


(*
(bir_prog_genLib.prog_gen_store_a_la_qc "spectre" 100) ()
(bir_prog_genLib.prog_gen_store_a_la_qc "spectre_v1" 100) ()
(bir_prog_genLib.prog_gen_store_a_la_qc "xld_br_yld" 2) ()
(bir_prog_genLib.prog_gen_store_a_la_qc "spectre_v1_mod1" 100) ()
(bir_prog_genLib.prog_gen_store_a_la_qc "xld_br_yld_mod1" 2) ()
*)

val _ = QUse.use "testcases/prog_1.sml";
val _ = QUse.use "testcases/prog_2.sml";
val _ = QUse.use "testcases/prog_3.sml";
val _ = QUse.use "testcases/prog_4.sml";
val _ = QUse.use "testcases/prog_5.sml";
val _ = QUse.use "testcases/prog_6.sml";
val _ = QUse.use "testcases/prog_7.sml";
val _ = QUse.use "testcases/prog_8.sml";
val _ = QUse.use "testcases/prog_9.sml";
val _ = QUse.use "testcases/prog_10.sml";
val _ = QUse.use "testcases/prog_11.sml";
val _ = QUse.use "testcases/prog_12.sml";
val _ = QUse.use "testcases/prog_13.sml";
val _ = QUse.use "testcases/prog_14.sml";


(* =========================== test case list to process ============================ *)

val test_cases =
  [prog_1_test,
   (* prog_2_test, *)
   prog_3_test,
   (* prog_4_test, *)
   (* prog_5_test, *)
   (* prog_6_test, *)
   (* prog_7_test, *)
   (* prog_8_test, *)
   (* prog_9_test, *)
   (* prog_10_test, *)
   (* prog_11_test, *)
   (* prog_12_test, *)
   (* prog_13_test, *)
   prog_14_test]

(* =========================== run and compare test cases ============================ *)

val _ = print "\n\n";

fun prog_obs_inst prog obs_type = proginst_fun_gen obs_type prog;

val entry = Arbnum.fromInt 0;
(*
val (name, prog, expected) = hd test_cases;

val (name, prog, expected) = prog_2_test;

val (name, prog, expected) = prog_5_test;

val m = "cache_speculation_first";
val m = "mem_address_pc_lspc";
(#add_obs (get_obs_model m)) mem_bounds (prog_obs_inst prog (#obs_hol_type (get_obs_model m))) entry
*)
fun run_test_case (name, prog, expected) =
  let
    val _ = print ("running test case '" ^ name ^ "' ...\n");

    fun fold_obs_add ((m, p), l) =
      if identical p ``F`` then (print ("!!! no expected output for '" ^ m ^ "' !!!\n"); l)
      else (((#add_obs (get_obs_model m)) mem_bounds (prog_obs_inst prog (#obs_hol_type (get_obs_model m))) entry, p)::l);

    val (expected_mem_address_pc,
         expected_mem_address_pc_lspc,
         expected_cache_tag_index,
         expected_cache_tag_only,
         expected_cache_index_only,
         expected_cache_tag_index_part,
         expected_cache_tag_index_part_page,
         expected_cache_speculation,
         expected_cache_speculation_first) = expected;

    val progs_list_raw =
      [("mem_address_pc",            expected_mem_address_pc),
       ("mem_address_pc_lspc",       expected_mem_address_pc_lspc),
       ("cache_tag_index",           expected_cache_tag_index),
       ("cache_tag_only",            expected_cache_tag_only),
       ("cache_index_only",          expected_cache_index_only),
       ("cache_tag_index_part",      expected_cache_tag_index_part),
       ("cache_tag_index_part_page", expected_cache_tag_index_part_page),
       ("cache_speculation",         expected_cache_speculation),
       ("cache_speculation_first",   expected_cache_speculation_first)];

    val progs_list = List.foldr fold_obs_add [] progs_list_raw;

    val _ = List.map (fn (t, t_) =>
            if identical t t_ then () else (
            print ("have: ");
            print_term t;
            print ("expecting: ");
            print_term t_;
            raise Fail ("unexpected obs added program: " ^ "\n" ^ (term_to_string prog)))
      ) progs_list;

    val _ = print "\n";

  in () end;

val _ = List.map run_test_case test_cases;
