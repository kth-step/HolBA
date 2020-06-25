open HolKernel Parse boolLib bossLib;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = wordsLib.add_word_cast_printer ();
val _ = Globals.show_types := true;

(* prepare test program terms and theorems *)
open toyBinaryTheory;
val lift_thm = toy_m0_program_THM;
val prog_tm = ((snd o dest_comb o concl) lift_thm);
val prog_l_tm = dest_BirProgram prog_tm;
val prog_l_def = Define `toy_m0_program_l = ^prog_l_tm`;
val prog_l_const = (fst o dest_eq o concl) prog_l_def;
val lift_thm_abbr = REWRITE_RULE [GSYM prog_l_def] lift_thm;
val prog_tm_abbr = ((snd o dest_comb o concl) lift_thm_abbr);

val valid_labels_thm = prove(``
  bir_is_lifted_prog r mu mms p ==> bir_is_valid_labels p
``,
  METIS_TAC [bir_inst_liftingTheory.bir_is_lifted_prog_def]
);

val valid_prog_thm = prove(``bir_is_valid_program (^prog_tm_abbr)``,
  REWRITE_TAC [bir_program_valid_stateTheory.bir_is_valid_program_def] >>
  STRIP_TAC >- (
    METIS_TAC [valid_labels_thm, lift_thm_abbr]
  ) >>
  SIMP_TAC list_ss [bir_program_valid_stateTheory.bir_program_is_empty_def, prog_l_def]
);

(* build the dictionaries using the library under test *)
val _ = print "Building dictionaries.\n";
open bir_blockCollectionLib;
val block_dict = gen_block_dict prog_tm;
val MEM_block_dict = gen_MEM_thm_block_dict prog_l_def valid_prog_thm;
val _ = print "\n";
val _ = print "\n";

(* test cases *)
val bir_blocks = [
  (Arbnum.fromHexString "8166",
    ``<|bb_label :=
         BL_Address_HC (Imm32 (33126w :word32)) "E004 (b.n 8172 <main+0x6e>)";
       bb_statements := ([] :'observation_type bir_stmt_basic_t list);
       bb_last_statement :=
         BStmt_Jmp (BLE_Label (BL_Address (Imm32 (33138w :word32))))|>``)
];

(* test that the domains match, and the test case addresses are available when used as normalized keys *)
val _ = print "Running tests.\n";
val _ = if get_block_dict_keys block_dict = get_block_dict_keys MEM_block_dict then () else
        raise Fail ("Domains of the two dictionaries don't match.");

val dict_keys = get_block_dict_keys block_dict;
val bir_block_keys = List.map ((mk_key_from_address 32) o fst) bir_blocks;
val _ = if List.all (fn x => List.exists (fn y => x = y) dict_keys) bir_block_keys then () else
        raise Fail ("Cannot find a label.");

(*
val (addr, block) = hd bir_blocks;
*)

fun assert_this success =
  if success then () else
  raise Fail ("Something is wrong.");

(* use the library functions for accessing the dictionaries *)
val _ = List.foldl
  (fn ((addr, block), _) =>
    let
      val lbl_tm = mk_key_from_address 32 addr;
      val _ = print ((term_to_string lbl_tm) ^ "\n");

      val _ = assert_this (lookup_block_dict_byAddr32 block_dict addr = SOME block);
      val _ = assert_this (lookup_block_dict block_dict lbl_tm = SOME block);

      val MEM_tm = (concl o valOf) (lookup_block_dict MEM_block_dict lbl_tm);
      val (conjl, conjr) = (dest_conj) MEM_tm;
      val _ = assert_this (conjr = ``
          (MEM (^lbl_tm)
               (bir_labels_of_program (^prog_tm_abbr))
	  )<=> T
        ``);

      val (eql, eqr) = dest_eq conjl;
      val _ = assert_this (eql = ``
          bir_get_program_block_info_by_label
            (^prog_tm_abbr)
            (^lbl_tm)
        ``);
      val (_, lookedup_block_tm) = (pairSyntax.dest_pair o optionSyntax.dest_some) eqr;
      val _ = assert_this (lookedup_block_tm = block);

      val _ = print "\n";
    in () end) () bir_blocks;
