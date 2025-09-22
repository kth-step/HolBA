structure birs_armcm0_concretizationLib =
struct

local

  open HolKernel Parse boolLib bossLib;

  open birsSyntax;

  open birs_utilsLib;
open birs_armcm0_constmemLib;

  (* error handling *)
  val libname = "birs_armcm0_concretizationLib"
  val ERR = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname

in (* local *)

(* from examples/binaries/binariesCfgLib.sml *)
  val bin_offset1 = 0x080055c8 (*new*) - 0x100013b4 (*old*); (* ..., __clzsi2 *)
  val hack_map_3
             = [(0x10000bb0+bin_offset1, "469F (mov pc, r3)",
                 0x10000da8+bin_offset1, (* first address of jump table *)
                 List.length [ (* mov pc, r3 <0x10000be2, 0x10000be6, 0x10000c3c, 0x10000d0a, 0x10000d14, 0x10000d18, 0x10000d20> *)
                         "10000c3c",
                         "10000be6",
                         "10000be6",
                         "10000d14",
                         "10000be2",
                         "10000be2",
                         "10000d0a",
                         "10000d14",
                         "10000be2",
                         "10000d0a",
                         "10000be2",
                         "10000d14",
                         "10000d18",
                         "10000d18",
                         "10000d18",
                         "10000d20"
                       ]),
                (0x1000060c+bin_offset1, "4697 (mov pc, r2)",
                 0x100007c8+bin_offset1, (* first address of jump table *)
                 List.length [ (* mov pc, r2 <0x10000620, 0x1000065e, 0x10000682, 0x100006fe, 0x1000070a, 0x10000722, 0x10000754> *)
                         "10000722",
                         "1000065e",
                         "10000682",
                         "10000620",
                         "10000682",
                         "100006fe",
                         "10000682",
                         "10000620",
                         "1000065e",
                         "1000065e",
                         "100006fe",
                         "10000620",
                         "10000754",
                         "10000754",
                         "10000754",
                         "1000070a"
                       ]),
                (0x100006b2+bin_offset1, "4697 (mov pc, r2)",
                 0x10000808+bin_offset1, (* first address of jump table *)
                 List.length [ (* mov pc, r2 <0x1000061e, 0x1000065e, 0x10000682, 0x100006fe, 0x10000708, 0x10000754> *)
                         "1000065e",
                         "1000065e",
                         "10000682",
                         "1000061e",
                         "10000682",
                         "100006fe",
                         "10000682",
                         "1000061e",
                         "1000065e",
                         "1000065e",
                         "100006fe",
                         "1000061e",
                         "10000754",
                         "10000754",
                         "10000754",
                         "10000708"
                       ])
                   ];

(* -------------------------------------------------------------------------- *)

local
  val indirjmp_mem_map_raw = (*[(0x100013b8, "", ["100013bc"])]@*)hack_map_3;
  (*
  fun fromString x =
    let
      val v = valOf (StringCvt.scanString (Int.scan StringCvt.HEX) x)
              handle _ => raise ERR "process_hack_map_targets" "cannot process target string";
    in
      v
    end;
  fun toMap (ad, pcl) = const_load_32_32_cheat_thms_fromprog progbin_tm (ad, pcl);
  *)
  fun indirjmp_mem_map progbin_tm = List.map (fn (_,_,ad,n) => (ad, List.map snd (const_load_32_32_fromprog progbin_tm (ad, n)))) indirjmp_mem_map_raw;
in
  fun get_all_targets progbin_tm addr =
    let
      val entries = List.filter ((fn x => x = addr) o fst) (indirjmp_mem_map progbin_tm);
      val _ = if length entries = 1 then () else raise ERR "get_single_target" "must find exactly one entry";
      val table = (snd o hd) entries;
    in
      table
    end;
  fun get_single_target progbin_tm addr idx =
    List.nth(get_all_targets progbin_tm addr, idx);
end

val pat_tm = ``
  birs_symbval_concretizations
    pcond
    (BExp_BinExp BIExp_And
      (BExp_Load (BExp_Den (BVar "sy_MEM" (BType_Mem Bit32 Bit8)))
        (BExp_BinExp BIExp_Plus
          (BExp_Const (Imm32 addr))
          (BExp_BinExp BIExp_LeftShift
            idx
            (BExp_Const (Imm32 2w))))
        BEnd_LittleEndian Bit32)
      (BExp_Const (Imm32 0xFFFFFFFEw)))``;
val pcond_pat_tm = ``pcond:bir_exp_t``;
val addr_pat_tm = ``addr:word32``;
val idx_pat_tm = ``idx:bir_exp_t``;
val idx_eval_tm = ``bir_eval_exp (idx:bir_exp_t) (BEnv (K NONE))``;
val empty_label_tm = ``EMPTY:bir_label_t->bool``;
fun concretization_resolver progbin_tm tm =
  let
    val _ = print "\n\nattempting to solve indirect jump through table in memory\n\n";
    val s = match_term pat_tm tm;
    (*val addr_tm = ((fn x => List.nth(x,1)) o fst) s;*)
    val addr_tm = subst (fst s) addr_pat_tm;
    (*val _ = print_term addr_tm;*)
    val addr = (Arbnum.toInt o wordsSyntax.dest_word_literal) addr_tm;
    val _ = print ("\nconcretizing @" ^ (Int.toString addr) ^ "\n");
  in
    let
      (*val idx_exp_tm = subst (fst s) idx_pat_tm;*)
      (* TODO: better take pathcondition into account here somehow, maybe with smt solver? to avoid unnecessary overapproximation *)
      val idx_val_thm = (EVAL o subst (fst s)) idx_eval_tm;
      (*val _ = print_thm idx_val_thm;*)
      val idx_tm = (snd o bir_valuesSyntax.gen_dest_BVal_Imm o optionSyntax.dest_some o rhs o concl) idx_val_thm;
      (*val _ = print_term idx_tm;*)
      val idx = (Arbnum.toInt o wordsSyntax.dest_word_literal) idx_tm;
      (*val _ = print (Int.toString idx);*)
      val v = get_single_target progbin_tm addr idx;
      (*val _ = print (Int.toString v);*)
      val v_tm = (bir_programSyntax.mk_BL_Address o bir_immSyntax.mk_Imm32) (wordsSyntax.mk_wordii (v, 32));
      (*val _ = print_term v_tm;*)
      val thm_tm = mk_eq (tm, pred_setSyntax.mk_insert(v_tm,empty_label_tm));
    in
      SOME (aux_moveawayLib.mk_oracle_preserve_tags [] "BIRS_INDIRJMP_MEM" (thm_tm))
      (*NONE : thm option*)
    end
    handle _ => (
      let
        fun int_to_Imm32 v = bir_immSyntax.mk_Imm32 (wordsSyntax.mk_wordii (v, 32));
        val vs_all = get_all_targets progbin_tm addr;
        val feasible_idxs =
          let
            (* first validate that idx cannot take other values, then repeatedly try to remove items from the list and see if it would still be including all items *)
            val idxs = List.tabulate(List.length vs_all, I);
            val pcond_exp_tm = subst (fst s) pcond_pat_tm;
            val idx_exp_tm = subst (fst s) idx_pat_tm;
            (*val _ = print_term pcond_exp_tm;
            val _ = print "\n";
            val _ = print_term idx_exp_tm;
            val _ = print "\n";*)
            fun is_an_index i =
                  bslSyntax.beq(idx_exp_tm, (bir_expSyntax.mk_BExp_Const o int_to_Imm32) i);
            fun includes_all_feasible check_idxs =
              let
                (*val _ = print "\nchecking: ";
                val _ = List.app (fn i => print ((Int.toString i) ^ ", ")) check_idxs;
                val _ = print "\n";*)
                val in_idxs_tm = bslSyntax.borl (List.map is_an_index check_idxs);
                val query_tm = bslSyntax.bor (bslSyntax.bnot pcond_exp_tm, in_idxs_tm);
                val res = bir_smtLib.bir_smt_check_taut false (query_tm);
                (*val _ = if res then print "done: includes\n" else print "done: something missing\n";*)
              in
                res
              end;
            fun reduce_list needs [] = needs
              | reduce_list needs (i::checks) =
                  let
                    val hyp_idxs = needs@checks;
                    val hyp_works = includes_all_feasible hyp_idxs;
                  in
                    if hyp_works then
                      reduce_list needs checks
                    else
                      reduce_list (i::needs) checks
                  end;
            (*val _ = print "trying first check\n";*)
            val _ = if includes_all_feasible idxs then () else
              raise ERR "concretization_resolver" "some feasible indexes are missing";
            (*val _ = print "trying to reduce indexes\n";*)
          in
            reduce_list [] idxs
          end;
        val _ = List.app (fn i => print ((Int.toString i) ^ ", ")) feasible_idxs;
        val _ = print "\n";
        val vs = list_mk_distinct gen_eq (List.map (fn i => List.nth(vs_all,i)) feasible_idxs);
        val v_tms = List.map (bir_programSyntax.mk_BL_Address o int_to_Imm32) vs;
        val vs_set_tm = List.foldl (pred_setSyntax.mk_insert) empty_label_tm v_tms;
        val thm_tm = mk_eq (tm, vs_set_tm);
        val _ = (print "possible overapproximation in concretization: "; print_term thm_tm);
      in
        SOME (aux_moveawayLib.mk_oracle_preserve_tags [] "BIRS_INDIRJMP_MEM" (thm_tm))
      end
    )
  end
  handle _ => (print "\nconcretization_resolver failed\n"; print_term tm; print "\n\n"; raise ERR "concretization_resolver" "concretization_resolver failed");

(*
(**)
val tm = ``
birs_symbval_concretizations
     (BExp_UnaryExp BIExp_Not
        (BExp_BinExp BIExp_And
           (BExp_BinPred BIExp_LessOrEqual (BExp_Const (Imm32 4w))
              (BExp_Den (BVar "syr_9" (BType_Imm Bit32))))
           (BExp_UnaryExp BIExp_Not
              (BExp_BinPred BIExp_Equal
                 (BExp_Den (BVar "syr_9" (BType_Imm Bit32)))
                 (BExp_Const (Imm32 15w))))))
  (BExp_BinExp BIExp_And
     (BExp_Load (BExp_Den (BVar "sy_MEM" (BType_Mem Bit32 Bit8)))
        (BExp_BinExp BIExp_Plus (BExp_Const (Imm32 0x10000DA8w))
           (BExp_BinExp BIExp_LeftShift
              (BExp_Den (BVar "syr_9" (BType_Imm Bit32)))
              (BExp_Const (Imm32 2w)))) BEnd_LittleEndian Bit32)
     (BExp_Const (Imm32 0xFFFFFFFEw)))
``;
val _ = print_thm (valOf (concretization_resolver tm));
val _ = raise Fail "";
(**)
*)

end (* local *)

end (* struct *)
