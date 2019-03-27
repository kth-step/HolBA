structure bir_exp_to_wordsLib :> bir_exp_to_wordsLib =
struct

  open Abbrev

  local

  open HolKernel Parse boolLib bossLib;
  open optionSyntax numSyntax;
  open wordsSyntax fcpSyntax;

  open bir_exp_memTheory bir_exp_memSyntax;
  open bir_valuesTheory bir_valuesSyntax;
  open bir_expTheory bir_expSyntax;
  open bir_immTheory bir_immSyntax;
  open bir_interval_expTheory;
  open bir_typing_expTheory;
  open bir_bool_expSyntax;
  open bir_envSyntax;

  open bir_exp_immTheory;
  open bir_exp_memTheory;

  (*open bir_wp_simpLib;*)

  val ERR = mk_HOL_ERR "bir_exp_to_wordsLib";
  val wrap_exn = Feedback.wrap_exn "bir_exp_to_wordsLib";

  fun simp_if_conv tm =
    let
      val thms = [
        prove (
          ``!A. ((if A then 1w else 0w) = (1w:word1)) = A``,
          Cases_on `A` >>
          SIMP_TAC (srw_ss()) []
        ),
        prove (
          ``!A. (~(if A then 1w else 0w) = (1w:word1)) = ~A``,
          Cases_on `A` >>
          SIMP_TAC (srw_ss()) []
        ),
        prove (
          ``!A. ((if ~A then 1w else 0w) = (1w:word1)) = ~A``,
          Cases_on `A` >>
          SIMP_TAC (srw_ss()) []
        ),
        prove (
          ``!A B. ((if A then (1w:word1) else 0w) && (if B then (1w:word1) else 0w))
                  = (if (A /\ B) then (1w:word1) else 0w)``,
          Cases_on `A` >>
          Cases_on `B` >>
          SIMP_TAC (srw_ss()) []
        ),
        prove (
          ``!A B. ((if A then (1w:word1) else 0w) || (if B then (1w:word1) else 0w))
                  = (if (A \/ B) then (1w:word1) else 0w)``,
          Cases_on `A` >>
          Cases_on `B` >>
          SIMP_TAC (srw_ss()) []
        )
      ]
    in
      REWRITE_CONV thms tm
        handle _ => REFL tm
    end;

  fun type_of_bir_exp_CONV term =
    (* Manual test
    val term = ``
      BExp_BinExp BIExp_Plus
        (BExp_Const (Imm32 20w))
        (BExp_Const (Imm32 22w))
    ``;
    val thm = type_of_bir_exp_CONV ``type_of_bir_exp ^term``;
    *)
    let
      open bir_immTheory
      open bir_valuesTheory
      open bir_envTheory
      open bir_exp_memTheory
      open bir_bool_expTheory
      open bir_extra_expsTheory
      open bir_nzcv_expTheory
      val type_of_bir_exp_thms = [
        type_of_bir_exp_def,
        bir_var_type_def,
        bir_type_is_Imm_def,
        type_of_bir_imm_def,
        BExp_Aligned_type_of,
        BExp_unchanged_mem_interval_distinct_type_of,
        bir_number_of_mem_splits_REWRS,
        BType_Bool_def,
        bir_exp_true_def,
        bir_exp_false_def,
        BExp_MSB_type_of,
        BExp_nzcv_ADD_DEFS,
        BExp_nzcv_SUB_DEFS,
        n2bs_def,
        BExp_word_bit_def,
        BExp_Align_type_of,
        BExp_ror_type_of,
        BExp_LSB_type_of,
        BExp_word_bit_exp_type_of,
        BExp_ADD_WITH_CARRY_type_of,
        BExp_word_reverse_type_of,
        BExp_ror_exp_type_of
      ]
      val conv = SIMP_CONV (srw_ss()) type_of_bir_exp_thms
    in
      conv term
    end
      handle e => raise wrap_exn "type_of_bir_exp_CONV" e;

  fun bir_type_of term =
    let
      val type_o_thm = type_of_bir_exp_CONV ``type_of_bir_exp ^term``
      val type_o_tm = (snd o dest_eq o concl) type_o_thm
    in
      dest_some type_o_tm
    end
      handle e => raise wrap_exn "bir_type_of" e;

  fun w2bool (w1_exp: term) =
    let
      val bool_tm = mk_eq (w1_exp, mk_wordii (1, 1))
      val simped_thm = simp_if_conv bool_tm
    in
      (snd o dest_eq o concl) simped_thm
    end
      handle e => raise wrap_exn "w2bool" e;

  fun bool2w exp_tm =
    let
      val to_rewrite = ``bool2w ^exp_tm``
      val rewritten = REWRITE_CONV [bool2w_def] to_rewrite
    in
      (snd o dest_comb o concl) rewritten
    end
      handle e => raise wrap_exn "bool2w" e;

  fun bir_exp_to_words exp =
    let
      val _ = ()
    in
      (* Constants *)
      if is_BExp_Const exp then
        (snd o gen_dest_Imm o dest_BExp_Const) exp
          handle e => raise wrap_exn "bir_exp_to_words::const" e
      (* Den *)
      else if is_BExp_Den exp then
        (* Manual tests
        val exp = ``(BExp_Den (BVar "ADDR" (BType_Imm Bit32)))``;
        val exp = ``(BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))``;
        val w = bir_exp_to_words exp;
        *)
        let
          val name = (fst o dest_BVar_string o dest_BExp_Den) exp
          val bir_type = (snd o dest_BVar_string o dest_BExp_Den) exp
          val hol_type =
            if is_BType_Imm bir_type then
              (word_ty_of_bir_immtype_t o dest_BType_Imm) bir_type
                handle e => raise wrap_exn "bir_exp_to_words::den::imm" e
            else if is_BType_Mem bir_type then
              let
                val (addr_bir_ty, val_bir_ty) = dest_BType_Mem bir_type
                val addr_ty = word_ty_of_bir_immtype_t addr_bir_ty
                val val_ty = word_ty_of_bir_immtype_t val_bir_ty
                  handle e => raise wrap_exn "bir_exp_to_words::den::mem" e
              in
                Type `: ^addr_ty -> ^val_ty`
              end
            else
              raise Fail ("unhandled type: " ^ (term_to_string bir_type))
        in
          mk_var (name, hol_type)
        end
          handle e => raise wrap_exn "bir_exp_to_words::den" e
      (* Casts are not handled yet. *)
      else if is_BExp_Cast exp then
        raise ERR "bir_exp_to_words" "Cast expressions aren't handled yet."
      (* Unary expressions *)
      else if is_BExp_UnaryExp exp then
        (* Manual tests
        val exp = ``BExp_UnaryExp BIExp_ChangeSign (BExp_Const (Imm64 112w))``;
        val exp = ``BExp_UnaryExp BIExp_Not (BExp_Const (Imm1 1w))``;
        val exp = ``BExp_UnaryExp BIExp_Not
          (BExp_BinPred BIExp_Equal
            (BExp_Den (BVar "oracle" (BType_Imm Bit32)))
            (BExp_Const (Imm32 0w)))``;
        *)
        let
          val (uop, bir_exp) = (dest_BExp_UnaryExp) exp
          val w_exp = bir_exp_to_words bir_exp
          val to_rw = ``(bir_unary_exp_GET_OPER ^uop) ^w_exp``
          val rewritten = REWRITE_CONV [bir_unary_exp_GET_OPER_def] to_rw
        in
          (snd o dest_comb o concl) rewritten
        end
          handle e => raise wrap_exn "bir_exp_to_words::unary_exp" e
      (* Binary expressions *)
      else if is_BExp_BinExp exp then
        (* Manual tests
        val exp = ``(BExp_BinExp BIExp_Plus (BExp_Const (Imm64 112w)) (BExp_Const (Imm64 11w)))``;
        *)
        let
          val (bop, bir_exp1, bir_exp2) = (dest_BExp_BinExp) exp
          val w_exp1 = bir_exp_to_words bir_exp1
          val w_exp2 = bir_exp_to_words bir_exp2
          val to_rw = ``(bir_bin_exp_GET_OPER ^bop) ^w_exp1 ^w_exp2``
          val rewritten = REWRITE_CONV [bir_bin_exp_GET_OPER_def] to_rw
        in
          (snd o dest_comb o concl) rewritten
        end
          handle e => raise wrap_exn "bir_exp_to_words::binary_exp" e
      (* Binary predicates *)
      else if is_BExp_BinPred exp then
        (* Manual tests
        val exp = ``BExp_BinPred BIExp_LessThan (BExp_Const (Imm64 112w)) (BExp_Const (Imm64 11w))``;
        val exp = ``BExp_BinPred BIExp_Equal
          (BExp_Den (BVar "oracle" (BType_Imm Bit32)))
          (BExp_Const (Imm32 0w))``;
        val w = bir_exp_to_words exp;
        *)
        let
          val (bpred, bir_exp1, bir_exp2) = (dest_BExp_BinPred) exp
          val w_exp1 = bir_exp_to_words bir_exp1
          val w_exp2 = bir_exp_to_words bir_exp2
          val to_rw = ``(bir_bin_pred_GET_OPER ^bpred) ^w_exp1 ^w_exp2``
          val rewritten = REWRITE_CONV [bir_bin_pred_GET_OPER_def] to_rw
          val w_bool_bin_pred = (snd o dest_comb o concl) rewritten
        in
          bool2w w_bool_bin_pred
        end
          handle e => raise wrap_exn "bir_exp_to_words::binary_pred" e
      (* MemEq expressions *)
      else if is_BExp_MemEq exp then
        (* Manual tests
        val exp = ``
          BExp_MemEq
            (BExp_Den (BVar "MEM_dest" (BType_Mem Bit32 Bit8)))
            (BExp_Store
              (BExp_Den (BVar "MEM_src" (BType_Mem Bit32 Bit8)))
              (BExp_Den (BVar "ADDR" (BType_Imm Bit32)))
              BEnd_BigEndian
              (BExp_Const (Imm16 (42w :word16))))
        ``;
        val w = bir_exp_to_words exp;
        *)
        let
          val (bir_lhs, bir_rhs) = dest_BExp_MemEq exp
          val lhs = bir_exp_to_words bir_lhs
          val rhs = bir_exp_to_words bir_rhs
          val eq = mk_eq (lhs, rhs)
            handle e => raise wrap_exn "bir_exp_to_words::mem_eq" e;
        in
          bool2w eq
            handle e => raise wrap_exn "bir_exp_to_words::mem_eq" e
        end
      (* If-then-else *)
      else if is_BExp_IfThenElse exp then
        (* Manual tests
        val exp = ``BExp_IfThenElse
          (BExp_BinPred BIExp_LessThan (BExp_Const (Imm64 112w)) (BExp_Const (Imm64 11w)))
          (BExp_Const (Imm64 200w))
          (BExp_Const (Imm64 404w))``;
        *)
        let
          val (bir_cond_exp, bir_then_exp, bir_else_exp) = dest_BExp_IfThenElse exp
          val w_cond_exp = bir_exp_to_words bir_cond_exp
          (* Do we really want to do this "optimization"? *)
          val (bool_cond_exp, _, _) = dest_cond w_cond_exp
          val w_then_exp = bir_exp_to_words bir_then_exp
          val w_else_exp = bir_exp_to_words bir_else_exp
        in
          mk_cond (bool_cond_exp, w_then_exp, w_else_exp)
        end
          handle e => raise wrap_exn "bir_exp_to_words::if_then_else" e
      (* Load expressions *)
      else if is_BExp_Load exp then
        (* Manual tests
        val exp = ``
          BExp_Load
            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
            (BExp_Den (BVar "ADDR" (BType_Imm Bit32)))
            BEnd_BigEndian
            Bit16
        ``;
        val exp = ``
          BExp_Load
            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
            (BExp_Den (BVar "ADDR" (BType_Imm Bit64)))
            BEnd_LittleEndian
            Bit128
        ``;
        val w = bir_exp_to_words exp;
        *)
        (*
         * ((addr+0) :> mem) @@ ((addr+1) :> mem) @@ ...
         *)
        let
          val (bir_mem, bir_addr, bir_endi, bir_val_ty) = dest_BExp_Load exp
          val mem_w = bir_exp_to_words bir_mem
          val mem_right_ty = (hd o tl o snd o dest_type o type_of) mem_w
          val mem_right_bir_ty = bir_immtype_t_of_word_ty mem_right_ty
          val base_addr_w = bir_exp_to_words bir_addr
          val addr_w = bir_exp_to_words bir_addr
          val addr_bir_ty = (bir_immtype_t_of_word_ty o type_of) addr_w
          (* Compute the number of splits *)
          val nsplits_o_thm = EVAL ``bir_number_of_mem_splits
            ^mem_right_bir_ty ^bir_val_ty ^addr_bir_ty``
          val nsplits_o_tm = (snd o dest_eq o concl) nsplits_o_thm
          val nsplits = (Arbnumcore.fromInt o int_of_term o dest_some) nsplits_o_tm
            handle e => raise wrap_exn "bir_exp_to_words::load::nsplits" e;
          (* Create the list of reads with offsets *)
          fun offset_reads_up_to n acc =
            if n = Arbnumcore.zero then acc else
              let
                val offset = Arbnumcore.- (n, Arbnumcore.one);
                val offset_w = mk_word (offset, size_of base_addr_w);
                val addr = ``^base_addr_w + ^offset_w``;
                val load_tm = ``^addr :> ^mem_w``;
              in
                offset_reads_up_to (Arbnumcore.- (n, Arbnumcore.one)) (load_tm::acc)
              end
          val reads = offset_reads_up_to nsplits []
            handle e => raise wrap_exn "bir_exp_to_words::load::reads" e;
          (* Reorder reads according to endianess *)
          val ordered_reads = if is_BEnd_BigEndian bir_endi then reads
            else if is_BEnd_LittleEndian bir_endi then rev reads
            else if is_BEnd_NoEndian bir_endi then
              if nsplits = Arbnumcore.one then reads
                 else raise ERR "bir_exp_to_words" "BEnd_NoEndian and nsplits>1"
            else raise ERR "bir_exp_to_words"
              ("Unknown endianess: " ^ (term_to_string bir_endi))
            handle e => raise wrap_exn "bir_exp_to_words::load::endianess" e;
          (* Concatenate the reads into a single expression *)
          fun concat_ws [] = raise ERR "bir_exp_to_words" "nsplits = 0"
            | concat_ws (h::ws) = List.foldl mk_word_concat h ws
          val concat_w = concat_ws ordered_reads
            handle e => raise wrap_exn "bir_exp_to_words::load::concat" e;
          (* Type-isntantiate to the actual length *)
          val val_ty = word_ty_of_bir_immtype_t bir_val_ty
          val val_length_ty = dest_word_type val_ty
        in
          concat_w
        end
      (* Store expressions *)
      else if is_BExp_Store exp then
        (* Manual tests
        val exp = ``
          (BExp_Store
            (BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))
            (BExp_Den (BVar "ADDR1" (BType_Imm Bit32)))
            BEnd_BigEndian
            (BExp_Const (Imm16 (42w :word16))))
        ``;
        val exp = ``
          (BExp_Store
            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
            (BExp_Den (BVar "ADDR1" (BType_Imm Bit64)))
            BEnd_BigEndian
            (BExp_Const (Imm128 (42w :word128))))
        ``;
        val w = bir_exp_to_words exp;
        *)
        let
          val (bir_mem, bir_addr, bir_endi, bir_val) = dest_BExp_Store exp
          val mem_w = bir_exp_to_words bir_mem
          val mem_right_ty = (hd o tl o snd o dest_type o type_of) mem_w
          val mem_right_bir_ty = bir_immtype_t_of_word_ty mem_right_ty
          val base_addr_w = bir_exp_to_words bir_addr
          val addr_w = bir_exp_to_words bir_addr
          val addr_bir_ty = (bir_immtype_t_of_word_ty o type_of) addr_w
          val bir_val_ty = (dest_BType_Imm o bir_type_of) bir_val;
          (* Compute the number of splits *)
          val nsplits_o_thm = EVAL ``bir_number_of_mem_splits
            ^mem_right_bir_ty ^bir_val_ty ^addr_bir_ty``
          val nsplits_o_tm = (snd o dest_eq o concl) nsplits_o_thm
          val nsplits = (Arbnumcore.fromInt o int_of_term o dest_some) nsplits_o_tm
            handle e => raise wrap_exn "bir_exp_to_words::store::nsplits" e
          (* Create the list of writes with offsets *)
          val write_len = (dest_int_numeric_type o dest_word_type) mem_right_ty
          val write_len_num = Arbnumcore.fromInt write_len
          val write_len_ty = mk_numeric_type write_len_num
          val val_w = bir_exp_to_words bir_val
          fun offset_writes_up_to n acc =
            if n = Arbnumcore.zero then acc else
              let
                val offset = Arbnumcore.- (n, Arbnumcore.one)
                val offset_w = mk_word (offset, size_of base_addr_w)
                val addr_tm = ``^base_addr_w + ^offset_w``
                val low_bit = Arbnumcore.* (offset, write_len_num)
                val high_bit_plus_one = Arbnumcore.+ (low_bit, write_len_num)
                val high_bit = Arbnumcore.- (high_bit_plus_one, Arbnumcore.one)
                val low_bit_tm = mk_numeral low_bit
                val high_bit_tm = mk_numeral high_bit
                val val_tm = mk_word_extract
                  (high_bit_tm, low_bit_tm, val_w, write_len_ty)
                val store_tm = ``(^addr_tm =+ ^val_tm)``
              in
                offset_writes_up_to (Arbnumcore.- (n, Arbnumcore.one)) (store_tm::acc)
              end
          val writes = offset_writes_up_to nsplits []
            handle e => raise wrap_exn "bir_exp_to_words::store::writes" e;
          (* Fold using mk_comb *)
          val whole_store_tm = List.foldl (fn (update_tm, mem_tm) =>
            mk_comb (update_tm, mem_tm))
            mem_w writes
            handle e => raise wrap_exn "bir_exp_to_words::store::mk_comb" e;
        in
          whole_store_tm
        end
      (*** WP specific terms ***)
      (* Implications *)
      else if is_bir_exp_imp exp then
        (* Manual tests
        val exp = ``
          bir_exp_imp
            (BExp_BinPred BIExp_Equal
              (BExp_Const (Imm16 (42w :word16)))
              (BExp_Const (Imm16 (1337w :word16))))
            (BExp_Const (Imm1 (0w :word1)))
        ``;
        val exp = p_imp_wp_bir_tm;
        val w = bir_exp_to_words exp;
        *)
        let
          val (bir_lhs, bir_rhs) = dest_bir_exp_imp exp
          val lhs = (w2bool o bir_exp_to_words) bir_lhs
          val rhs = (w2bool o bir_exp_to_words) bir_rhs
          val imp = mk_imp (lhs, rhs)
        in
          bool2w imp
        end
          handle e => raise wrap_exn "bir_exp_to_words::imp" e
      (*** Unknown expressions ***)
      else
        raise ERR "bir_exp_to_words" ("Don't know BIR expression: " ^ (term_to_string exp))
    end;

  in

  fun bir2w bir_exp_tm = bir_exp_to_words bir_exp_tm;

  fun bir2bool bir_exp_tm = (w2bool o bir2w) bir_exp_tm;

  val w2bool = w2bool;
  val bool2w = bool2w;

  (* Tests *)
  val _ = if false then () else
    let
      fun test_bir_exp_to_words exp expected =
        let
          val actual = bir_exp_to_words exp;
          val _ = if actual = expected then () else
            raise ERR "test_bir_exp_to_words" ("Test failed:"
            ^ "\n - actual: " ^ (term_to_string actual)
            ^ "\n - expected: " ^ (term_to_string expected)
            );
        in () end;
      val t = test_bir_exp_to_words;
      (* Const *)
      val _ = t ``BExp_Const (Imm32 12345w)`` ``12345w: 32 word``;
      val _ = t ``BExp_Const (Imm64 12345w)`` ``12345w: 64 word``;
      (* Den *)
      val _ = t ``BExp_Den (BVar "name" (BType_Imm Bit64))`` ``name: 64 word``;
      val _ = t ``BExp_Den (BVar "x" (BType_Imm Bit1))`` ``x: 1 word``;
      val _ = t ``BExp_Den (BVar "y" (BType_Imm Bit16))`` ``y: 16 word``;
      val _ = t ``BExp_Den (BVar "z" (BType_Imm Bit32))`` ``z: 32 word``;
      (* Unary expressions *)
      val _ = t
        ``(BExp_UnaryExp BIExp_ChangeSign (BExp_Const (Imm8 12w)))``
        ``(-12w): 8 word``;
      val _ = t
        ``(BExp_UnaryExp BIExp_ChangeSign (BExp_Den (BVar "x" (BType_Imm Bit64))))``
        ``(-x): 64 word``;
      val _ = t
        ``(BExp_UnaryExp BIExp_Not
            (BExp_BinPred BIExp_Equal
              (BExp_Den (BVar "oracle" (BType_Imm Bit32)))
              (BExp_Const (Imm32 0w))))``
        ``(~(if (oracle: 32 word) = (0w: 32 word)
                  then (1w: 1 word)
                  else (0w: 1 word))): 1 word``
      (* Binary expressions *)
      val _ = t
        ``(BExp_BinExp BIExp_Minus
            (BExp_Den (BVar "x" (BType_Imm Bit64)))
            (BExp_Const (Imm64 112w)))`` ``(x - 112w): 64 word``;
      (* Binary predicates *)
      val _ = t
        ``(BExp_BinPred BIExp_LessThan
            (BExp_Den (BVar "x" (BType_Imm Bit128)))
            (BExp_Const (Imm128 112w)))``
        ``(if (x: 128 word) <₊ (112w: 128 word) then (1w: 1 word) else (0w: 1 word)): 1 word``;
      (* If-then-else *)
      val _ = t
        ``BExp_IfThenElse
            (BExp_BinPred BIExp_LessThan (BExp_Const (Imm64 112w)) (BExp_Const (Imm64 11w)))
              (BExp_Const (Imm64 200w))
              (BExp_Const (Imm64 404w))``
        ``if (112w :word64) <₊ (11w :word64)
            then (200w :word64)
            else (404w :word64)``;
      (* TODO: Write tests for store and loads *)
    in () end;

  end (* local *)

end (* bir_exp_to_wordsLib *)

