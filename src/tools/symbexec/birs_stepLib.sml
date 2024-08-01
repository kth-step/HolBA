structure birs_stepLib =
struct

local
  open HolKernel Parse boolLib bossLib;

  open bir_auxiliaryTheory;
  open bir_programTheory;

in
  val cur_stmt_lookup_fun = ref ((K (NONE)) : term -> thm option);
  val cur_l_mem_lookup_fun = ref ((K (NONE)) : term -> thm option);


(* ------------------------------------------------------------------------- *)

(*
val list_tm = bprog_l_tm;
val restr_consts = [bprog_tm];
*)
fun get_el_thms list_tm restr_consts =
  let
    val split_el_inst_thm = ISPEC list_tm SPLIT_ELs_0_thm;
    val split_conj_thm = CONV_RULE (RATOR_CONV (RAND_CONV EVAL) THENC computeLib.RESTR_EVAL_CONV (listSyntax.el_tm::restr_consts)) split_el_inst_thm;
  in
    (CONJUNCTS split_conj_thm,
     EVAL (listSyntax.mk_length list_tm))
  end;

(* ------------------------------------------------------------------------- *)

(* patch for lifter theorem *)
fun patch_lifter_thm lift_thm =
   if (List.null o hyp) lift_thm
   then lift_thm
   else patch_lifter_thm ((REWRITE_RULE [] o CONV_RULE (RATOR_CONV (RAND_CONV EVAL)) o (fn t => DISCH ((hd o hyp) t) t)) lift_thm);

(* ------------------------------------------------------------------------- *)

fun dest_block_thm block_thm =
  let
    val block_thm_tm = concl block_thm;
    val i_tm = (fst o listSyntax.dest_el o fst o dest_eq) block_thm_tm;
    val block_tm = (snd o dest_eq) block_thm_tm;
    val (l_tm,stmts_tm,_) = bir_programSyntax.dest_bir_block block_tm;
  in
    (i_tm, block_tm, l_tm, stmts_tm)
  end;

val bir_get_program_block_info_by_label_tm = “bir_get_program_block_info_by_label”;
fun gen_stmt_thms bprog_tm prog_length_thm bir_get_block_GEN_thm block_thm =
  let
    val (i_tm, block_tm, l_tm, stmts_tm) = dest_block_thm block_thm;
    val n_stmts = ((length o fst o listSyntax.dest_list) stmts_tm) + 1;
    val inst_thm1 = SPECL [l_tm, i_tm, block_tm] bir_get_block_GEN_thm;
    val inst_thm2 = CONV_RULE (RAND_CONV (REWRITE_CONV [block_thm, prog_length_thm] THENC EVAL)) inst_thm1;
    val inst_thm3 = REWRITE_RULE [] inst_thm2;

    val pc_tms = List.tabulate(n_stmts, fn i => bir_programSyntax.mk_bir_programcounter (l_tm, numSyntax.term_of_int i));
    (* val pc_tm = hd pc_tms; *)
    fun gen_stmt_thm pc_tm =
      let
        val inst_s_thm0 = ISPECL [bprog_tm, pc_tm] bir_programTheory.bir_get_current_statement_def;
        val inst_s_thm1 = CONV_RULE (RAND_CONV (computeLib.RESTR_EVAL_CONV [bprog_tm, bir_get_program_block_info_by_label_tm] THENC REWRITE_CONV [inst_thm3] THENC EVAL)) inst_s_thm0;
      in
        (pc_tm, inst_s_thm1)
      end;
  in
    map gen_stmt_thm pc_tms
  end;

fun gen_exec_prep_thms bprog_tm valid_labels_thm =
let
  val bprog_l_tm = “bir_get_blocks ^bprog_tm”;

  val (block_thms, prog_length_thm) = get_el_thms bprog_l_tm [bprog_tm];

  val bir_get_block_GEN_thm =
    REWRITE_RULE [bir_get_blocks_INV_thm]
      (MATCH_MP
        (CONJUNCT2 bir_program_valid_stateTheory.bir_get_program_block_info_by_label_valid_THM)
        valid_labels_thm);

  val stmt_thms = List.concat (map (gen_stmt_thms bprog_tm prog_length_thm bir_get_block_GEN_thm) block_thms);

  val label_idx_tms = List.map ((fn (i_tm, _, l_tm, _) => (l_tm, i_tm)) o dest_block_thm) block_thms;
    
  val label_tms = List.map fst label_idx_tms;
  (*val l_tm = last label_tms;*)
  fun gen_label_mem_thm l_tm =
    let
      val block_idx_tm = case List.find (identical l_tm o fst) label_idx_tms of SOME x => snd x | _ => raise Feedback.mk_HOL_ERR "" "gen_exec_prep_thms::gen_label_mem_thm" "this should not happen";
      val labels_tm = bir_programSyntax.mk_bir_labels_of_program bprog_tm;
      val length_thm = (REWRITE_CONV [bir_get_blocks_labels_length_thm, prog_length_thm] THENC EVAL) (numSyntax.mk_less (block_idx_tm, listSyntax.mk_length labels_tm));
      val helper_thm = REWRITE_RULE [GSYM bir_get_blocks_labels_length_thm, length_thm] (ISPECL [bprog_tm, block_idx_tm] bir_get_blocks_labels_EL_thm);

      val eval_tm = listSyntax.mk_mem (l_tm, labels_tm);
      val mem_el_thm = REWRITE_CONV [listTheory.MEM_EL] eval_tm;
      val exists_tm = (snd o dest_eq o concl) mem_el_thm;
      val exists_inst_tm = ((subst [``n:num`` |-> block_idx_tm] o snd o dest_exists) exists_tm);
      val inst_idx_thm = (REWRITE_CONV (length_thm::helper_thm::block_thms) THENC EVAL) exists_inst_tm;
      val gen_thm = EXISTS (exists_tm, block_idx_tm) (REWRITE_RULE [] inst_idx_thm);
      val label_mem_thm = REWRITE_RULE [gen_thm] mem_el_thm;
    in
      (l_tm, label_mem_thm)
    end;
  val label_mem_thms = List.map gen_label_mem_thm label_tms;
in
  (stmt_thms, label_mem_thms)
end;

fun gen_exec_prep_thms_from_lift_thm bir_lift_thm =
let
  val bprog_tm = (snd o dest_comb o concl) bir_lift_thm;
  val bprog_l_tm = “bir_get_blocks ^bprog_tm”;
  val valid_labels_thm = prove(“
      bir_is_valid_labels (BirProgram ^bprog_l_tm)
    ”,
      REWRITE_TAC [bir_get_blocks_INV_thm] >>
      REWRITE_TAC [REWRITE_RULE [bir_inst_liftingTheory.bir_is_lifted_prog_def] bir_lift_thm]
    );
in
  gen_exec_prep_thms bprog_tm valid_labels_thm
end;

(*
val (stmt_thms, label_mem_thms) = prep_structure;
*)
fun gen_lookup_functions (stmt_thms, label_mem_thms) =
  let
    val stmt_map = Redblackmap.insertList (Redblackmap.mkDict Term.compare, stmt_thms);
    val l_mem_map = Redblackmap.insertList (Redblackmap.mkDict Term.compare, label_mem_thms);
    fun lookup_fun m k = 
      SOME (Redblackmap.find (m, k))
      handle NotFound => NONE;
  in
    (lookup_fun stmt_map, lookup_fun l_mem_map)
  end;

fun prepare_program_lookups bir_lift_thm =
let
  val prep_structure = Profile.profile "gen_exec_prep_thms" gen_exec_prep_thms_from_lift_thm bir_lift_thm;
  val (stmt_lookup_fun, l_mem_lookup_fun) = gen_lookup_functions prep_structure;
  val _ = cur_stmt_lookup_fun := stmt_lookup_fun;
  val _ = cur_l_mem_lookup_fun := l_mem_lookup_fun;
in
  ()
end;

(* ------------------------------------------------------------------------- *)
end

local

open HolKernel Parse boolLib bossLib;
open computeLib;

open bir_exp_substitutionsTheory;
open bir_expTheory;

open bir_symbTheory;
open birs_auxTheory;

open bir_exp_typecheckLib;

  (* error handling *)
  val libname = "bir_symbLib"
  val ERR = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname


(* TODO: this is stolen from exec tool *)
  fun GEN_match_conv is_tm_fun conv tm =
    if is_tm_fun tm then
      conv tm
    else if is_comb tm then
        ((RAND_CONV  (GEN_match_conv is_tm_fun conv)) THENC
         (RATOR_CONV (GEN_match_conv is_tm_fun conv))) tm
    else if is_abs tm then
        TRY_CONV (ABS_CONV (GEN_match_conv is_tm_fun conv)) tm
    else
      raise UNCHANGED
    ;


(*
birs_senv_typecheck_CONV test_term_birs_senv_typecheck
*)
val is_birs_senv_typecheck =
  ((fn x => (identical ``birs_senv_typecheck`` o fst) x andalso ((fn l => l = 2) o length o snd) x) o strip_comb);
val birs_senv_typecheck_CONV = (
  RESTR_EVAL_CONV [``type_of_bir_exp``] THENC
  GEN_match_conv (bir_typing_expSyntax.is_type_of_bir_exp) (type_of_bir_exp_DIRECT_CONV) THENC
  EVAL
);
val birs_senv_typecheck_CONV = Profile.profile "senv_typecheck_CONV" birs_senv_typecheck_CONV;

(*
CBV_CONV (new_compset [
  birs_eval_exp_subst_def,
  bir_exp_subst_def,
  bir_exp_subst_var_def,
  bir_typing_expTheory.bir_vars_of_exp_def,
  finite_mapTheory.FLOOKUP_DEF
]) test_term_birs_eval_exp_subst
*)

(*
val test_term_birs_eval_exp = ``
birs_eval_exp
            (BExp_BinExp BIExp_Plus
               (BExp_Den (BVar "countw" (BType_Imm Bit64)))
               (BExp_Const (Imm64 1w)))
            (birs_gen_env
               [("R7",BExp_Den (BVar "sy_R7" (BType_Imm Bit32)));
                ("SP_process",
                 BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)));
                ("countw",BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))])
``;

birs_eval_exp_CONV test_term_birs_eval_exp
*)
val birs_eval_exp_CONV = (
  CBV_CONV (new_compset [birs_eval_exp_def, birs_gen_env_thm, birs_gen_env_NULL_thm]) THENC
  GEN_match_conv (bir_typing_expSyntax.is_type_of_bir_exp) (type_of_bir_exp_DIRECT_CONV) THENC
  GEN_match_conv (is_birs_senv_typecheck) (birs_senv_typecheck_CONV) THENC
  EVAL
);
val birs_eval_exp_CONV = Profile.profile "eval_exp_CONV" birs_eval_exp_CONV;

(*
val test_term = ``
birs_exec_step bprog_test
      <|bsst_pc := <|bpc_label := BL_Address (Imm32 2826w); bpc_index := 1|>;
        bsst_environ :=
          birs_gen_env
            [("R7",BExp_Den (BVar "sy_R7" (BType_Imm Bit32)));
             ("SP_process",BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)));
             ("countw",BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))];
        bsst_status := BST_Running;
        bsst_pcond :=
          BExp_BinExp BIExp_And (BExp_Const (Imm1 1w))
            (BExp_BinPred BIExp_LessOrEqual
               (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
               (BExp_Const (Imm64 0xFFFFFFFFFFFFFFFEw)))|>
``;

val bstate_tm = ``
  <|bsst_pc := <|bpc_label := BL_Address (Imm64 0x10w); bpc_index := 1|>;
    bsst_environ :=
      birs_gen_env
        [("x2",BExp_Den (BVar "sy_x2" (BType_Imm Bit64)));
         ("x1",BExp_Const (Imm64 0x14w))];
    bsst_status := BST_Running;
    bsst_pcond := (BExp_Const (Imm1 1w))|>
``;
val bprog_tm = ``
  BirProgram [
          <|bb_label := BL_Address (Imm64 0x10w);
             bb_statements :=
               [BStmt_Assert
                  (BExp_UnaryExp BIExp_Not
                     (BExp_LSB
                        (BExp_BinExp BIExp_And
                           (BExp_Const (Imm64 0xFFFFFFFFFFFFFFFEw))
                           (BExp_Den (BVar "x1" (BType_Imm Bit64))))))];
             bb_last_statement :=
               BStmt_Jmp
                 (BLE_Exp
                    (BExp_BinExp BIExp_And
                       (BExp_Const (Imm64 0xFFFFFFFFFFFFFFFEw))
                       (BExp_Den (BVar "x1" (BType_Imm Bit64)))))|>;
          <|bb_label :=
               BL_Address (Imm64 0x14w);
             bb_statements :=
               [BStmt_Assign (BVar "x2" (BType_Imm Bit64))
                  (BExp_BinExp BIExp_Minus
                     (BExp_Den (BVar "x2" (BType_Imm Bit64)))
                     (BExp_Const (Imm64 32w)))];
             bb_last_statement :=
               BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x18w)))|>]
``;
val test_term = ``birs_exec_step ^bprog_tm ^bstate_tm``;
birs_exec_step_CONV test_term;

val test_eval_label_term = ``
birs_eval_label_exp
          (BLE_Exp
             (BExp_BinExp BIExp_And (BExp_Const (Imm64 0xFFFFFFFFFFFFFFFEw))
                (BExp_Den (BVar "x1" (BType_Imm Bit64)))))
          (birs_gen_env
             [("x2",BExp_Den (BVar "sy_x2" (BType_Imm Bit64)));
              ("x1",BExp_Const (Imm64 20w))]) (BExp_Const (Imm1 1w))
``;
val test_eval_label_term = ``
birs_eval_label_exp
  (BLE_Exp
     (BExp_BinExp BIExp_And (BExp_Const (Imm64 0xFFFFFFFFFFFFFFFEw))
        (BExp_Den (BVar "x1" (BType_Imm Bit64)))))
  (birs_gen_env
     [("x2",
       BExp_BinExp BIExp_Minus (BExp_Den (BVar "sy_x2" (BType_Imm Bit64)))
         (BExp_Const (Imm64 32w)));
      ("x8",
       BExp_BinExp BIExp_Minus (BExp_Den (BVar "sy_x2" (BType_Imm Bit64)))
         (BExp_Const (Imm64 0w)));
      ("x10",
       BExp_Cast BIExp_SignedCast
         (BExp_Cast BIExp_LowCast
            (BExp_BinExp BIExp_Plus
               (BExp_Cast BIExp_SignedCast
                  (BExp_Cast BIExp_LowCast
                     (BExp_Load
                        (BExp_Den (BVar "sy_MEM8" (BType_Mem Bit64 Bit8)))
                        (BExp_Const (Imm64 256w)) BEnd_LittleEndian Bit64)
                     Bit32) Bit64) (BExp_Const (Imm64 10w))) Bit32) Bit64);
      ("x15",
       BExp_Cast BIExp_SignedCast
         (BExp_Cast BIExp_LowCast
            (BExp_BinExp BIExp_Plus
               (BExp_Cast BIExp_SignedCast
                  (BExp_Cast BIExp_LowCast
                     (BExp_Load
                        (BExp_Den (BVar "sy_MEM8" (BType_Mem Bit64 Bit8)))
                        (BExp_Const (Imm64 256w)) BEnd_LittleEndian Bit64)
                     Bit32) Bit64) (BExp_Const (Imm64 10w))) Bit32) Bit64);
      ("x14",BExp_Const (Imm64 10w));
      ("MEM8",
       BExp_Store
         (BExp_Store
            (BExp_Store
               (BExp_Store
                  (BExp_Store
                     (BExp_Store
                        (BExp_Den (BVar "sy_MEM8" (BType_Mem Bit64 Bit8)))
                        (BExp_BinExp BIExp_Minus
                           (BExp_Den (BVar "sy_x2" (BType_Imm Bit64)))
                           (BExp_Const (Imm64 8w))) BEnd_LittleEndian
                        (BExp_Den (BVar "sy_x1" (BType_Imm Bit64))))
                     (BExp_BinExp BIExp_Minus
                        (BExp_Den (BVar "sy_x2" (BType_Imm Bit64)))
                        (BExp_Const (Imm64 16w))) BEnd_LittleEndian
                     (BExp_Den (BVar "sy_x8" (BType_Imm Bit64))))
                  (BExp_BinExp BIExp_Minus
                     (BExp_Den (BVar "sy_x2" (BType_Imm Bit64)))
                     (BExp_Const (Imm64 20w))) BEnd_LittleEndian
                  (BExp_Cast BIExp_LowCast (BExp_Const (Imm64 1w)) Bit32))
               (BExp_BinExp BIExp_Minus
                  (BExp_Den (BVar "sy_x2" (BType_Imm Bit64)))
                  (BExp_Const (Imm64 40w))) BEnd_LittleEndian
               (BExp_BinExp BIExp_Minus
                  (BExp_Den (BVar "sy_x2" (BType_Imm Bit64)))
                  (BExp_Const (Imm64 0w))))
            (BExp_BinExp BIExp_Minus
               (BExp_Den (BVar "sy_x2" (BType_Imm Bit64)))
               (BExp_Const (Imm64 56w))) BEnd_LittleEndian
            (BExp_Const (Imm64 3w)))
         (BExp_BinExp BIExp_Minus (BExp_Den (BVar "sy_x2" (BType_Imm Bit64)))
            (BExp_Const (Imm64 60w))) BEnd_LittleEndian
         (BExp_Cast BIExp_LowCast (BExp_Const (Imm64 7w)) Bit32));
      ("x1",BExp_Const (Imm64 1692w)); ("x11",BExp_Const (Imm64 7w))])
  (BExp_BinExp BIExp_And
     (BExp_BinPred BIExp_Equal (BExp_Den (BVar "sy_x2" (BType_Imm Bit64)))
        (BExp_Const (Imm64 pre_x2)))
     (BExp_BinExp BIExp_And
        (BExp_BinPred BIExp_Equal
           (BExp_BinExp BIExp_And (BExp_Den (BVar "sy_x2" (BType_Imm Bit64)))
              (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)))
        (BExp_BinExp BIExp_And
           (BExp_BinPred BIExp_LessOrEqual (BExp_Const (Imm64 8192w))
              (BExp_Den (BVar "sy_x2" (BType_Imm Bit64))))
           (BExp_BinPred BIExp_LessThan
              (BExp_Den (BVar "sy_x2" (BType_Imm Bit64)))
              (BExp_Const (Imm64 0x100000000w))))))
``;
birs_eval_label_exp_CONV test_eval_label_term;
*)

(*
is_plain_jumptarget_set ``{BL_Address (Imm64 20w)}``
is_plain_jumptarget_set ``{BL_Address iv | Imm64 20w = iv}``
*)
fun is_plain_jumptarget_set tm =
  let
    val l = pred_setSyntax.strip_set tm;
  in
    List.all (fn e_tm =>
      bir_programSyntax.is_BL_Address e_tm andalso
      bir_immSyntax.gen_is_Imm (bir_programSyntax.dest_BL_Address e_tm)) l
  end handle _ => false;

(*
val tm = ``birs_symbval_concretizations
          (BExp_BinExp BIExp_And
             (BExp_BinPred BIExp_Equal
                (BExp_Den (BVar "sy_x2" (BType_Imm Bit64)))
                (BExp_Const (Imm64 pre_x2)))
             (BExp_BinExp BIExp_And
                (BExp_BinPred BIExp_Equal
                   (BExp_BinExp BIExp_And
                      (BExp_Den (BVar "sy_x2" (BType_Imm Bit64)))
                      (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)))
                (BExp_BinExp BIExp_And
                   (BExp_BinPred BIExp_LessOrEqual (BExp_Const (Imm64 8192w))
                      (BExp_Den (BVar "sy_x2" (BType_Imm Bit64))))
                   (BExp_BinPred BIExp_LessThan
                      (BExp_Den (BVar "sy_x2" (BType_Imm Bit64)))
                      (BExp_Const (Imm64 0x100000000w))))))
          (BExp_BinExp BIExp_And (BExp_Const (Imm64 0xFFFFFFFFFFFFFFFEw))
             (BExp_Const (Imm64 1692w)))``;
val tm = ``birs_symbval_concretizations
                (BExp_BinExp BIExp_And
                   (BExp_BinPred BIExp_LessThan
		      (BExp_Const (Imm64 0x20w))
                      (BExp_Den (BVar "sy_x2" (BType_Imm Bit64))))
                   (BExp_BinPred BIExp_LessThan
                      (BExp_Den (BVar "sy_x2" (BType_Imm Bit64)))
                      (BExp_Const (Imm64 0x20w))))
          (BExp_BinExp BIExp_And (BExp_Const (Imm64 0xFFFFFw))
             (BExp_Const (Imm64 1692w)))``;
birs_symbval_concretizations_oracle_CONV tm;
*)
val is_birs_symbval_concretizations = identical ``birs_symbval_concretizations`` o fst o strip_comb;
val birs_symbval_concretizations_oracle_CONV =
  (fn tm => if is_birs_symbval_concretizations tm then REFL tm else
   (print_term tm;
    raise ERR "birs_symbval_concretizations_oracle_CONV" "something is not right here, expect a birs_symbval_concretizations")) THENC
  (fn tm => let
    val vaex_tm = (snd o dest_comb) tm;
    val pcond_tm = (snd o dest_comb o fst o dest_comb) tm;
    val pcond_is_sat = birs_smtLib.bir_check_sat false pcond_tm;
    val pcond_sat_thm =
     if pcond_is_sat then
       mk_oracle_thm "BIRS_SIMP_LIB_Z3" ([], ``?i. birs_interpret_fun i ^pcond_tm = SOME bir_val_true``)
     else
       mk_oracle_thm "BIRS_SIMP_LIB_Z3" ([], ``!i. birs_interpret_fun i ^pcond_tm = SOME bir_val_false``);
    val res_thm =
     if not pcond_is_sat then
       SIMP_RULE (std_ss) [pcond_sat_thm] (SPECL [pcond_tm, vaex_tm] birs_rulesTheory.birs_jumptarget_empty_thm)
     else
     let
      val vaex_thm = EVAL ``birs_interpret_fun i ^vaex_tm``;
      val concr_thm = SIMP_RULE (std_ss++HolBACoreSimps.holBACore_ss) [vaex_thm, pcond_sat_thm] (SPECL [pcond_tm, vaex_tm] birs_rulesTheory.birs_jumptarget_singletonconst_thm);
     in
      concr_thm
     end;
   in
    if
      identical tm ((fst o dest_eq o concl) res_thm)
      handle _ => raise ERR "birs_symbval_concretizations_oracle_CONV" "failed to resolve single jump target, not an equality theorem"
    then res_thm else
    raise ERR "birs_symbval_concretizations_oracle_CONV" "failed to resolve single jump target"
   end);

val is_birs_eval_label_exp = identical ``birs_eval_label_exp`` o fst o strip_comb;
val birs_eval_label_exp_CONV = (
  (*(fn tm => (print_term tm; REFL tm)) THENC*)
  (fn tm => if is_birs_eval_label_exp tm then REFL tm else
   raise ERR "birs_eval_label_exp_CONV" "something is not right here, expect a birs_eval_label_exp") THENC
  RESTR_EVAL_CONV [``birs_eval_exp``, ``birs_gen_env``, ``birs_symbval_concretizations``] THENC
  GEN_match_conv (identical ``birs_eval_exp`` o fst o strip_comb) (birs_eval_exp_CONV) THENC
  RESTR_EVAL_CONV [``birs_symbval_concretizations``] THENC

(* here we should have either NONE or SOME and a set that is either trivially singleton of a constant or we have to resolve it into a set of constants *)
  (fn tm =>
    if optionSyntax.is_none tm then REFL tm else
    if optionSyntax.is_some tm then RAND_CONV (
      (fn tm => if is_birs_symbval_concretizations tm then birs_symbval_concretizations_oracle_CONV tm else REFL tm) THENC
      (* here we should have a simple set of constants *)
      (fn tm => if is_plain_jumptarget_set tm then REFL tm else
        (print_term tm;
         raise ERR "birs_eval_label_exp_CONV" "could not resolve the jump targets"))
    ) tm else
    raise ERR "birs_eval_label_exp_CONV" "something is not right here, should be NONE or SOME")
);

val birs_state_t_ty = mk_type ("birs_state_t", []);
fun dest_birs_state tm = let
  val (ty, l) = TypeBase.dest_record tm
  val _ = if ty = birs_state_t_ty then () else fail()
  val pc = Lib.assoc "bsst_pc" l
  val env = Lib.assoc "bsst_environ" l
  val status = Lib.assoc "bsst_status" l
  val pcond = Lib.assoc "bsst_pcond" l
in
  (pc, env, status, pcond)
end handle e => (print_term tm; raise wrap_exn "dest_bir_state" e);

local
  open bir_expSyntax;
in
 fun is_bir_exp t =
  type_of t = bir_exp_t_ty;

 fun bir_exp_size t =
  if is_BExp_Const t then
     1
  else if is_BExp_MemConst t then
     1
  else if is_BExp_Den t then
     1
  else if is_BExp_Cast t then
   let
     val (_,x,_) = dest_BExp_Cast t;
   in
     1 + bir_exp_size x
   end
  else if is_BExp_UnaryExp t then
   let
     val (_,x) = dest_BExp_UnaryExp t;
   in
     1 + bir_exp_size x
   end
  else if is_BExp_BinExp t then
   let
     val (_,x1,x2) = dest_BExp_BinExp t;
   in
     1 + bir_exp_size x1 + bir_exp_size x2
   end
  else if is_BExp_BinPred t then
   let
     val (_,x1,x2) = dest_BExp_BinPred t;
   in
     1 + bir_exp_size x1 + bir_exp_size x2
   end
  else if is_BExp_MemEq t then
   let
     val (x1,x2) = dest_BExp_MemEq t;
   in
     1 + bir_exp_size x1 + bir_exp_size x2
   end
  else if is_BExp_IfThenElse t then
   let
     val (c,x1,x2) = dest_BExp_IfThenElse t;
   in
     1 + bir_exp_size c + bir_exp_size x1 + bir_exp_size x2
   end
  else if is_BExp_Load t then
   let
     val (mem_e,a_e,_,_) = dest_BExp_Load t;
   in
     1 + bir_exp_size mem_e + bir_exp_size a_e
   end
  else if is_BExp_Store t then
   let
     val (mem_e,a_e,_,v_e) = dest_BExp_Store t;
   in
     1 + bir_exp_size mem_e + bir_exp_size a_e + bir_exp_size v_e
   end
(*
  else if is_... t then
   let
     val (_,x1,...) = dest_... t;
   in
     1 + bir_exp_size x1 + ...
   end
*)
  else raise ERR "bir_exp_size" ("unknown BIR expression " ^ (term_to_string t));
end

fun count_term is_tm_fun count_tm_fun tm =
    if is_tm_fun tm then
      count_tm_fun tm
    else if is_comb tm then
      let
        val (rator,rand) = dest_comb tm;
      in
        (count_term is_tm_fun count_tm_fun rator) +
        (count_term is_tm_fun count_tm_fun rand)
      end
    else if is_abs tm then
      count_term is_tm_fun count_tm_fun ((snd o dest_abs) tm)
    else
      0
    ;

fun get_birs_state_size t =
  let
    val (_, env, _, pcond) = dest_birs_state t;
    val n_pcond = bir_exp_size pcond;
    val n_env = count_term is_bir_exp bir_exp_size env;
  in
    n_pcond + n_env
  end;

fun measure_fun s f v =
  let
    val timer = bir_miscLib.timer_start 0;
    val res = f v;
    val _ = bir_miscLib.timer_stop (fn delta_s => print (s ^ delta_s ^ "\n")) timer;
  in
    res
  end;

local
  fun syntax_fns n d m = HolKernel.syntax_fns {n = n, dest = d, make = m} "bir_program"
  val syntax_fns2 = syntax_fns 2 HolKernel.dest_binop HolKernel.mk_binop;
 open bir_programTheory;
in
 val (bir_get_current_statement_tm,  mk_bir_get_current_statement, dest_bir_get_current_statement, is_bir_get_current_statement)  = syntax_fns2 "bir_get_current_statement";
end;

fun birs_exec_step_CONV_pre t =
let
 val bprog_tm = (snd o dest_comb o fst o dest_comb) t;
 val _ = print_term bprog_tm;
 val _ = if is_const bprog_tm then () else
         raise ERR "birs_exec_step_CONV" "program term is not a constant";
in
 t |>
(* (fn t => ((print_term o snd o dest_comb) t; print "\n"; t)) |>*)
 (fn t => ((print_term o (fn (x,_,_,_) => x) o dest_birs_state o snd o dest_comb) t; t)) |>
 (fn t => (print ("symb state term size = " ^ ((Int.toString o term_size) t) ^ "\n"); t)) |>
 (fn t => (print ("symb state bir expression sizes = " ^ ((Int.toString o get_birs_state_size o snd o dest_comb) t) ^ "\n"); t)) |>
 (fn t => (bprog_tm)) 
end;
val birs_exec_step_CONV_pre = Profile.profile "exec_step_CONV_pre" birs_exec_step_CONV_pre;

(*
val test_term = (snd o dest_eq o snd o strip_forall o concl) bir_symbTheory.birs_exec_step_def;
((fn (_,x,_) => x) o TypeBase.dest_case o (fn (_,_,x) => x) o dest_cond) test_term
(snd o dest_comb o fst o dest_comb o fst o dest_comb o snd o dest_comb) test_term

val test_term = (fst o dest_eq o snd o strip_forall o concl) bir_symbTheory.birs_exec_step_def;
(snd o dest_comb) test_term
*)

(*
val test_term = ``ABC (BExp_BinExp BIExp_Plus (BExp_Const (Imm64 0w))
                            (BExp_BinExp BIExp_LeftShift
                               (BExp_Cast BIExp_SignedCast
                                  (BExp_BinExp BIExp_RightShift
                                     (BExp_Cast BIExp_LowCast
                                        (BExp_BinExp BIExp_Xor
                                           (BExp_Cast BIExp_SignedCast
                                              (BExp_Load
                                                 (BExp_Den
                                                    (BVar "sy_MEM8"
                                                       (BType_Mem Bit64 Bit8)))
                                                 (BExp_BinExp BIExp_Plus
                                                    (BExp_Den
                                                       (BVar "sy_x12"
                                                          (BType_Imm Bit64)))
                                                    (BExp_Const (Imm64 4w)))
                                                 BEnd_LittleEndian Bit32)
                                              Bit64)
                                           (BExp_Cast BIExp_SignedCast
                                              (BExp_Load
                                                 (BExp_Den
                                                    (BVar "sy_MEM8"
                                                       (BType_Mem Bit64 Bit8)))
                                                 (BExp_BinExp BIExp_Plus
                                                    (BExp_Den
                                                       (BVar "sy_x10"
                                                          (BType_Imm Bit64)))
                                                    (BExp_Const (Imm64 4w)))
                                                 BEnd_LittleEndian Bit32)
                                              Bit64)) Bit32)
                                     (BExp_Const (Imm32 24w))) Bit64)
                               (BExp_Const (Imm64 2w)))) (DEF:num) = 0w:word64``;
val test_thm = prove(test_term, cheat);

val subs_tm = (snd o dest_comb o fst o dest_comb o fst o dest_eq o concl) test_thm;
val abc_tm = ``(abc:bir_exp_t)``;
val eq_tm = ``^abc_tm = ^subs_tm``

val B_tm = ``(B:bir_exp_t)``;
val pat_tm = ``ABC ^B_tm (DEF:num) = 0w:word64``;

SUBST [B_tm |-> GSYM (ASSUME eq_tm)] pat_tm test_thm

val changed_thm = REWRITE_RULE [GSYM (ASSUME eq_tm)] test_thm;

(*
val changed_back_thm = SIMP_RULE std_ss [] (DISCH_ALL changed_thm);

val changed_back_thm = REWRITE_RULE [] (CONV_RULE (RATOR_CONV EVAL) (INST [abc_tm |-> subs_tm] (DISCH_ALL changed_thm)));
*)

val changed_back_thm = BETA_RULE (CONV_RULE (RATOR_CONV EVAL) (INST [abc_tm |-> subs_tm] (DISCH_ALL changed_thm)));

val changed_back_thm = MP (INST [abc_tm |-> subs_tm] (DISCH_ALL changed_thm)) (REFL subs_tm);

val changed_back_thm = MP (DISCH_ALL (INST [abc_tm |-> subs_tm] (changed_thm))) (REFL subs_tm);

val changed_back_thm = REWRITE_RULE [gen_rev_thm] (DISCH_ALL (INST [abc_tm |-> subs_tm] (changed_thm)));

prove(``
  ^test_term
``,
  METIS_TAC [changed_back_thm]
);

*)

val gen_rev_thm = prove(``!A B. ((A = A) ==> B) ==> B``, METIS_TAC []);
val env_abbr_tm = ``temp_env_abbr : string -> bir_exp_t option``;
val pcond_abbr_tm = ``temp_pcond_abbr : bir_exp_t``;
fun abbr_app (t, env_tm, pcond_tm) =
  let
     val env_eq_tm = mk_eq (env_abbr_tm, env_tm);
     val pcond_eq_tm = mk_eq (pcond_abbr_tm, pcond_tm);
     val env_eq_thm = ASSUME (env_eq_tm);
     val pcond_eq_thm = ASSUME (pcond_eq_tm);
     val abbr_thm = REWRITE_CONV [GSYM (env_eq_thm), GSYM (pcond_eq_thm)] t;
  in
    (abbr_thm, [env_eq_thm, pcond_eq_thm])
  end;
val abbr_app = Profile.profile "abbr_app" abbr_app;
fun abbr_rev (res, env_tm, pcond_tm) =
  REWRITE_RULE [gen_rev_thm] (DISCH_ALL (INST [env_abbr_tm |-> env_tm, pcond_abbr_tm |-> pcond_tm] res));
val abbr_rev = Profile.profile "abbr_rev" abbr_rev;

(*
https://github.com/kth-step/HolBA/blob/master/src/tools/exec/bir_exec_blockLib.sml
https://github.com/kth-step/HolBA/blob/dev_symbnoproof_next/src/tools/symbexec/examples/binaries/binariesLib.sml
*)
fun pc_lookup_fallback_fun pc_lookup_t =
  let
     val _ = print "falling back to evaluation to get current statement";
     val pc_lookup_thm = EVAL pc_lookup_t;
  in
    pc_lookup_thm
  end;
fun pc_lookup_fun (bprog_tm, pc_tm) =
  let
     val pc_lookup_t = mk_bir_get_current_statement (bprog_tm, pc_tm);
  in
 case (!cur_stmt_lookup_fun) pc_tm of
     NONE =>  pc_lookup_fallback_fun pc_lookup_t
   | SOME x => if (identical pc_lookup_t o fst o dest_eq o concl) x then x else pc_lookup_fallback_fun pc_lookup_t
  end;
val pc_lookup_fun = Profile.profile "pc_lookup_fun" pc_lookup_fun;

val birs_exec_stmt_tm = ``birs_exec_stmt``;
fun birs_exec_step_CONV_p1 (bprog_tm, t) = (* get the statement *)
 ((fn t =>
   let
     val st_tm = (snd o dest_comb) t;
     val (pc_tm,env_tm,_,pcond_tm) = (dest_birs_state) st_tm;
     val pc_lookup_thm = pc_lookup_fun (bprog_tm, pc_tm);
     (*val _ = print_thm pc_lookup_thm;*)
     (*val _ = computeLib.del_consts [bprog_tm]; (* (fst o strip_comb) pc_lookup_t,  *)*)
     (*val _ = computeLib.del_funs [bir_programTheory.bir_get_current_statement_def];*)
     (*val _ = computeLib.add_funs [pc_lookup_thm];*)
     (*val _ = computeLib.add_thms [pc_lookup_thm] (computeLib.the_compset);*)

     val (abbr_thm, eq_thms) = abbr_app (t, env_tm, pcond_tm);

     val rhs_tm = (snd o dest_eq o concl) abbr_thm;
     val res = (*CONV_RULE (RAND_CONV*) (
             REWRITE_CONV [birs_exec_step_def, bir_symbTheory.birs_state_t_accfupds, combinTheory.K_THM, pc_lookup_thm]
       THENC RESTR_EVAL_CONV ([bprog_tm, birs_exec_stmt_tm])
       ) rhs_tm;
(*      )) abbr_thm;*)
     val res = TRANS abbr_thm res;
(*TRANS (EVAL ``1+3:num``) (GSYM (EVAL ``2+2:num``))*)

(*
val res = abbr_rev (res, env_tm, pcond_tm);
*)
(*
     val _ = print_thm abbr_thm;
     val _ = print_thm res;
     val _ = raise ERR "" "";
*)
   in
     (res, env_tm, pcond_tm, eq_thms)
   end
  )
 ) t;
val birs_exec_step_CONV_p1 = Profile.profile "exec_step_CONV_p1" birs_exec_step_CONV_p1;

val birs_eval_label_exp_tm = ``birs_eval_label_exp``;
val birs_eval_exp_tm = ``birs_eval_exp``;
val birs_update_env_tm = ``birs_update_env : string # bir_exp_t -> (string -> bir_exp_t option) -> string -> bir_exp_t option``;
val birs_gen_env_tm = ``birs_gen_env``;

val is_birs_eval_exp = (identical birs_eval_exp_tm o fst o strip_comb);

(*
val birs_exec_step_CONV_p2 =
  GEN_match_conv is_birs_eval_label_exp birs_eval_label_exp_CONV;
val birs_exec_step_CONV_p2 = Profile.profile "exec_step_CONV_p2" birs_exec_step_CONV_p2;

val birs_exec_step_CONV_p3 =
  (* TODO: remove this patch later *)
   REWRITE_CONV [GSYM birs_gen_env_thm, GSYM birs_gen_env_NULL_thm];
val birs_exec_step_CONV_p3 = Profile.profile "exec_step_CONV_p3" birs_exec_step_CONV_p3;

val birs_exec_step_CONV_p4 =
  GEN_match_conv is_birs_eval_exp (birs_eval_exp_CONV) THENC
   REWRITE_CONV [birs_gen_env_GET_thm, birs_gen_env_GET_NULL_thm] THENC
   RESTR_EVAL_CONV [birs_update_env_tm, birs_gen_env_tm, bir_typing_expSyntax.type_of_bir_exp_tm] THENC
   GEN_match_conv (bir_typing_expSyntax.is_type_of_bir_exp) (type_of_bir_exp_DIRECT_CONV) THENC
   RESTR_EVAL_CONV [birs_update_env_tm, birs_gen_env_tm];
val birs_exec_step_CONV_p4 = Profile.profile "exec_step_CONV_p4" birs_exec_step_CONV_p4;

val birs_exec_step_CONV_p5 =
  (* TODO: here better only convert the subexpression birs_update_env *)
   REWRITE_CONV [birs_update_env_thm] THENC
   RESTR_EVAL_CONV [birs_gen_env_tm];
val birs_exec_step_CONV_p5 = Profile.profile "exec_step_CONV_p5" birs_exec_step_CONV_p5;
*)

val is_OPTION_BIND = (identical ``OPTION_BIND : bir_exp_t option -> (bir_exp_t -> bir_type_t option) -> bir_type_t option`` o fst o strip_comb);
val is_birs_update_env = (identical birs_update_env_tm o fst o strip_comb);

fun continue_eq_rule c = CONV_RULE (RAND_CONV c);
fun restr_conv_eq_rule consts c th =
  let
    val fix_th = continue_eq_rule (RESTR_EVAL_CONV consts) th;
  in
    continue_eq_rule c fix_th
  end;

(*
val test_term =
``birs_update_env
        ("MEM8",
         BExp_Store (BExp_Den (BVar "sy_MEM8" (BType_Mem Bit64 Bit8)))
           (BExp_Den (BVar "sy_x10" (BType_Imm Bit64))) BEnd_LittleEndian
           (BExp_Load (BExp_Den (BVar "sy_MEM8" (BType_Mem Bit64 Bit8)))
              (BExp_Den (BVar "sy_x11" (BType_Imm Bit64))) BEnd_LittleEndian
              Bit64))
        (birs_update_env
           ("x14",
            BExp_Load (BExp_Den (BVar "sy_MEM8" (BType_Mem Bit64 Bit8)))
              (BExp_Den (BVar "sy_x11" (BType_Imm Bit64))) BEnd_LittleEndian
              Bit64)
           (birs_update_env
              ("x15",
               BExp_Load (BExp_Den (BVar "sy_MEM8" (BType_Mem Bit64 Bit8)))
                 (BExp_Den (BVar "sy_x10" (BType_Imm Bit64)))
                 BEnd_LittleEndian Bit64)
              (birs_gen_env
                 [("x14",BExp_Den (BVar "sy_x14" (BType_Imm Bit64)));
                  ("MEM8",BExp_Den (BVar "sy_MEM8" (BType_Mem Bit64 Bit8)));
                  ("x11",BExp_Den (BVar "sy_x11" (BType_Imm Bit64)));
                  ("x15",BExp_Den (BVar "sy_x15" (BType_Imm Bit64)));
                  ("x10",BExp_Den (BVar "sy_x10" (BType_Imm Bit64)));
                  ("x1",BExp_Den (BVar "sy_x1" (BType_Imm Bit64)))])))``;
is_birs_update_env test_term;
*)

fun birs_exec_step_CONV_B (bprog_tm, (res_p1, env_tm, pcond_tm, eq_thms)) =
let
  (* evaluate to symbolic expression *)
  val res_b_eval_exp = (* restr_conv_eq_rule *)
   continue_eq_rule
    (GEN_match_conv is_birs_eval_exp (REWRITE_CONV eq_thms THENC (Profile.profile "exec_step_CONV_B_1_eval_exp_EECONV" birs_eval_exp_CONV)))
    (continue_eq_rule
      (Profile.profile "exec_step_CONV_B_1_eval_exp_PREEVAL" (RESTR_EVAL_CONV [birs_eval_exp_tm, birs_update_env_tm]))
      res_p1)
  ;

  (* lookup type of previous symbolic expression, if is assignment statement *)
  val res_b_option_bind = Profile.profile "exec_step_CONV_B_2_option_bind" (continue_eq_rule
    (GEN_match_conv is_OPTION_BIND (
      RATOR_CONV (RAND_CONV (REWRITE_CONV ([birs_gen_env_GET_thm, birs_gen_env_GET_NULL_thm]@eq_thms) THENC EVAL)) THENC
      REWRITE_CONV [optionTheory.OPTION_BIND_def] (* OPTION_BIND semantics *) THENC
      GEN_match_conv (bir_typing_expSyntax.is_type_of_bir_exp) (type_of_bir_exp_DIRECT_CONV)
    ))
    ) res_b_eval_exp;

  (* update symbolic environment, if is assignment statement *)
  val res_b_update_env = Profile.profile "exec_step_CONV_B_3_update_env" (restr_conv_eq_rule
    [birs_update_env_tm]
    (GEN_match_conv is_birs_update_env (
      (* (fn t => (print "UPDATE ENV HERE\n"; print_term t; REFL t)) THENC *)
      REWRITE_CONV ([birs_update_env_thm]@eq_thms) THENC
      RESTR_EVAL_CONV [birs_gen_env_tm]
    ))
    ) res_b_option_bind;


  val res = (abbr_rev (res_b_update_env, env_tm, pcond_tm));

(*
  val _ = print "\neval expression\n";
  val _ = (print_term o concl) res_b_eval_exp;
  val _ = print "\neval option_bind\n";
  val _ = (print_term o concl) res_b_option_bind;
  val _ = print "\neval update env\n";
  val _ = (print_term o concl) res_b_update_env;
  val _ = print "\nresult\n";
  val _ = (print_term o concl) res;
  val _ = raise ERR "" "";
*)

in
  res
end;
val birs_exec_step_CONV_B = Profile.profile "exec_step_CONV_B" birs_exec_step_CONV_B;




(*
val t = ``MEM (BL_Address (Imm64 0w)) (bir_labels_of_program bir_aes_prog)``;
val x = (snd o hd) label_mem_thms;
val t = concl x;
*)
val spec_conv_thm = (GSYM o GEN_ALL) (List.nth((CONJUNCTS o Q.SPEC `t`) boolTheory.EQ_CLAUSES,1));
fun MEM_proglabels_fun (t, eq_thms) =
  let
    val l_tm = (snd o dest_comb o fst o dest_comb) t;
    val mem_thm_o = !cur_l_mem_lookup_fun l_tm;
(*
    val _ = print_term t;
    val _ = print_term l_tm;
 *)
  fun fallback_fun t =
    (print "falling back to evaluating membership of prog labels"; EVAL t);
  in
    case mem_thm_o of
     NONE =>  fallback_fun t
   | SOME x => if (identical t o concl) x then EQ_MP (SPEC t spec_conv_thm) x else fallback_fun t
  end;
val MEM_proglabels_fun = Profile.profile "MEM_proglabels_fun" MEM_proglabels_fun;

val birs_exec_stmt_jmp_tm = ``birs_exec_stmt_jmp``;
val MEM_tm = ``MEM : bir_label_t -> bir_label_t list -> bool``;
fun birs_exec_step_CONV_E (bprog_tm, (res_p1, env_tm, pcond_tm, eq_thms)) =
let
  val res_e_eval_exp = restr_conv_eq_rule
    [bprog_tm, birs_exec_stmt_jmp_tm, birs_eval_exp_tm]
    (GEN_match_conv is_birs_eval_exp (REWRITE_CONV eq_thms THENC birs_eval_exp_CONV))
    res_p1;

  val res_e_eval_label = restr_conv_eq_rule
    [bprog_tm, birs_eval_label_exp_tm]
    (GEN_match_conv is_birs_eval_label_exp (REWRITE_CONV eq_thms THENC birs_eval_label_exp_CONV))
    res_e_eval_exp;
  
  val res_e_mem_proglabels = restr_conv_eq_rule
    [bprog_tm, MEM_tm]
    (GEN_match_conv listSyntax.is_mem (fn t => MEM_proglabels_fun (t, eq_thms)))
    res_e_eval_label;

  val res_e_finish = continue_eq_rule
    EVAL
    res_e_mem_proglabels;

(*
  val _ = print_thm res_e_eval_label;
  val _ = raise ERR "" "";
*)

  val res = (abbr_rev (res_e_finish, env_tm, pcond_tm));
in
  res
end;
val birs_exec_step_CONV_E = Profile.profile "exec_step_CONV_E" birs_exec_step_CONV_E;

val birs_exec_step_CONV =
  measure_fun "\n>>>>>>>> step_CONV in " (fn t =>
  let
    val bprog_tm =
      (measure_fun "\n>>>>>>>>>> step_CONV_pre in " birs_exec_step_CONV_pre t);
    val (res_p1, env_tm, pcond_tm, eq_thms) =
      (measure_fun "\n>>>>>>>>>> step_CONV_p1 in " birs_exec_step_CONV_p1 (bprog_tm, t));
  (*val _ = (print "P1: GET STATEMENT\n"; print_thm res_p1);*)
    val stmt_tm = (snd o dest_comb o fst o dest_comb o snd o dest_eq o concl) res_p1;
  (*val _ = print_term stmt_tm;
    val stmt_type_tm = (fst o dest_comb) stmt_tm;
    val _ = print_term stmt_type_tm;*)
  in
  (
       if bir_programSyntax.is_BStmtB stmt_tm then
         birs_exec_step_CONV_B (bprog_tm, (res_p1, env_tm, pcond_tm, eq_thms))
       else if bir_programSyntax.is_BStmtE stmt_tm then
         birs_exec_step_CONV_E (bprog_tm, (res_p1, env_tm, pcond_tm, eq_thms))
       else
         raise ERR "birs_exec_step_CONV" "something is wrong, should be BStmtB or BStmtE here"
  )
  end
 );
val birs_exec_step_CONV = Profile.profile "exec_step_CONV" birs_exec_step_CONV;


(*

val test_term_birs_eval_exp = ``
          birs_eval_exp
            (BExp_BinPred BIExp_LessOrEqual
               (BExp_Den (BVar "countw" (BType_Imm Bit64)))
               (BExp_Const (Imm64 0xFFFFFFFFFFFFFFFEw)))
            (K NONE)⦇
              "R7" ↦ SOME (BExp_Den (BVar "sy_R7" (BType_Imm Bit32)));
              "SP_process" ↦
                SOME (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)));
              "countw" ↦ SOME (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
            ⦈
``;


val test_term_birs_eval_exp_subst = ``
          birs_eval_exp_subst
            (BExp_BinPred BIExp_LessOrEqual
               (BExp_Den (BVar "countw" (BType_Imm Bit64)))
               (BExp_Const (Imm64 0xFFFFFFFFFFFFFFFEw)))
            (K NONE)⦇
              "R7" ↦ SOME (BExp_Den (BVar "sy_R7" (BType_Imm Bit32)));
              "SP_process" ↦
                SOME (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)));
              "countw" ↦ SOME (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
            ⦈
``;


val test_term_birs_senv_typecheck = ``
          birs_senv_typecheck
            (BExp_BinPred BIExp_LessOrEqual
               (BExp_Den (BVar "countw" (BType_Imm Bit64)))
               (BExp_Const (Imm64 0xFFFFFFFFFFFFFFFEw)))
            (K NONE)⦇
              "R7" ↦ SOME (BExp_Den (BVar "sy_R7" (BType_Imm Bit32)));
              "SP_process" ↦
                SOME (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)));
              "countw" ↦ SOME (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
            ⦈
``;


*)

in

val birs_eval_exp_CONV = birs_eval_exp_CONV;


(* helpers to check if sound structure terms (and subterms) are in normalform *)
(* ----------------------------------------------- *)
  local

    fun is_bsst_pc_fupd tm =
      is_comb tm andalso
      (identical ``bsst_pc_fupd`` o fst o dest_comb) tm;
    fun is_bsst_environ_fupd tm =
      is_comb tm andalso
      (identical ``bsst_environ_fupd`` o fst o dest_comb) tm;
    fun is_bsst_status_fupd tm =
      is_comb tm andalso
      (identical ``bsst_status_fupd`` o fst o dest_comb) tm;
    fun is_bsst_pcond_fupd tm =
      is_comb tm andalso
      (identical ``bsst_pcond_fupd`` o fst o dest_comb) tm;

  in

    fun birs_state_is_normform tm =
      is_comb tm andalso
      ((is_bsst_pc_fupd o fst o dest_comb) tm orelse
       (is_bsst_environ_fupd o fst o dest_comb) tm orelse
       (is_bsst_status_fupd o fst o dest_comb) tm orelse
       (is_bsst_pcond_fupd o fst o dest_comb) tm);

    fun is_a_normform_set tm =
      (pred_setSyntax.strip_set tm; true)
      handle _ => false;

    fun birs_states_are_normform tm =
      is_a_normform_set tm andalso
      (List.all birs_state_is_normform o pred_setSyntax.strip_set) tm;


    fun birs_state_is_normform_CONV sfun bstate_tm =
      (if (birs_state_is_normform) bstate_tm then () else
            (print_term bstate_tm;
             raise ERR (sfun^"::birs_state_is_normform_CONV") "something is not right, the input state is not as expected");
       REFL bstate_tm);

    fun birs_states_are_normform_CONV sfun bstates_tm =
      (if (birs_states_are_normform) bstates_tm then () else
            (print_term bstates_tm;
             raise ERR (sfun^"::birs_states_are_normform_CONV") "something is not right, the produced theorem is not evaluated enough");
       REFL bstates_tm);

    fun birs_states_are_normform_CONV_with_start sfun bstate_tm bstates_tm =
        birs_states_are_normform_CONV sfun bstates_tm
	handle e => (print "\n[[[[\n"; print_term bstate_tm; print "\n]]]]\n"; raise e);

(*
val THE_NONE_tm = ``(THE NONE) : ``;
    fun is_THE_NONE tm =
      aconv tm THE_NONE_tm;
*)
    fun contains_THE_NONE tm =
      String.isSubstring "THE NONE" (term_to_string tm);
(*
(GEN_match_conv is_THE_NONE REFL tm; true) handle _ => false;
contains_THE_NONE freesymbols_tm
(is_birs_exec_step)
(fn bstate_tm
*)
    fun contains_THE_NONE_CONV_with_extra sfun extra_tm tm =
      if contains_THE_NONE tm then (
        print "\n[[[[\n"; print_term extra_tm; print "\n]]]]\n";
        print "\n[[[[\n"; print_term tm; print "\n]]]]\n";
        raise ERR (sfun^"::contains_THE_NONE_CONV_with_extra") "something is not right, there is THE NONE in the term"
      ) else
	REFL tm;

  end;

(* extract information from a sound structure *)
(* ----------------------------------------------- *)
fun symb_sound_struct_get_sysLPi_fun tm =
  let
    val sysLPi_tm =
      case (strip_comb) tm of
         (_,[_,tm]) => tm
       | _ => raise Fail "symb_sound_struct_get_sysLPi_fun::unexpected term1";
    val res =
      case pairSyntax.strip_pair sysLPi_tm of
         [sys_tm, L_tm, Pi_tm] => (sys_tm, L_tm, Pi_tm)
       | _ => raise Fail "symb_sound_struct_get_sysLPi_fun::unexpected term2";
  in
    res
  end;

(* check if sound structure term is in normalform *)
(* ----------------------------------------------- *)
fun symb_sound_struct_is_normform tm =
  let
    val (sys, L, Pi) = symb_sound_struct_get_sysLPi_fun tm
                       handle _ => raise Fail "symb_sound_struct_is_normform::unexpected term1";

    (*
    val bir_state_init = ``<|bsst_pc := <|bpc_label := BL_Address (Imm32 2824w); bpc_index := 0|>;
      bsst_environ := bir_senv_GEN_list birenvtyl;
      bsst_status := BST_Running;
      bsst_pcond :=
        BExp_BinExp BIExp_And
          (BExp_BinExp BIExp_And
             (BExp_BinPred BIExp_LessOrEqual (BExp_Const (Imm64 0xFFFFFFw))
                (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32))))
             (BExp_Aligned Bit32 2
                (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)))))
          (BExp_BinPred BIExp_LessOrEqual
             (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
             (BExp_Const (Imm64 0xFFFFFFFFFFFFFF00w)))|>``;
    is_bsst_pc_fupd bir_state_init
    birs_state_is_ok bir_state_init
    *)

    val sys_ok =
      is_comb sys andalso
      (identical ``birs_symb_to_symbst`` o fst o dest_comb) sys andalso
      (birs_state_is_normform o snd o dest_comb) sys;

    val L_ok = is_a_normform_set L;

    val Pi_ok =
      is_comb Pi andalso
      (identical ``IMAGE birs_symb_to_symbst`` o fst o dest_comb) Pi andalso
      (birs_states_are_normform o snd o dest_comb) Pi;
  in
    sys_ok andalso L_ok andalso Pi_ok
  end;


(* bir symbolic execution steps *)
(* ----------------------------------------------- *)
(*
val bstate_tm = ``
  <|bsst_pc := <|bpc_label := BL_Address (Imm32 2826w); bpc_index := 1|>;
    bsst_environ :=
      birs_gen_env
        [("SP_process",
          BExp_BinExp BIExp_Minus
            (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)))
            (BExp_Const (Imm32 8w)));
         ("MEM",
          BExp_Store
            (BExp_Store (BExp_Den (BVar "sy_MEM" (BType_Mem Bit32 Bit8)))
               (BExp_BinExp BIExp_Minus
                  (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)))
                  (BExp_Const (Imm32 8w))) BEnd_LittleEndian
               (BExp_Den (BVar "sy_R7" (BType_Imm Bit32))))
            (BExp_BinExp BIExp_Minus
               (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)))
               (BExp_Const (Imm32 4w))) BEnd_LittleEndian
            (BExp_Den (BVar "sy_LR" (BType_Imm Bit32))));
         ("countw",
          BExp_BinExp BIExp_Plus
            (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
            (BExp_Const (Imm64 3w)));
         ("tmp_SP_process",
          BExp_BinExp BIExp_Minus
            (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)))
            (BExp_Const (Imm32 8w)));
         ("PSR_C",BExp_Den (BVar "sy_PSR_C" (BType_Imm Bit1)));
         ("PSR_N",BExp_Den (BVar "sy_PSR_N" (BType_Imm Bit1)));
         ("PSR_V",BExp_Den (BVar "sy_PSR_V" (BType_Imm Bit1)));
         ("PSR_Z",BExp_Den (BVar "sy_PSR_Z" (BType_Imm Bit1)));
         ("R0",BExp_Den (BVar "sy_R0" (BType_Imm Bit32)));
         ("R1",BExp_Den (BVar "sy_R1" (BType_Imm Bit32)));
         ("R2",BExp_Den (BVar "sy_R2" (BType_Imm Bit32)));
         ("R3",BExp_Den (BVar "sy_R3" (BType_Imm Bit32)));
         ("R4",BExp_Den (BVar "sy_R4" (BType_Imm Bit32)));
         ("R5",BExp_Den (BVar "sy_R5" (BType_Imm Bit32)));
         ("R6",BExp_Den (BVar "sy_R6" (BType_Imm Bit32)));
         ("R7",BExp_Den (BVar "sy_R7" (BType_Imm Bit32)));
         ("R8",BExp_Den (BVar "sy_R8" (BType_Imm Bit32)));
         ("R9",BExp_Den (BVar "sy_R9" (BType_Imm Bit32)));
         ("R10",BExp_Den (BVar "sy_R10" (BType_Imm Bit32)));
         ("R11",BExp_Den (BVar "sy_R11" (BType_Imm Bit32)));
         ("R12",BExp_Den (BVar "sy_R12" (BType_Imm Bit32)));
         ("LR",BExp_Den (BVar "sy_LR" (BType_Imm Bit32)));
         ("SP_main",BExp_Den (BVar "sy_SP_main" (BType_Imm Bit32)));
         ("ModeHandler",BExp_Den (BVar "sy_ModeHandler" (BType_Imm Bit1)));
         ("tmp_PC",BExp_Den (BVar "sy_tmp_PC" (BType_Imm Bit32)));
         ("tmp_COND",BExp_Den (BVar "sy_tmp_COND" (BType_Imm Bit1)));
         ("tmp_MEM",BExp_Den (BVar "sy_tmp_MEM" (BType_Mem Bit32 Bit8)));
         ("tmp_PSR_C",BExp_Den (BVar "sy_tmp_PSR_C" (BType_Imm Bit1)));
         ("tmp_PSR_N",BExp_Den (BVar "sy_tmp_PSR_N" (BType_Imm Bit1)));
         ("tmp_PSR_V",BExp_Den (BVar "sy_tmp_PSR_V" (BType_Imm Bit1)));
         ("tmp_PSR_Z",BExp_Den (BVar "sy_tmp_PSR_Z" (BType_Imm Bit1)));
         ("tmp_R0",BExp_Den (BVar "sy_tmp_R0" (BType_Imm Bit32)));
         ("tmp_R1",BExp_Den (BVar "sy_tmp_R1" (BType_Imm Bit32)));
         ("tmp_R2",BExp_Den (BVar "sy_tmp_R2" (BType_Imm Bit32)));
         ("tmp_R3",BExp_Den (BVar "sy_tmp_R3" (BType_Imm Bit32)));
         ("tmp_R4",BExp_Den (BVar "sy_tmp_R4" (BType_Imm Bit32)));
         ("tmp_R5",BExp_Den (BVar "sy_tmp_R5" (BType_Imm Bit32)));
         ("tmp_R6",BExp_Den (BVar "sy_tmp_R6" (BType_Imm Bit32)));
         ("tmp_R7",BExp_Den (BVar "sy_tmp_R7" (BType_Imm Bit32)));
         ("tmp_R8",BExp_Den (BVar "sy_tmp_R8" (BType_Imm Bit32)));
         ("tmp_R9",BExp_Den (BVar "sy_tmp_R9" (BType_Imm Bit32)));
         ("tmp_R10",BExp_Den (BVar "sy_tmp_R10" (BType_Imm Bit32)));
         ("tmp_R11",BExp_Den (BVar "sy_tmp_R11" (BType_Imm Bit32)));
         ("tmp_R12",BExp_Den (BVar "sy_tmp_R12" (BType_Imm Bit32)));
         ("tmp_LR",BExp_Den (BVar "sy_tmp_LR" (BType_Imm Bit32)));
         ("tmp_SP_main",BExp_Den (BVar "sy_tmp_SP_main" (BType_Imm Bit32)));
         ("tmp_ModeHandler",
          BExp_Den (BVar "sy_tmp_ModeHandler" (BType_Imm Bit1)));
         ("tmp_countw",BExp_Den (BVar "sy_tmp_countw" (BType_Imm Bit64)))];
    bsst_status := BST_Running;
    bsst_pcond :=
      BExp_BinExp BIExp_And
        (BExp_BinExp BIExp_And
           (BExp_BinPred BIExp_LessOrEqual (BExp_Const (Imm32 0xFFFFFFw))
              (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32))))
           (BExp_BinPred BIExp_Equal
              (BExp_BinExp BIExp_And
                 (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit32)))
                 (BExp_Const (Imm32 3w))) (BExp_Const (Imm32 0w))))
        (BExp_BinPred BIExp_LessOrEqual
           (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
           (BExp_Const (Imm64 0xFFFFFFFFFFFFFF00w)))|>
``;
*)
(*
val bstate_tm = birs_state_init;
val bstate_tm = birs_state_mid;

val bstate_tm = birs_state_init_tm;
val bprog_tm = bprog_tm;

val tm = ``ABCD (birs_exec_step ^bprog_tm ^bstate_tm)``;
val tm = ``birs_exec_step ^bprog_tm ^bstate_tm``;
*)
val birs_exec_step_tm = ``birs_exec_step``;
fun is_birs_exec_step tm =
  is_comb tm andalso
  (is_comb o fst o dest_comb) tm andalso
  (same_const birs_exec_step_tm o fst o dest_comb o fst o dest_comb) tm;
fun birs_exec_step_CONV_fun tm =
  GEN_match_conv
(is_birs_exec_step)
(fn bstate_tm => (
  RAND_CONV (birs_state_is_normform_CONV "birs_exec_step_CONV_fun") THENC

  (fn tm_i =>
    let
      val timer_exec_step = bir_miscLib.timer_start 0;
      (* TODO: optimize *)
      val birs_exec_thm = birs_exec_step_CONV tm_i;
      val _ = bir_miscLib.timer_stop (fn delta_s => print ("\n>>>>>> executed step in " ^ delta_s ^ "\n")) timer_exec_step;
    in
      birs_exec_thm
    end) THENC

  birs_states_are_normform_CONV_with_start "birs_exec_step_CONV_fun" bstate_tm
  (* THENC contains_THE_NONE_CONV_with_extra "birs_exec_step_CONV_fun" bstate_tm *)
  ) bstate_tm
)
tm;


(* halt free programs *)
(* ----------------------------------------------- *)
(*
val bprog_tm = bprog;
*)
fun bir_prog_has_no_halt_fun bprog_tm =
  let
    (* prep step rule to be used *)
    (*
    val bir_prog_has_no_halt_prog_thm = store_thm(
       "bir_prog_has_no_halt_prog_thm", *)
    val bir_prog_has_no_halt_prog_thm = prove(``
      bir_prog_has_no_halt ^bprog_tm
    ``,
      EVAL_TAC
    );
  in
    bir_prog_has_no_halt_prog_thm
  end;

(*
val bprog_tm = bprog;
val no_halt_thm = (bir_prog_has_no_halt_fun bprog_tm)
*)
fun birs_rule_STEP_prog_fun no_halt_thm =
  let
    val prep_thm = 
      MATCH_MP birs_rulesTheory.birs_rule_STEP_gen2_thm no_halt_thm;
(*
    val _ = (print_term o concl) prep_thm;
*)
  in
    prep_thm
  end;


(* plugging in the execution of steps to obtain sound structure *)
(* ----------------------------------------------- *)
local
  val birs_state_ss = rewrites (type_rws ``:birs_state_t``);
  open birs_auxTheory;
in
fun birs_rule_STEP_fun birs_rule_STEP_thm bstate_tm =
  let

    val birs_exec_thm = CONV_RULE (birs_exec_step_CONV_fun) (SPEC bstate_tm birs_rule_STEP_thm);

    val timer_exec_step_p3 = bir_miscLib.timer_start 0;
    (* TODO: optimize *)
    val single_step_prog_thm =
      REWRITE_RULE
        [bir_symbTheory.recordtype_birs_state_t_seldef_bsst_pc_def,
         bir_symbTheory.birs_state_t_accfupds, combinTheory.K_THM]
        birs_exec_thm;

    val _ = bir_miscLib.timer_stop (fn delta_s => print ("\n>>>>>> STEP in " ^ delta_s ^ "\n")) timer_exec_step_p3;

    val _ = if symb_sound_struct_is_normform (concl single_step_prog_thm) then () else
            (print_term (concl single_step_prog_thm);
             raise ERR "birs_rule_STEP_fun" "something is not right, the produced theorem is not evaluated enough");
  in
    single_step_prog_thm
  end;
end;



(*
val Pi_tm = Pi_A_tm;
*)
fun symb_sound_struct_Pi_to_birstatelist_fun Pi_tm =
  (pred_setSyntax.strip_set o snd o dest_comb) Pi_tm;


(* TODO: justify the second branch of assert is infeasible (need precondition for this) *)
(* TODO: simplify path condition in poststate to get rid of the implied and not accumulate it *)
(* TODO: clean up environment after assignment to not accumulate useless mappings *)
(* TODO: maybe have a specialized assert/assignment step function? (optimization to detect this situation directly, maybe better as separate function?) *)

(*
val pcond_tm = ``
               BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_Den (BVar "countw" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 0xFFFFFFFFFFFFFF00w)))
                 (BExp_UnaryExp BIExp_Not
                    (BExp_BinPred BIExp_LessOrEqual
                       (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 0xFFFFFFFFFFFFFFFEw))))
``;
*)

(* stepping a sound structure, try to justify assert *)
(* ----------------------------------------------- *)
(*
val bstate_tm = birs_state_init_tm;
*)
local
  val birs_state_ss = rewrites (type_rws ``:birs_state_t``);
  open birs_auxTheory;

  open birs_rulesTheory;

  open birs_smtLib;

  fun justify_assumption_EVAL t =
    if (not o is_imp o concl) t then
      raise ERR "justify_assumption_EVAL" "not an implication"
    else
      let
        val assmpt = (fst o dest_imp o concl) t;
        val assmpt_thm = (EVAL) assmpt;

        val assmpt_new = (snd o dest_eq o concl) assmpt_thm;

        (* raise exception when the assumption turns out to be false *)
        val _ = if not (identical assmpt_new F) then () else
                raise ERR "justify_assumption_EVAL" "assumption does not hold";

        val _ = if identical assmpt_new T then () else
                raise ERR "justify_assumption_EVAL" ("failed to fix the assumption: " ^ (term_to_string assmpt));
      in
        (REWRITE_RULE [assmpt_thm] t)
      end;

  val birs_pcondinf_tm = ``birs_pcondinf``;
in
fun birs_rule_tryjustassert_fun force_assert_justify single_step_prog_thm =
  let
    (*
    val single_step_prog_thm = birs_rule_STEP_fun birs_rule_STEP_thm bprog_tm bstate_tm;
    *)
    val continue_thm_o_1 =
      SOME (MATCH_MP assert_spec_thm single_step_prog_thm)
      handle _ => NONE;
    val continue_thm_o_2 =
      Option.map (justify_assumption_EVAL) continue_thm_o_1
      handle _ => NONE;
  in
    (* val SOME continue_thm = continue_thm_o; *)
    case continue_thm_o_2 of
       SOME continue_thm =>
        let
    val timer_exec_step_p3 = bir_miscLib.timer_start 0;
          val pcond_tm = (snd o dest_comb o snd o dest_comb o fst o dest_comb o concl) continue_thm;
          (*val _ = print_term pcond_tm;*)
          val pcond_is_contr = bir_check_unsat false pcond_tm;
          val _ = if (not force_assert_justify) orelse pcond_is_contr then () else
            (print "\n\n\n<<<<<<<<<<<< ASSERTION MAY FAIL <<<<<<<<<<<< \n";
             print_term (concl single_step_prog_thm);
             print ">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>\n\n";
             raise ERR "birs_rule_tryjustassert_fun" "can't prove assertion to hold");
          val pcond_thm_o =
            if pcond_is_contr then
              SOME (mk_oracle_thm "BIRS_CONTR_Z3" ([], mk_comb (birs_pcondinf_tm, pcond_tm)))
            else
              NONE;
    val _ = bir_miscLib.timer_stop (fn delta_s => print ("\n>>>>>> tryassert in " ^ delta_s ^ "\n")) timer_exec_step_p3;
        in
          (* val SOME pcond_thm = pcond_thm_o; *)
          case pcond_thm_o of
             SOME pcond_thm => MP continue_thm pcond_thm
           | _ => single_step_prog_thm
        end
     | _ => single_step_prog_thm
  end;
fun birs_rule_tryprune_fun prune_thm single_step_prog_thm =
  let
    (* val _ = print "try prune now \n"; *)
    val continue_thm_o_1 =
      SOME (MATCH_MP prune_thm single_step_prog_thm)
      handle _ => NONE;
    val continue_thm_o_2 =
      Option.map (fn t => (print "going into pruning\n"; (*print_thm t; *)justify_assumption_EVAL t)) continue_thm_o_1
      handle _ => NONE;
  in
    case continue_thm_o_2 of
       SOME continue_thm =>
        let
    val timer_exec_step_p3 = bir_miscLib.timer_start 0;
          val pcond_tm = (snd o dest_comb o snd o dest_comb o fst o dest_comb o concl) continue_thm;
          (* val _ = print_term pcond_tm; *)
          val pcond_is_contr = bir_check_unsat false pcond_tm;
	  val _ = if pcond_is_contr then print "can prune" else ();
          val pcond_thm_o =
            if pcond_is_contr then
              SOME (mk_oracle_thm "BIRS_CONTR_Z3" ([], mk_comb (birs_pcondinf_tm, pcond_tm)))
            else
              NONE;
    val _ = bir_miscLib.timer_stop (fn delta_s => print ("\n>>>>>> tryprune2 in " ^ delta_s ^ "\n")) timer_exec_step_p3;
        in
          case pcond_thm_o of
             SOME pcond_thm =>
	     let
               val res = MP continue_thm pcond_thm;
               val _ = print "pruning finished\n";
               (*val _ = print_thm res;*)
	     in
	       res
	     end
           | _ => single_step_prog_thm
        end
     | _ => single_step_prog_thm
  end;
end;


(* stepping a sound structure, try to simplify after assignment *)
(* ----------------------------------------------- *)
(* first prepare the SUBST rule for prog *)
fun birs_rule_SUBST_prog_fun bprog_tm =
  let
    open birs_rulesTheory;
    val prog_type = (hd o snd o dest_type o type_of) bprog_tm;
    (*
    val symbols_f_sound_thm = INST_TYPE [Type.alpha |-> prog_type] bir_symb_soundTheory.birs_symb_symbols_f_sound_thm;
    val birs_symb_symbols_f_sound_prog_thm =
      (SPEC (bprog_tm) symbols_f_sound_thm);
    val ARB_val_sound_thm = INST_TYPE [Type.alpha |-> prog_type] bir_symb_soundTheory.birs_symb_ARB_val_sound_thm;
    val birs_symb_ARB_val_sound_prog_thm =
      (SPEC (bprog_tm) ARB_val_sound_thm);

    val prep_thm =
      MATCH_MP
        (MATCH_MP symb_rule_SUBST_SING_thm birs_symb_symbols_f_sound_prog_thm)
        birs_symb_ARB_val_sound_prog_thm;

    val inst_thm = prove(``
         !sys L lbl envl status pcond vn symbexp symbexp'.
           symb_hl_step_in_L_sound (bir_symb_rec_sbir ^bprog_tm) (sys,L,IMAGE birs_symb_to_symbst {
             <|bsst_pc := lbl;
               bsst_environ := birs_gen_env ((vn, symbexp)::envl);
               bsst_status := status;
               bsst_pcond := pcond|>}) ==>
           birs_simplification pcond symbexp symbexp' ==>
           symb_hl_step_in_L_sound (bir_symb_rec_sbir ^bprog_tm) (sys,L,IMAGE birs_symb_to_symbst {
             <|bsst_pc := lbl;
               bsst_environ := birs_gen_env ((vn, symbexp')::envl);
               bsst_status := status;
               bsst_pcond := pcond|>})
      ``,
        cheat (* TODO: connect this with prep_thm from above *)
      );*)
    val inst_thm = SIMP_RULE std_ss [] ((SPEC bprog_tm o INST_TYPE [Type.alpha |-> prog_type]) birs_rule_SUBST_spec_thm);
    (*val _ = (print_term o concl) inst_thm;*)
  in
    inst_thm
  end;


(*
val single_step_prog_thm = result;
*)
fun birs_rule_SUBST_trysimp_fun birs_rule_SUBST_thm single_step_prog_thm =
  let
    val assignment_thm_o =
      SOME (MATCH_MP birs_rule_SUBST_thm single_step_prog_thm)
      handle _ => NONE;

    val simp_t_o = Option.mapPartial (fn assignment_thm =>
      let
        val simp_tm = (fst o dest_imp o (*snd o strip_binder (SOME boolSyntax.universal) o*) concl o Q.SPEC `symbexp'`) assignment_thm;

    val timer_exec_step_p3 = bir_miscLib.timer_start 0;
        val simp_t = birs_simpLib.birs_simp_repeat simp_tm;
        (* TODO: need to remove the following line later and enable the simp function above *)
        (*val simp_t_o = NONE;*)
    val _ = bir_miscLib.timer_stop (fn delta_s => print ("\n>>>>>> SUBST in " ^ delta_s ^ "\n")) timer_exec_step_p3;
      in
        SOME (simp_t, assignment_thm)
      end) assignment_thm_o;
  in
    case simp_t_o of
       SOME (simp_t, assignment_thm) => MATCH_MP assignment_thm simp_t
     | NONE => single_step_prog_thm
  end;


end (* local *)

end (* struct *)
