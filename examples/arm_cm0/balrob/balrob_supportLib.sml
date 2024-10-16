structure balrob_supportLib =
struct

local

  open HolKernel Parse boolLib bossLib;

  open birsSyntax;

  open birs_utilsLib;

  (* error handling *)
  val libname = "balrob_supportLib"
  val ERR = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname

in (* local *)

  val bir_countw_bvar_tm = ``BExp_Den (BVar "countw" (BType_Imm Bit64))``;
  val bir_sp_bvar_tm = ``BExp_Den (BVar "SP_process" (BType_Imm Bit32))``;

  fun bir_const64 v = ``BExp_Const (Imm64 ^(wordsSyntax.mk_wordii(v, 64)))``;
  fun bir_const32 v = ``BExp_Const (Imm32 ^(wordsSyntax.mk_wordii(v, 32)))``;
  fun mk_countw_plus tm v = bslSyntax.bplus (tm, bir_const64 v);

  val bir_countw_hvar_tm = ``BExp_Const (Imm64 pre_countw)``;
  val bir_hvar_cond = bslSyntax.beq (bir_countw_bvar_tm, bir_countw_hvar_tm);

(* -------------------------------------------------------------------------- *)
val configs          = [("balrob",
                           ("balrob.elf.da", "balrob/balrob.elf.da.plus", "balrob/balrob.elf.mem"),
                           "balrob_program_THM",
                           ((Arbnum.fromInt 0x00000000, Arbnum.fromInt 0x10001c54),
                            (Arbnum.fromInt 0x10001c54, Arbnum.fromInt (0x0000001c + 0x338 - 0x80 - 0x10)),
                            (Arbnum.fromInt (0x10001ff0 - 0x48 - 0x80 - 0x10), Arbnum.fromInt (0x00000010 + 0x48 + 0x80 + 0x10))),
((Arbnum.fromInt 0), (Arbnum.fromInt 0x10001c54)),
[
    "imu_handler_pid_entry",
    "atan2f_own",
    "abs_own",
    "__aeabi_f2iz",
    "__aeabi_fmul",
    "__aeabi_i2f",
    "__aeabi_fadd",
    "__aeabi_fcmplt",
    "__aeabi_fsub",
    "__aeabi_fdiv",
    "__lesf2",
    "__clzsi2"
  ]
                        ),
                        ("balrob_otherbenchs",
                           ("balrob_otherbenchs.elf.da", "balrob/balrob_otherbenchs.elf.da.plus", "balrob/balrob_otherbenchs.elf.mem"),
                           "balrob_otherbenchs_program_THM",
                           ((Arbnum.fromInt 0x00000000, Arbnum.fromInt 0x10001574),
                            (Arbnum.fromInt 0x10001574, Arbnum.fromInt (0x0000001c + 0x338)),
                            (Arbnum.fromInt (0x10001574 + 0x1c + 0x338), Arbnum.fromInt (0x10002000 - (0x10001574 + 0x1c + 0x338)))),
((Arbnum.fromInt 0), (Arbnum.fromInt 0x10001574)),
[
    "_mymodexp",
    "l6",
    "l10",
    "l12",
    "__aeabi_uidivmod",
    "__udivsi3",
    "__aeabi_idiv0"
]
                        )];

  val (prog_id, (da_file_lift, da_file_mem, mem_file), thm_name, (mem_region_const, mem_region_data, mem_region_stack), prog_range, symbs_sec_text) = List.nth(configs,0);

(* -------------------------------------------------------------------------- *)

  (* TODO: how much space do we actually have? we should "enforce" this with the linker... *)
  val mem_ram_start = 0x10000000;
  val mem_ram_size  = 0x2000;

  val (mem_region_const_start, mem_region_const_sz) = mem_region_const;
  val (mem_region_data_start,  mem_region_data_sz)  = mem_region_data;
  val (mem_region_stack_start, mem_region_stack_sz) = mem_region_stack;

  (*
  val stack_size  = 0x100;
  val stack_start = mem_ram_start + mem_ram_size -16;
  val stack_end   = stack_start - stack_size;
  *)
  val stack_start = mem_ram_start + mem_ram_size - 16;
  val stack_end   = mem_ram_start + mem_ram_size - (Arbnum.toInt mem_region_stack_sz);

  (* TODO: need to fix this to handlermode -> needs change of the used lifter machine *)
  val pred_not_handlermode =
  ``BExp_UnaryExp BIExp_Not (BExp_Den (BVar "ModeHandler" BType_Bool))``;

  val pred_sp_aligned =
  ``BExp_BinPred BIExp_Equal
      (BExp_BinExp BIExp_And
          (^bir_sp_bvar_tm)
          (BExp_Const (Imm32 3w)))
      (BExp_Const (Imm32 0w))``;

  fun pred_sp_space_req stack_space_req =
  ``BExp_BinExp BIExp_And
            (BExp_BinPred BIExp_LessThan
               ^(bir_const32 (stack_end + stack_space_req))
               ^bir_sp_bvar_tm)
            (BExp_BinPred BIExp_LessOrEqual
               ^bir_sp_bvar_tm
               ^(bir_const32 stack_start))``;

  fun pred_countw_space_req countw_space_req =
  ``BExp_BinPred BIExp_LessOrEqual
       ^bir_countw_bvar_tm
       ^(bir_const64 (0x10000000 - countw_space_req))``;

  fun pred_conjs (stack_space_req, countw_space_req) =
    [pred_not_handlermode]@ (* needed for bx lr statements *)
    (if stack_space_req = 0 then [] else
       [pred_sp_aligned,
        pred_sp_space_req stack_space_req])@
    [pred_countw_space_req countw_space_req];

  val _ = if Arbnum.fromInt 0 = mem_region_const_start then () else raise Fail "memory layout error";
  val _ = if mem_region_data_start = Arbnum.+ (mem_region_const_start, mem_region_const_sz) then () else raise Fail "memory layout error";
  val _ = if mem_region_stack_start = Arbnum.+ (mem_region_data_start, mem_region_data_sz) then () else raise Fail "memory layout error";
  val _ = if Arbnum.+ (mem_region_stack_start, mem_region_stack_sz) = Arbnum.fromInt (mem_ram_start + mem_ram_size) then () else raise Fail "memory layout error";

  (*
  val mem_sz_const = mem_ram_start;
  val mem_sz_globl = mem_region_data_sz;
  val mem_sz_stack = mem_ram_size - mem_sz_globl;
  *)
  val mem_sz_const = Arbnum.toInt mem_region_const_sz;
  val mem_sz_globl = Arbnum.toInt mem_region_data_sz;
  val mem_sz_stack = Arbnum.toInt mem_region_stack_sz;

  val _ = if mem_sz_stack > 0 then () else
          raise Fail "mem_sz_stack should be greater than 0";

(* -------------------------------------------------------------------------- *)

  (* TODO: integrate the start and end labels and also all subfragments here as well *)
  fun get_fun_usage entry_name =
    case entry_name of
       "__lesf2"
        => (12, 49)
     | "__clzsi2"
        => (0, 21)
     | "__aeabi_f2iz"
        => (0, 27)
     | "timer_read"
        => (8, 10)
     | "__aeabi_fadd"
        => (32, 168)
     | "__aeabi_fdiv"
        => (40, 581)
     | "__aeabi_i2f"
        => (16, 89)
     | "__aeabi_fcmplt"
        => (20, 68)
     | "abs_own"
        => (36, 101)
     | "__aeabi_fmul"
        => (44, 244)
     | "__aeabi_fsub"
        => (32, 187)
     | "motor_prep_input"
        => (20, 47)
     | "motor_set_l"
        => (44, 113)
     | "motor_set_r"
        => (44, 113)
     | "motor_set"
        => (60, 264)
     | "motor_set_f"
        => (84, 885)
     | "atan2f_own"
        => (92, 2038)
     | "imu_handler_pid_entry"
        => (204, 8312)

     | "_mymodexp"
        => (100, 0x10000)
     | "__aeabi_uidivmod"
        => (50, 0x800)

     | _ => raise Fail "get_fun_usage: don't know function";

(* -------------------------------------------------------------------------- *)

val birs_prog_config = ((fst o dest_eq o concl) balrobLib.bir_balrob_prog_def, balrobLib.balrob_birenvtyl_def);

  local
    open bir_programSyntax;
    open optionSyntax;
    fun is_SOME_BStmtB_BStmt_Assign t = is_some t andalso (is_BStmtB o dest_some) t andalso (is_BStmt_Assign o dest_BStmtB o dest_some) t;
  in
    fun apply_if_assign tm f =
      if is_SOME_BStmtB_BStmt_Assign tm then
        f
      else
        I;
    fun apply_if_branch f t =
      let
        val Pi_len = (get_birs_Pi_length o concl) t;
      in
        if Pi_len > 1 then
          f t
        else
          t
      end;
  end

(* -------------------------------------------------------------------------- *)

(*
fun debug_Pi_fun t =
  let
      val _ = if (symb_sound_struct_is_normform o concl) t then () else
              raise ERR "debug_Pi_fun" "theorem is not a standard birs_symb_exec";
    open birs_utilsLib;
    open bir_expSyntax;
    val Pis = (pred_setSyntax.strip_set o get_birs_Pi o concl) t;
    fun find_env_exp varname mappings =
     let
      val is_m_for_varname = (fn x => x = varname) o stringSyntax.fromHOLstring o fst;
      fun get_exp_if m =
        if is_m_for_varname m then SOME m else NONE;
      val m_o = List.foldl (fn (m, acc) => case acc of SOME x => SOME x | NONE => get_exp_if m) NONE mappings;
      val m = valOf m_o handle _ => raise ERR "debug_Pi_fun" "variable name not mapped in bir state";
     in snd m end;
    fun debug_expression_exception callback cond tm =
      if cond tm then (
          callback tm;
          raise ERR "debug_Pi_fun" "found it"
        )
      else ();
    val _ = List.map (fn state_tm =>
      let
        val (pc,env,_,_) = dest_birs_state state_tm;
        val exp = (find_env_exp "countw" o get_env_mappings) env;
        val _ = debug_expression_exception (fn tm =>
          (print_term pc; print_term tm; print_thm t)) is_BExp_IfThenElse exp;
      in () end) Pis;
  in
    t
  end;
  *)

(* -------------------------------------------------------------------------- *)


local
    open bir_immSyntax;
    fun mk_word_addr v = wordsSyntax.mk_wordii(v, 32);
    fun mk_bir_lbl x = ``bir_block_pc (BL_Address ^(gen_mk_Imm x))``;
    val bir_lbl_from_addr = snd o dest_eq o concl o EVAL o mk_bir_lbl o mk_word_addr;

   fun bir_local_symb_analysis bprog_tm birs_end_lbls birs_state =
   let
      open birs_simp_instancesLib;
      val birs_simp_select = birs_simp_default_armcm0_gen true;
      val birs_simp_select_ifthenelse = birs_simp_default_core_exp_simp;
      open holba_miscLib;

      val timer_symbanalysis = timer_start 0;
      val timer_symbanalysis_last = ref (timer_start 0);
      fun debug_output_RULE t =
         (timer_stop (fn delta_s => print ("running since " ^ delta_s ^ "\n")) timer_symbanalysis;
         timer_stop (fn delta_s => print ("time since last step " ^ delta_s ^ "\n")) (!timer_symbanalysis_last);
         timer_symbanalysis_last := timer_start 0;
         (*print_term ((last o pairSyntax.strip_pair o snd o dest_comb o concl) t);*)
         t);

      open birs_execLib;
      val birs_simp_RULE_gen = birs_rule_SUBST_trysimp_fun (birs_rule_SUBST_prog_fun bprog_tm);
      fun birs_simp_RULE last_stmt =
        ((* the ifthenelse simplification for countw assignments before branches, that gets applied after the branch happens and the condition is available in the branchcondition *)
         apply_if_branch (birs_simp_RULE_gen (birs_simp_select_ifthenelse)) o
         (* the simplification after assignments *)
         apply_if_assign last_stmt (birs_simp_RULE_gen (birs_simp_select)));
      val birs_prune_RULE =
        (birs_rule_tryprune_fun birs_rulesTheory.branch_prune1_spec_thm o
         birs_rule_tryprune_fun birs_rulesTheory.branch_prune2_spec_thm o
         birs_rule_tryjustassert_fun true);

      fun birs_post_step_fun (t, (last_pc, last_stmt)) = (
         debug_output_RULE o
         (*(apply_if_branch debug_Pi_fun) o*)
         birs_simp_RULE last_stmt o
         birs_prune_RULE
      ) t;
   in
      birs_driveLib.bir_symb_exec_to (bprog_tm, birs_post_step_fun) birs_end_lbls birs_state
   end
in
 fun birs_basic_init_state (bprog_tm, prog_birenvtyl_def) reqs init_addr =
  let
    val init_lbl = bir_lbl_from_addr init_addr;
    val precond = bslSyntax.bandl (pred_conjs reqs);
    (* TODO: remove birs_env_thm and bsysprecond_thm make it separate things (only needed for transfer) *)
      (* they shouldn't come out of the symbolic exec function, it is only needed for the transfer, and it shouldn't be a problem to compute it repeatedly, see the function gen_senv_GEN_thm below *)
    val (init_state, _, _) =
      bir_symbLib.bir_symb_analysis_init_gen (SOME bir_symbLib.pcond_gen_symb) init_lbl precond prog_birenvtyl_def;
  in
    init_state
  end;

 fun birs_basic_execute (bprog_tm, prog_birenvtyl_def) end_addrs init_state =
  let
    open birs_intervalLib;

    val end_lbls = List.map bir_lbl_from_addr end_addrs;
    val symb_exec_thm =
      bir_local_symb_analysis bprog_tm end_lbls init_state;
    val interval_thm = birs_intervals_Pi_unify_RULE "countw" symb_exec_thm;
  in
    interval_thm
  end;
 val birs_basic_execute = fn x => fn y => Profile.profile "birs_basic_execute" (birs_basic_execute x y);
end

(*
val _ = print "\n\n";
val _ = raise Fail "done";
val init_state = birs_basic_init_state birs_prog_config (200, 200) 0x100013b4;
val thm = birs_basic_execute birs_prog_config [0x100013BE, 0x100013C2] init_state;
*)


val birs_basic_merge =
  let
    open birs_mergeLib;
    open birs_intervalLib;
  in
    (birs_Pi_merge_RULE o birs_intervals_Pi_bounds_RULE "countw")
  end;
val birs_basic_merge = Profile.profile "birs_basic_merge" birs_basic_merge;

fun birs_basic_instantiate (bprog_tm, prog_birenvtyl_def) =
  let
    open birs_composeLib;
    open birs_instantiationLib;
    open birs_intervalLib;
    val birs_rule_SEQ_thm = birs_rule_SEQ_prog_fun bprog_tm;
    val inst_SEQ_fun = birs_sound_inst_SEQ_RULE birs_rule_SEQ_thm bir_symbLib.pcond_gen_symb;
  in
    fn A_thm => (birs_intervals_Pi_unify_RULE "countw" o inst_SEQ_fun A_thm)
  end;
  val birs_basic_instantiate = fn x => fn y => Profile.profile "birs_basic_instantiate" (birs_basic_instantiate x y);

(* ========================================================================================== *)

  (* TODO: add previous summaries and indirectjump theorems as argument here, and the proper handling in the buildtree function (probably good as function argument) *)
     (* handle intervals correctly: in symbolic execution driver (together with the indirectjump handling and previous summaries) and also before merging *)
  fun birs_summary (bprog_tm, prog_birenvtyl_def) reqs (init_addr, end_addr) =
    let
      val init_state = birs_basic_init_state (bprog_tm, prog_birenvtyl_def) reqs init_addr;
      val symb_exec_thm = birs_basic_execute (bprog_tm, prog_birenvtyl_def) [end_addr] init_state;

      val merged_thm = birs_basic_merge symb_exec_thm;
    in
      merged_thm
  end;
  val birs_summary = fn x => fn y => Profile.profile "birs_summary" (birs_summary x y);

  fun gen_senv_GEN_thm prog_birenvtyl_def =
    let
      open birs_auxTheory;
      val bprog_envtyl_tm = (fst o dest_eq o concl) prog_birenvtyl_def;
    in
      (REWRITE_CONV [prog_birenvtyl_def] THENC EVAL THENC REWRITE_CONV [GSYM birs_gen_env_thm, GSYM birs_gen_env_NULL_thm]) ``bir_senv_GEN_list ^bprog_envtyl_tm``
    end;


end (* local *)

end (* struct *)
