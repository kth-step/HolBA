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
    [pred_not_handlermode, (* needed for bx lr statements *)
     pred_sp_aligned]@
    (if stack_space_req = 0 then [] else
       [pred_sp_space_req stack_space_req])@
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

(* from examples/binaries/binariesCfgLib.sml *)
  val hack_map_3
             = [(0x10000bb0, "469F (mov pc, r3)", [ (* mov pc, r3 <0x10000be2, 0x10000be6, 0x10000c3c, 0x10000d0a, 0x10000d14, 0x10000d18, 0x10000d20> *)
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
                    (0x1000060c, "4697 (mov pc, r2)", [ (* mov pc, r2 <0x10000620, 0x1000065e, 0x10000682, 0x100006fe, 0x1000070a, 0x10000722, 0x10000754> *)
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
                    (0x100006b2, "4697 (mov pc, r2)", [ (* mov pc, r2 <0x1000061e, 0x1000065e, 0x10000682, 0x100006fe, 0x10000708, 0x10000754> *)
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

fun gen_const_load_32_32_cheat_thm (a,b) =
  let
    fun bir_const32 v = ``BExp_Const (Imm32 ^(wordsSyntax.mk_wordii(v, 32)))``;
    val load_cheat_thm = prove(``
    !pcond.
      birs_simplification
        pcond
        (BExp_Load
          (BExp_Den (BVar "sy_MEM" (BType_Mem Bit32 Bit8)))
          ^(bir_const32 a)
          BEnd_LittleEndian
          Bit32)
        ^(bir_const32 b)
    ``,
    cheat);
  in
    load_cheat_thm
  end;
val gen_const_load_32_32_cheat_thms = List.map gen_const_load_32_32_cheat_thm;

(* -------------------------------------------------------------------------- *)

val birs_prog_config = ((fst o dest_eq o concl) balrobLib.bir_balrob_prog_def, balrobLib.balrob_birenvtyl_def);

(* -------------------------------------------------------------------------- *)

(*
fun debug_Pi_fun t =
  let
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
in
  val bir_lbl_from_addr = snd o dest_eq o concl o EVAL o mk_bir_lbl o mk_word_addr;
end

local
  val indirjmpresolv_map_raw = (*[(0x100013b8, "", ["100013bc"])]@*)hack_map_3;
  fun process_hack_map_targets pcl =
    let
      fun fromString x =
        let
          val v = valOf (StringCvt.scanString (Int.scan StringCvt.HEX) x)
                  handle _ => raise ERR "process_hack_map_targets" "cannot process target string";
        in
          v
        end;
    in
      List.map (fn x => fromString x) (list_mk_distinct gen_eq pcl)
    end;
  val indirjmpresolv_map = List.map (fn (pc,c,pcl) => (pc,c, process_hack_map_targets pcl)) indirjmpresolv_map_raw;

  val (add_fun, lookup_fun) = aux_moveawayLib.result_cache Term.compare;
  val () = List.app (fn (pc,c,pcl) => add_fun (bir_lbl_from_addr pc, (c, List.map bir_lbl_from_addr pcl))) indirjmpresolv_map;
  fun get_indirjmp_targets lbl_tm = lookup_fun lbl_tm;
  fun replace_state_lbl st_tm lbl_tm =
    let
      val (_, env, status, pcond) = dest_birs_state st_tm;
    in
      mk_birs_state (lbl_tm, env, status, pcond)
    end;
in
  fun get_indirjmp_oracle bprog_tm st_tm =
    let
      val lbl_tm = dest_birs_state_pc st_tm;
      val targets_o = get_indirjmp_targets lbl_tm;
    in
      if not (isSome targets_o) then NONE else
      let
        val (c, targets) = valOf targets_o;
        (* TODO: add validation with lifter instruction comment c with bprog_tm, use cached lookup for this *)
        (*
        val pct = (!birs_auxLib.cur_stmt_lookup_fun) lbl_tm;
        val _ = print_thm (valOf pct);
        val _ = raise ERR "" "";
        *)
        
        val st_tms = List.map (replace_state_lbl st_tm) targets;
        val sts_tm = pred_setSyntax.mk_set st_tms;
        val exec_tm = mk_birs_symb_exec (bprog_tm, mk_sysLPi (st_tm, pred_setSyntax.mk_set [lbl_tm], sts_tm));
      in
        SOME (mk_oracle_thm "BIRS_INDIRJMP" ([], exec_tm))
      end
    end;
end

fun birs_basic_from_sums bprog_tm birs_rule_SUBST_thm sums st_tm =
  let
    open birs_intervalLib;
    val birs_simp_select = birs_simp_instancesLib.birs_simp_default_core_exp_simp;
    val birs_simp_RULE_gen = birs_execLib.birs_rule_SUBST_trysimp_fun birs_rule_SUBST_thm;
    val simplify_sp =
      (birs_simp_RULE_gen birs_simp_select) o
      (birs_Pi_each_RULE (CONV_RULE (birs_Pi_first_CONV (birs_env_var_top_CONV "SP_process"))));
    val postproc_fun = simplify_sp o birs_intervals_Pi_unify_RULE "countw";

    val jmp_t_o = get_indirjmp_oracle bprog_tm st_tm;
  in
    if isSome jmp_t_o then
      jmp_t_o
    else
      birs_strategiesLib.birs_from_summaries postproc_fun sums st_tm
  end;
val birs_basic_from_sums = fn x => fn y => fn z => Profile.profile "birs_basic_from_sums" (birs_basic_from_sums x y z);


fun birs_basic_init_state prog_birenvtyl_def reqs init_addr =
  let
    open birs_driveLib;

    val init_lbl = bir_lbl_from_addr init_addr;
    val precond = bslSyntax.bandl (pred_conjs reqs);
    val init_state =
    birs_analysis_init prog_birenvtyl_def precond init_lbl;
  in
    init_state
  end;

fun birs_basic_execute bprog_tm pre_simp extra_thms sums end_addrs init_state =
  let
    open birs_intervalLib;
    open birs_driveLib;
    val birs_rule_SUBST_thm = birs_execLib.birs_rule_SUBST_prog_fun bprog_tm;

    val end_lbls = List.map bir_lbl_from_addr end_addrs;
    val symb_exec_thm =
    birs_exec_to
      bprog_tm
      (birs_strategiesLib.birs_post_step_armcm0_default pre_simp extra_thms)
      (birs_basic_from_sums bprog_tm birs_rule_SUBST_thm sums)
      (birs_strategiesLib.not_at_lbls end_lbls)
      init_state;
    val interval_thm = birs_intervals_Pi_unify_RULE "countw" symb_exec_thm;
  in
    interval_thm
  end;
val birs_basic_execute = fn x => fn pre_simp => fn extra_thms => fn y => fn z => Profile.profile "birs_basic_execute" (birs_basic_execute x pre_simp extra_thms y z);


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
    val inst_SEQ_fun = birs_sound_inst_SEQ_RULE birs_rule_SEQ_thm birs_driveLib.pcond_gen_symb;
  in
    fn A_thm => (birs_intervals_Pi_unify_RULE "countw" o inst_SEQ_fun A_thm)
  end;
  val birs_basic_instantiate = fn x => fn y => Profile.profile "birs_basic_instantiate" (birs_basic_instantiate x y);

(* ========================================================================================== *)

  fun birs_summary_gen pre_simp extra_thms (bprog_tm, prog_birenvtyl_def) sums reqs (init_addr, end_addrs) =
    let
      val init_state = birs_basic_init_state prog_birenvtyl_def reqs init_addr;
      val symb_exec_thm = birs_basic_execute bprog_tm pre_simp extra_thms sums end_addrs init_state;

      (* need to handle intervals correctly: in symbolic execution driver
           (also need this together with the indirectjump handling and previous summaries) and also before merging *)
      val merged_thm = birs_basic_merge symb_exec_thm;
    in
      merged_thm
  end;
  val birs_summary_gen = fn pre_simp => fn extra_thms => fn x => fn y => fn z => Profile.profile "birs_summary_gen" (birs_summary_gen pre_simp extra_thms x y z);

  val birs_summary = birs_summary_gen birs_simpLib.birs_simp_ID_fun [];


end (* local *)

end (* struct *)
