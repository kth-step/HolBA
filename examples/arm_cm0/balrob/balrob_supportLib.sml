structure balrob_supportLib =
struct

local

  open HolKernel Parse boolLib bossLib;

  open birsSyntax;

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

(* TODO: add previous summaries and indirectjump theorems as argument here (probably good as function), and the proper handling in the buildtree function *)
fun birs_summary_execute (bprog_tm, prog_birenvtyl_def) reqs (init_addr, end_addrs) =
  let
    open bir_symbLib;
    open bir_immSyntax;

    val precond = bslSyntax.bandl (pred_conjs reqs);

    fun mk_bir_lbl x = ``bir_block_pc (BL_Address ^(gen_mk_Imm x))``;
    val bir_lbl_from_addr = snd o dest_eq o concl o EVAL o mk_bir_lbl;
    val init_lbl = bir_lbl_from_addr init_addr;
    val end_lbls = List.map bir_lbl_from_addr end_addrs;

    (* TODO: remove birs_env_thm and bsysprecond_thm make it separate things (only needed for transfer) *)
      (* they shouldn't come out of the symbolic exec function, it is only needed for the transfer, and it shouldn't be a problem to compute it repeatedly, see the function gen_senv_GEN_thm below *)
    val (birs_state_init, _, _) =
      bir_symb_analysis_init_gen (SOME pcond_gen_symb) init_lbl precond prog_birenvtyl_def;
    val symb_exec_thm =
      bir_symb_analysis bprog_tm end_lbls birs_state_init;

    (* TODO: should merge Pi states here, also handle intervals correctly, in symbolic execution driver (together with the indirectjump handling and previous summaries) and also before merging *)
  in
    symb_exec_thm
  end;

  fun gen_senv_GEN_thm prog_birenvtyl_def =
    let
      open birs_auxTheory;
      val bprog_envtyl_tm = (fst o dest_eq o concl) prog_birenvtyl_def;
    in
      (REWRITE_CONV [prog_birenvtyl_def] THENC EVAL THENC REWRITE_CONV [GSYM birs_gen_env_thm, GSYM birs_gen_env_NULL_thm]) ``bir_senv_GEN_list ^bprog_envtyl_tm``
    end;


end (* local *)

end (* struct *)
