structure commonBalrobScriptLib =
struct

local
  open bir_symbexec_stateLib;
  open bir_symbexec_coreLib;
in
  (* TODO: how much space do we actually have? we should "enforce" this with the linker... *)
  val mem_ram_start = 0x10000000;
  val mem_ram_size  = 0x2000;

  val stack_size  = 0x100;
  val stack_start = mem_ram_start + mem_ram_size -16;
  val stack_end   = stack_start - stack_size;

(*
  val stack_space_req = 0x80;
*)

  (* TODO: need to fix this to handlermode -> needs change of the used lifter machine *)
  val pred_not_handlermode =
  ``BExp_UnaryExp BIExp_Not (BExp_Den (BVar "ModeHandler" BType_Bool))``;

  val pred_sp_aligned =
  ``BExp_BinPred BIExp_Equal
      (BExp_BinExp BIExp_And
          (BExp_Den (BVar "SP_process" (BType_Imm Bit32)))
          (BExp_Const (Imm32 3w)))
      (BExp_Const (Imm32 0w))``;

  fun pred_sp_space_req stack_space_req =
  ``BExp_BinExp BIExp_And
            (BExp_BinPred BIExp_LessOrEqual
               (BExp_Den (BVar "SP_process" (BType_Imm Bit32)))
               (BExp_Const (Imm32 ^(wordsSyntax.mk_wordii(stack_start, 32)))))
            (BExp_BinPred BIExp_LessThan
               (BExp_Const (Imm32 ^(wordsSyntax.mk_wordii(stack_end + stack_space_req, 32))))
               (BExp_Den (BVar "SP_process" (BType_Imm Bit32))))``;

  fun pred_countw_space_req countw_space_req =
  ``BExp_BinPred BIExp_LessOrEqual
       (BExp_Den (BVar "countw" (BType_Imm Bit64)))
       (BExp_Const (Imm64 ^(wordsSyntax.mk_wordii(0x10000000 - countw_space_req, 64))))``;

  fun pred_conjs (stack_space_req, countw_space_req) =
    [pred_not_handlermode,
     pred_sp_aligned,
     pred_sp_space_req stack_space_req,
     pred_countw_space_req countw_space_req];

  val mem_sz_const = mem_ram_start;
  val mem_sz_globl = 0x1000;
  val mem_sz_stack = mem_ram_size - mem_sz_globl;
  val _ = if mem_sz_stack > 0 then () else
          raise ERR "scriptLib" "mem_sz_stack should be greater than 0";


  fun abpfun cfb systs =
    let
      val systs_filtered =
        if cfb andalso length systs > 1 then
          List.filter check_feasible systs
        else
          systs;

      val _ = if not cfb then () else
              List.app (fn syst =>
                if state_is_running syst then () else
                print "a non-running state is still present after feasibility check\n"
              ) systs_filtered;

      fun remove_asserts_from_running syst =
          if state_is_running syst then
            state_remove_preds_by_suffix "assert_cnd" syst
          else
            syst;

      val systs_noassertpreds =
             List.map
             remove_asserts_from_running
             systs_filtered;
    in
      systs_noassertpreds
    end;

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
     | _ => raise Fail "get_fun_usage: don't know function";

end

end
