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

  val stack_space_req = 0x80;

  val pred_conjs = [
  ``BExp_BinPred BIExp_Equal
      (BExp_BinExp BIExp_And
          (BExp_Den (BVar "SP_process" (BType_Imm Bit32)))
          (BExp_Const (Imm32 3w)))
      (BExp_Const (Imm32 0w))``,
  ``BExp_BinExp BIExp_And
            (BExp_BinPred BIExp_LessOrEqual
               (BExp_Den (BVar "SP_process" (BType_Imm Bit32)))
               (BExp_Const (Imm32 ^(wordsSyntax.mk_wordii(stack_start, 32)))))
            (BExp_BinPred BIExp_LessThan
               (BExp_Const (Imm32 ^(wordsSyntax.mk_wordii(stack_end + stack_space_req, 32))))
               (BExp_Den (BVar "SP_process" (BType_Imm Bit32))))``,
  ``BExp_BinPred BIExp_LessOrEqual
       (BExp_Den (BVar "countw" (BType_Imm Bit64)))
       (BExp_Const (Imm64 ^(wordsSyntax.mk_wordii(0x10000000, 64))))``
  ];

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

end

end
