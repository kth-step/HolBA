open HolKernel boolLib Parse bossLib;

open markerTheory;

open bir_bool_expSyntax;
open bir_programSyntax bir_program_labelsTheory;
open bir_immTheory bir_valuesTheory bir_expTheory;
open bir_tsTheory bir_bool_expTheory bir_programTheory;
open bir_exp_equivTheory;

open bir_riscv_backlifterTheory;
open bir_backlifterLib;
open bir_riscv_extrasTheory;
open bir_compositionLib;

open bir_interval_expTheory;

open bir_lifting_machinesTheory;
open bir_typing_expTheory;
open bir_htTheory;

open bir_predLib;

open bir_smtLib;

open bir_symbTheory birs_auxTheory;
open HolBACoreSimps;
open bir_program_transfTheory;
open bir_extra_expsTheory;

open total_program_logicTheory;
open total_ext_program_logicTheory;
open symb_prop_transferTheory;

open jgmt_rel_bir_contTheory;

open pred_setTheory;

open program_logicSimps;

open bir_env_oldTheory;
open bir_program_varsTheory;

open kernel_trap_spec_riscvTheory;

open bslSyntax;

val _ = new_theory "kernel_trap_spec_bir";

(* ------------------------- *)
(* BSPEC trap_entry contract *)
(* ------------------------- *)

(* address values from the RISC-V specification, as BIR constants *)
fun addr_word_tm def = (rhs o concl) def;
fun addr_num_tm def = (numSyntax.mk_numeral o wordsSyntax.dest_word_literal o addr_word_tm) def;

val bspec_kernel_trap_entry_pre_tm = bandl [
  beq (bden (bvarimm8 "MPRV"), bconst8 3),

  mem_addrs_aligned_prog_disj_bir_tm mem_params_standard "mscratch",

  ``BExp_unchanged_mem_interval_distinct Bit64
     (^(addr_num_tm kernel_trap_entry_init_addr_def) - 256)
     ^(addr_num_tm kernel_trap_return_end_addr_def)
     ^(bden (bvarimm64 "mscratch"))
     8``,

  beq (bden (bvarimm64 "mscratch"), bconstvar64 "pre_mscratch"),

  beq (bden (bvarimm64 "mepc"), bconstvar64 "pre_mepc"),

  beq (bden (bvarimm64 "mcause"), bconstvar64 "pre_mcause"),

  beq (bden (bvarimm64 "mhartid"), bconstvar64 "pre_mhartid"),

  beq (bden (bvarimm64 "mtval"), bconstvar64 "pre_mtval"),

  beq (bden (bvarimm64 "x1"), bconstvar64 "pre_x1"),

  beq (bden (bvarimm64 "x2"), bconstvar64 "pre_x2"),

  beq (bden (bvarimm64 "x3"), bconstvar64 "pre_x3"),

  beq (bden (bvarimm64 "x4"), bconstvar64 "pre_x4"),

  beq (bden (bvarimm64 "x5"), bconstvar64 "pre_x5"),

  beq (bden (bvarimm64 "x6"), bconstvar64 "pre_x6"),

  beq (bden (bvarimm64 "x7"), bconstvar64 "pre_x7"),

  beq (bden (bvarimm64 "x8"), bconstvar64 "pre_x8"),

  beq (bden (bvarimm64 "x9"), bconstvar64 "pre_x9"),

  beq (bden (bvarimm64 "x10"), bconstvar64 "pre_x10"),

  beq (bden (bvarimm64 "x11"), bconstvar64 "pre_x11"),

  beq (bden (bvarimm64 "x12"), bconstvar64 "pre_x12"),

  beq (bden (bvarimm64 "x13"), bconstvar64 "pre_x13"),

  beq (bden (bvarimm64 "x14"), bconstvar64 "pre_x14"),

  beq (bden (bvarimm64 "x15"), bconstvar64 "pre_x15"),

  beq (bden (bvarimm64 "x16"), bconstvar64 "pre_x16"),

  beq (bden (bvarimm64 "x17"), bconstvar64 "pre_x17"),

  beq (bden (bvarimm64 "x18"), bconstvar64 "pre_x18"),

  beq (bden (bvarimm64 "x19"), bconstvar64 "pre_x19"),

  beq (bden (bvarimm64 "x20"), bconstvar64 "pre_x20"),

  beq (bden (bvarimm64 "x21"), bconstvar64 "pre_x21"),

  beq (bden (bvarimm64 "x22"), bconstvar64 "pre_x22"),

  beq (bden (bvarimm64 "x23"), bconstvar64 "pre_x23"),

  beq (bden (bvarimm64 "x24"), bconstvar64 "pre_x24"),

  beq (bden (bvarimm64 "x25"), bconstvar64 "pre_x25"),

  beq (bden (bvarimm64 "x26"), bconstvar64 "pre_x26"),

  beq (bden (bvarimm64 "x27"), bconstvar64 "pre_x27"),

  beq (bden (bvarimm64 "x28"), bconstvar64 "pre_x28"),

  beq (bden (bvarimm64 "x29"), bconstvar64 "pre_x29"),

  beq (bden (bvarimm64 "x30"), bconstvar64 "pre_x30"),

  beq (bden (bvarimm64 "x31"), bconstvar64 "pre_x31")
];

Definition bspec_kernel_trap_entry_pre_def:
 bspec_kernel_trap_entry_pre
  (pre_mscratch:word64) (pre_mepc:word64)
  (pre_mcause:word64) (pre_mhartid:word64)
  (pre_mtval:word64)
  (pre_x1:word64) (pre_x2:word64)
  (pre_x3:word64) (pre_x4:word64)
  (pre_x5:word64) (pre_x6:word64)
  (pre_x7:word64) (pre_x8:word64)
  (pre_x9:word64) (pre_x10:word64)
  (pre_x11:word64) (pre_x12:word64)
  (pre_x13:word64) (pre_x14:word64)
  (pre_x15:word64) (pre_x16:word64)
  (pre_x17:word64) (pre_x18:word64)
  (pre_x19:word64) (pre_x20:word64)
  (pre_x21:word64) (pre_x22:word64)
  (pre_x23:word64) (pre_x24:word64)
  (pre_x25:word64) (pre_x26:word64)
  (pre_x27:word64) (pre_x28:word64)
  (pre_x29:word64) (pre_x30:word64)
  (pre_x31:word64)
 : bir_exp_t =
  ^bspec_kernel_trap_entry_pre_tm
End

val bspec_kernel_trap_entry_post_tm = bandl [
  beq (bden (bvarimm64 "mscratch"), bconstvar64 "pre_x10"),

  beq (bden (bvarimm64 "x2"),
       bplus (bmult (bconst ``0xFFFFFFFFFFFFFFFFw:word64``,
                     blshift (bconstvar64 "pre_mhartid", bconst64 10)),
              bconst (addr_word_tm kernel_trap_slots_addr_def))),

  beq (bden (bvarimm64 "x3"), bconst (addr_word_tm kernel_trap_global_pointer_addr_def)),

  beq (bden (bvarimm64 "x10"), bconstvar64 "pre_mscratch"),

  beq (bden (bvarimm64 "x11"), bconstvar64 "pre_mcause"),

  beq (bden (bvarimm64 "x12"), bconstvar64 "pre_mtval"),

  beq (bload64_le (bden (bvarmem64_8 "MEM8")) (bplus (bconstvar64 "pre_mscratch", bconst64 8)),
       bconstvar64 "pre_mepc"),

  beq (bload64_le (bden (bvarmem64_8 "MEM8")) (bplus (bconstvar64 "pre_mscratch", bconst64 16)),
       bconstvar64 "pre_x1"),

  beq (bload64_le (bden (bvarmem64_8 "MEM8")) (bplus (bconstvar64 "pre_mscratch", bconst64 24)),
       bconstvar64 "pre_x2"),

  beq (bload64_le (bden (bvarmem64_8 "MEM8")) (bplus (bconstvar64 "pre_mscratch", bconst64 32)),
       bconstvar64 "pre_x3"),

  beq (bload64_le (bden (bvarmem64_8 "MEM8")) (bplus (bconstvar64 "pre_mscratch", bconst64 40)),
       bconstvar64 "pre_x4"),

  beq (bload64_le (bden (bvarmem64_8 "MEM8")) (bplus (bconstvar64 "pre_mscratch", bconst64 48)),
       bconstvar64 "pre_x5"),

  beq (bload64_le (bden (bvarmem64_8 "MEM8")) (bplus (bconstvar64 "pre_mscratch", bconst64 56)),
       bconstvar64 "pre_x6"),

  beq (bload64_le (bden (bvarmem64_8 "MEM8")) (bplus (bconstvar64 "pre_mscratch", bconst64 64)),
       bconstvar64 "pre_x7"),

  beq (bload64_le (bden (bvarmem64_8 "MEM8")) (bplus (bconstvar64 "pre_mscratch", bconst64 72)),
       bconstvar64 "pre_x8"),

  beq (bload64_le (bden (bvarmem64_8 "MEM8")) (bplus (bconstvar64 "pre_mscratch", bconst64 80)),
       bconstvar64 "pre_x9"),

  beq (bload64_le (bden (bvarmem64_8 "MEM8")) (bplus (bconstvar64 "pre_mscratch", bconst64 88)),
       bconstvar64 "pre_x10"),

  beq (bload64_le (bden (bvarmem64_8 "MEM8")) (bplus (bconstvar64 "pre_mscratch", bconst64 96)),
       bconstvar64 "pre_x11"),

  beq (bload64_le (bden (bvarmem64_8 "MEM8")) (bplus (bconstvar64 "pre_mscratch", bconst64 104)),
       bconstvar64 "pre_x12"),

  beq (bload64_le (bden (bvarmem64_8 "MEM8")) (bplus (bconstvar64 "pre_mscratch", bconst64 112)),
       bconstvar64 "pre_x13"),

  beq (bload64_le (bden (bvarmem64_8 "MEM8")) (bplus (bconstvar64 "pre_mscratch", bconst64 120)),
       bconstvar64 "pre_x14"),

  beq (bload64_le (bden (bvarmem64_8 "MEM8")) (bplus (bconstvar64 "pre_mscratch", bconst64 128)),
       bconstvar64 "pre_x15"),

  beq (bload64_le (bden (bvarmem64_8 "MEM8")) (bplus (bconstvar64 "pre_mscratch", bconst64 136)),
       bconstvar64 "pre_x16"),

  beq (bload64_le (bden (bvarmem64_8 "MEM8")) (bplus (bconstvar64 "pre_mscratch", bconst64 144)),
       bconstvar64 "pre_x17"),

  beq (bload64_le (bden (bvarmem64_8 "MEM8")) (bplus (bconstvar64 "pre_mscratch", bconst64 152)),
       bconstvar64 "pre_x18"),

  beq (bload64_le (bden (bvarmem64_8 "MEM8")) (bplus (bconstvar64 "pre_mscratch", bconst64 160)),
       bconstvar64 "pre_x19"),

  beq (bload64_le (bden (bvarmem64_8 "MEM8")) (bplus (bconstvar64 "pre_mscratch", bconst64 168)),
       bconstvar64 "pre_x20"),

  beq (bload64_le (bden (bvarmem64_8 "MEM8")) (bplus (bconstvar64 "pre_mscratch", bconst64 176)),
       bconstvar64 "pre_x21"),

  beq (bload64_le (bden (bvarmem64_8 "MEM8")) (bplus (bconstvar64 "pre_mscratch", bconst64 184)),
       bconstvar64 "pre_x22"),

  beq (bload64_le (bden (bvarmem64_8 "MEM8")) (bplus (bconstvar64 "pre_mscratch", bconst64 192)),
       bconstvar64 "pre_x23"),

  beq (bload64_le (bden (bvarmem64_8 "MEM8")) (bplus (bconstvar64 "pre_mscratch", bconst64 200)),
       bconstvar64 "pre_x24"),

  beq (bload64_le (bden (bvarmem64_8 "MEM8")) (bplus (bconstvar64 "pre_mscratch", bconst64 208)),
       bconstvar64 "pre_x25"),

  beq (bload64_le (bden (bvarmem64_8 "MEM8")) (bplus (bconstvar64 "pre_mscratch", bconst64 216)),
       bconstvar64 "pre_x26"),

  beq (bload64_le (bden (bvarmem64_8 "MEM8")) (bplus (bconstvar64 "pre_mscratch", bconst64 224)),
       bconstvar64 "pre_x27"),

  beq (bload64_le (bden (bvarmem64_8 "MEM8")) (bplus (bconstvar64 "pre_mscratch", bconst64 232)),
       bconstvar64 "pre_x28"),

  beq (bload64_le (bden (bvarmem64_8 "MEM8")) (bplus (bconstvar64 "pre_mscratch", bconst64 240)),
       bconstvar64 "pre_x29"),

  beq (bload64_le (bden (bvarmem64_8 "MEM8")) (bplus (bconstvar64 "pre_mscratch", bconst64 248)),
       bconstvar64 "pre_x30"),

  beq (bload64_le (bden (bvarmem64_8 "MEM8")) (bplus (bconstvar64 "pre_mscratch", bconst64 256)),
       bconstvar64 "pre_x31")
];

Definition bspec_kernel_trap_entry_post_def:
 bspec_kernel_trap_entry_post
  (pre_mscratch:word64) (pre_mepc:word64)
  (pre_mcause:word64) (pre_mhartid:word64)
  (pre_mtval:word64)
  (pre_x1:word64) (pre_x2:word64)
  (pre_x3:word64) (pre_x4:word64)
  (pre_x5:word64) (pre_x6:word64)
  (pre_x7:word64) (pre_x8:word64)
  (pre_x9:word64) (pre_x10:word64)
  (pre_x11:word64) (pre_x12:word64)
  (pre_x13:word64) (pre_x14:word64)
  (pre_x15:word64) (pre_x16:word64)
  (pre_x17:word64) (pre_x18:word64)
  (pre_x19:word64) (pre_x20:word64)
  (pre_x21:word64) (pre_x22:word64)
  (pre_x23:word64) (pre_x24:word64)
  (pre_x25:word64) (pre_x26:word64)
  (pre_x27:word64) (pre_x28:word64)
  (pre_x29:word64) (pre_x30:word64)
  (pre_x31:word64)
 : bir_exp_t =
  ^bspec_kernel_trap_entry_post_tm
End

(* -------------------------- *)
(* BSPEC trap_return contract *)
(* -------------------------- *)

val bspec_kernel_trap_return_pre_tm = bandl [
  beq (bden (bvarimm8 "MPRV"), bconst8 3),

  mem_addrs_aligned_prog_disj_bir_tm mem_params_standard "x10",

  beq (bden (bvarimm64 "mscratch"), bconstvar64 "pre_mscratch"),

  beq (bden (bvarimm64 "x10"), bconstvar64 "pre_x10"),

  beq (bload64_le (bden (bvarmem64_8 "MEM8")) (bplus (bconstvar64 "pre_x10", bconst64 8)),
       bconstvar64 "pre_mepc_mem"),

  beq (bload64_le (bden (bvarmem64_8 "MEM8")) (bplus (bconstvar64 "pre_x10", bconst64 16)),
       bconstvar64 "pre_x1_mem"),

  beq (bload64_le (bden (bvarmem64_8 "MEM8")) (bplus (bconstvar64 "pre_x10", bconst64 24)),
       bconstvar64 "pre_x2_mem"),

  beq (bload64_le (bden (bvarmem64_8 "MEM8")) (bplus (bconstvar64 "pre_x10", bconst64 32)),
       bconstvar64 "pre_x3_mem"),

  beq (bload64_le (bden (bvarmem64_8 "MEM8")) (bplus (bconstvar64 "pre_x10", bconst64 40)),
       bconstvar64 "pre_x4_mem"),

  beq (bload64_le (bden (bvarmem64_8 "MEM8")) (bplus (bconstvar64 "pre_x10", bconst64 48)),
       bconstvar64 "pre_x5_mem"),

  beq (bload64_le (bden (bvarmem64_8 "MEM8")) (bplus (bconstvar64 "pre_x10", bconst64 56)),
       bconstvar64 "pre_x6_mem"),

  beq (bload64_le (bden (bvarmem64_8 "MEM8")) (bplus (bconstvar64 "pre_x10", bconst64 64)),
       bconstvar64 "pre_x7_mem"),

  beq (bload64_le (bden (bvarmem64_8 "MEM8")) (bplus (bconstvar64 "pre_x10", bconst64 72)),
       bconstvar64 "pre_x8_mem"),

  beq (bload64_le (bden (bvarmem64_8 "MEM8")) (bplus (bconstvar64 "pre_x10", bconst64 80)),
       bconstvar64 "pre_x9_mem"),

  beq (bload64_le (bden (bvarmem64_8 "MEM8")) (bplus (bconstvar64 "pre_x10", bconst64 88)),
       bconstvar64 "pre_x10_mem"),

  beq (bload64_le (bden (bvarmem64_8 "MEM8")) (bplus (bconstvar64 "pre_x10", bconst64 96)),
       bconstvar64 "pre_x11_mem"),

  beq (bload64_le (bden (bvarmem64_8 "MEM8")) (bplus (bconstvar64 "pre_x10", bconst64 104)),
       bconstvar64 "pre_x12_mem"),

  beq (bload64_le (bden (bvarmem64_8 "MEM8")) (bplus (bconstvar64 "pre_x10", bconst64 112)),
       bconstvar64 "pre_x13_mem"),

  beq (bload64_le (bden (bvarmem64_8 "MEM8")) (bplus (bconstvar64 "pre_x10", bconst64 120)),
       bconstvar64 "pre_x14_mem"),

  beq (bload64_le (bden (bvarmem64_8 "MEM8")) (bplus (bconstvar64 "pre_x10", bconst64 128)),
       bconstvar64 "pre_x15_mem"),

  beq (bload64_le (bden (bvarmem64_8 "MEM8")) (bplus (bconstvar64 "pre_x10", bconst64 136)),
       bconstvar64 "pre_x16_mem"),

  beq (bload64_le (bden (bvarmem64_8 "MEM8")) (bplus (bconstvar64 "pre_x10", bconst64 144)),
       bconstvar64 "pre_x17_mem"),

  beq (bload64_le (bden (bvarmem64_8 "MEM8")) (bplus (bconstvar64 "pre_x10", bconst64 152)),
       bconstvar64 "pre_x18_mem"),

  beq (bload64_le (bden (bvarmem64_8 "MEM8")) (bplus (bconstvar64 "pre_x10", bconst64 160)),
       bconstvar64 "pre_x19_mem"),

  beq (bload64_le (bden (bvarmem64_8 "MEM8")) (bplus (bconstvar64 "pre_x10", bconst64 168)),
       bconstvar64 "pre_x20_mem"),

  beq (bload64_le (bden (bvarmem64_8 "MEM8")) (bplus (bconstvar64 "pre_x10", bconst64 176)),
       bconstvar64 "pre_x21_mem"),

  beq (bload64_le (bden (bvarmem64_8 "MEM8")) (bplus (bconstvar64 "pre_x10", bconst64 184)),
       bconstvar64 "pre_x22_mem"),

  beq (bload64_le (bden (bvarmem64_8 "MEM8")) (bplus (bconstvar64 "pre_x10", bconst64 192)),
       bconstvar64 "pre_x23_mem"),

  beq (bload64_le (bden (bvarmem64_8 "MEM8")) (bplus (bconstvar64 "pre_x10", bconst64 200)),
       bconstvar64 "pre_x24_mem"),

  beq (bload64_le (bden (bvarmem64_8 "MEM8")) (bplus (bconstvar64 "pre_x10", bconst64 208)),
       bconstvar64 "pre_x25_mem"),

  beq (bload64_le (bden (bvarmem64_8 "MEM8")) (bplus (bconstvar64 "pre_x10", bconst64 216)),
       bconstvar64 "pre_x26_mem"),

  beq (bload64_le (bden (bvarmem64_8 "MEM8")) (bplus (bconstvar64 "pre_x10", bconst64 224)),
       bconstvar64 "pre_x27_mem"),

  beq (bload64_le (bden (bvarmem64_8 "MEM8")) (bplus (bconstvar64 "pre_x10", bconst64 232)),
       bconstvar64 "pre_x28_mem"),

  beq (bload64_le (bden (bvarmem64_8 "MEM8")) (bplus (bconstvar64 "pre_x10", bconst64 240)),
       bconstvar64 "pre_x29_mem"),

  beq (bload64_le (bden (bvarmem64_8 "MEM8")) (bplus (bconstvar64 "pre_x10", bconst64 248)),
       bconstvar64 "pre_x30_mem"),

  beq (bload64_le (bden (bvarmem64_8 "MEM8")) (bplus (bconstvar64 "pre_x10", bconst64 256)),
       bconstvar64 "pre_x31_mem")
];

Definition bspec_kernel_trap_return_pre_def:
 bspec_kernel_trap_return_pre
 (pre_mscratch:word64) (pre_x10:word64)
 (pre_mepc_mem:word64)
 (pre_x1_mem:word64) (pre_x2_mem:word64)
 (pre_x3_mem:word64) (pre_x4_mem:word64)
 (pre_x5_mem:word64) (pre_x6_mem:word64)
 (pre_x7_mem:word64) (pre_x8_mem:word64)
 (pre_x9_mem:word64) (pre_x10_mem:word64)
 (pre_x11_mem:word64) (pre_x12_mem:word64)
 (pre_x13_mem:word64) (pre_x14_mem:word64)
 (pre_x15_mem:word64) (pre_x16_mem:word64)
 (pre_x17_mem:word64) (pre_x18_mem:word64)
 (pre_x19_mem:word64) (pre_x20_mem:word64)
 (pre_x21_mem:word64) (pre_x22_mem:word64)
 (pre_x23_mem:word64) (pre_x24_mem:word64)
 (pre_x25_mem:word64) (pre_x26_mem:word64)
 (pre_x27_mem:word64) (pre_x28_mem:word64)
 (pre_x29_mem:word64) (pre_x30_mem:word64)
 (pre_x31_mem:word64)
 : bir_exp_t =
  ^bspec_kernel_trap_return_pre_tm
End

val bspec_kernel_trap_return_post_tm = bandl [
  beq (bden (bvarimm64 "mscratch"), bconstvar64 "pre_x10"),

  beq (bden (bvarimm64 "mepc"),
       band (bconst ``0xFFFFFFFFFFFFFFFCw:word64``, bconstvar64 "pre_mepc_mem")),

  beq (bden (bvarimm64 "x1"), bconstvar64 "pre_x1_mem"),

  beq (bden (bvarimm64 "x2"), bconstvar64 "pre_x2_mem"),

  beq (bden (bvarimm64 "x3"), bconstvar64 "pre_x3_mem"),

  beq (bden (bvarimm64 "x4"), bconstvar64 "pre_x4_mem"),

  beq (bden (bvarimm64 "x5"), bconstvar64 "pre_x5_mem"),

  beq (bden (bvarimm64 "x6"), bconstvar64 "pre_x6_mem"),

  beq (bden (bvarimm64 "x7"), bconstvar64 "pre_x7_mem"),

  beq (bden (bvarimm64 "x8"), bconstvar64 "pre_x8_mem"),

  beq (bden (bvarimm64 "x9"), bconstvar64 "pre_x9_mem"),

  beq (bden (bvarimm64 "x10"), bconstvar64 "pre_x10_mem"),

  beq (bden (bvarimm64 "x11"), bconstvar64 "pre_x11_mem"),

  beq (bden (bvarimm64 "x12"), bconstvar64 "pre_x12_mem"),

  beq (bden (bvarimm64 "x13"), bconstvar64 "pre_x13_mem"),

  beq (bden (bvarimm64 "x14"), bconstvar64 "pre_x14_mem"),

  beq (bden (bvarimm64 "x15"), bconstvar64 "pre_x15_mem"),

  beq (bden (bvarimm64 "x16"), bconstvar64 "pre_x16_mem"),

  beq (bden (bvarimm64 "x17"), bconstvar64 "pre_x17_mem"),

  beq (bden (bvarimm64 "x18"), bconstvar64 "pre_x18_mem"),

  beq (bden (bvarimm64 "x19"), bconstvar64 "pre_x19_mem"),

  beq (bden (bvarimm64 "x20"), bconstvar64 "pre_x20_mem"),

  beq (bden (bvarimm64 "x21"), bconstvar64 "pre_x21_mem"),

  beq (bden (bvarimm64 "x22"), bconstvar64 "pre_x22_mem"),

  beq (bden (bvarimm64 "x23"), bconstvar64 "pre_x23_mem"),

  beq (bden (bvarimm64 "x24"), bconstvar64 "pre_x24_mem"),

  beq (bden (bvarimm64 "x25"), bconstvar64 "pre_x25_mem"),

  beq (bden (bvarimm64 "x26"), bconstvar64 "pre_x26_mem"),

  beq (bden (bvarimm64 "x27"), bconstvar64 "pre_x27_mem"),

  beq (bden (bvarimm64 "x28"), bconstvar64 "pre_x28_mem"),

  beq (bden (bvarimm64 "x29"), bconstvar64 "pre_x29_mem"),

  beq (bden (bvarimm64 "x30"), bconstvar64 "pre_x30_mem"),

  beq (bden (bvarimm64 "x31"), bconstvar64 "pre_x31_mem")
];

Definition bspec_kernel_trap_return_post_def:
 bspec_kernel_trap_return_post
 (pre_mscratch:word64) (pre_x10:word64)
 (pre_mepc_mem:word64)
 (pre_x1_mem:word64) (pre_x2_mem:word64)
 (pre_x3_mem:word64) (pre_x4_mem:word64)
 (pre_x5_mem:word64) (pre_x6_mem:word64)
 (pre_x7_mem:word64) (pre_x8_mem:word64)
 (pre_x9_mem:word64) (pre_x10_mem:word64)
 (pre_x11_mem:word64) (pre_x12_mem:word64)
 (pre_x13_mem:word64) (pre_x14_mem:word64)
 (pre_x15_mem:word64) (pre_x16_mem:word64)
 (pre_x17_mem:word64) (pre_x18_mem:word64)
 (pre_x19_mem:word64) (pre_x20_mem:word64)
 (pre_x21_mem:word64) (pre_x22_mem:word64)
 (pre_x23_mem:word64) (pre_x24_mem:word64)
 (pre_x25_mem:word64) (pre_x26_mem:word64)
 (pre_x27_mem:word64) (pre_x28_mem:word64)
 (pre_x29_mem:word64) (pre_x30_mem:word64)
 (pre_x31_mem:word64)
 : bir_exp_t =
 ^bspec_kernel_trap_return_post_tm
End

(* ----------------------------------------------- *)
(* Connecting RISC-V and BSPEC contracts for entry *)
(* ----------------------------------------------- *)

Theorem kernel_trap_entry_riscv_pre_imp_bspec_pre_thm:
 bir_pre_riscv_to_bir
  (riscv_kernel_trap_entry_pre pre_mscratch pre_mepc pre_mcause
    pre_mhartid pre_mtval pre_x1 pre_x2 pre_x3 pre_x4 pre_x5 pre_x6
    pre_x7 pre_x8 pre_x9 pre_x10 pre_x11 pre_x12 pre_x13 pre_x14
    pre_x15 pre_x16 pre_x17 pre_x18 pre_x19 pre_x20 pre_x21 pre_x22
    pre_x23 pre_x24 pre_x25 pre_x26 pre_x27 pre_x28 pre_x29 pre_x30 pre_x31)
  (bspec_kernel_trap_entry_pre pre_mscratch pre_mepc pre_mcause
    pre_mhartid pre_mtval pre_x1 pre_x2 pre_x3 pre_x4 pre_x5 pre_x6
    pre_x7 pre_x8 pre_x9 pre_x10 pre_x11 pre_x12 pre_x13 pre_x14
    pre_x15 pre_x16 pre_x17 pre_x18 pre_x19 pre_x20 pre_x21 pre_x22
    pre_x23 pre_x24 pre_x25 pre_x26 pre_x27 pre_x28 pre_x29 pre_x30 pre_x31)
Proof
  rw [bir_pre_riscv_to_bir_def] >-
   (rw [bspec_kernel_trap_entry_pre_def] >>    
    FULL_SIMP_TAC (std_ss++HolBASimps.bir_is_bool_ss) [
     bir_extra_expsTheory.BExp_Aligned_def,
     bir_immTheory.n2bs_def,
     BExp_unchanged_mem_interval_distinct_def
    ]) >>
  Q.PAT_X_ASSUM `bir_env_vars_are_initialised x y` (fn thm => ALL_TAC) >>

  Cases_on `bs` >> Cases_on `b0` >>
  
  FULL_SIMP_TAC (std_ss) [
   riscv_kernel_trap_entry_pre_def,
   kernel_trap_entry_init_addr_def, kernel_trap_return_end_addr_def,
   bspec_kernel_trap_entry_pre_def,
   bir_extra_expsTheory.BExp_Aligned_def
  ] >>
  
  fs [GSYM bir_and_equiv] >>

  FULL_SIMP_TAC (std_ss++holBACore_ss) [
   bir_eval_bin_pred_def,
   riscv_bmr_rel_EVAL,
   bir_immTheory.bool2b_def,
   bir_immTheory.bool2w_def,
   bir_envTheory.bir_env_read_def,bir_envTheory.bir_env_lookup_def,
   BExp_unchanged_mem_interval_distinct_def,
   bir_val_TF_bool2b_DEF
  ] >>

  rw []
QED

Theorem kernel_trap_entry_riscv_post_imp_bspec_post_thm:
 !ls. bir_post_bir_to_riscv
   (riscv_kernel_trap_entry_post pre_mscratch pre_mepc pre_mcause
    pre_mhartid pre_mtval pre_x1 pre_x2 pre_x3 pre_x4 pre_x5 pre_x6
    pre_x7 pre_x8 pre_x9 pre_x10 pre_x11 pre_x12 pre_x13 pre_x14
    pre_x15 pre_x16 pre_x17 pre_x18 pre_x19 pre_x20 pre_x21 pre_x22
    pre_x23 pre_x24 pre_x25 pre_x26 pre_x27 pre_x28 pre_x29 pre_x30 pre_x31)
   (\l. (bspec_kernel_trap_entry_post pre_mscratch pre_mepc pre_mcause
    pre_mhartid pre_mtval pre_x1 pre_x2 pre_x3 pre_x4 pre_x5 pre_x6
    pre_x7 pre_x8 pre_x9 pre_x10 pre_x11 pre_x12 pre_x13 pre_x14
    pre_x15 pre_x16 pre_x17 pre_x18 pre_x19 pre_x20 pre_x21 pre_x22
    pre_x23 pre_x24 pre_x25 pre_x26 pre_x27 pre_x28 pre_x29 pre_x30 pre_x31))
   ls
Proof
 fs [bir_post_bir_to_riscv_def,bspec_kernel_trap_entry_post_def,GSYM bir_and_equiv] >>

 Cases_on `bs` >> Cases_on `b0` >>
 
 FULL_SIMP_TAC (std_ss++holBACore_ss) [
  bir_envTheory.bir_env_read_def, bir_envTheory.bir_env_check_type_def,
  bir_envTheory.bir_env_lookup_type_def, bir_envTheory.bir_env_lookup_def,
  bir_eval_bin_pred_def,
  bir_eval_bin_pred_exists_64_mem_eq,
  bir_eval_bin_pred_exists_64_eq
 ] >>

 rw [riscv_kernel_trap_entry_post_def,
     kernel_trap_slots_addr_def, kernel_trap_global_pointer_addr_def] >>

 METIS_TAC [
  bir_load_from_mem_riscv_mem_load_dword,
  bmr_rel_riscv_MEM8_map,
  riscv_bmr_mscratch_equiv,
  riscv_bmr_x2_equiv,
  riscv_bmr_x3_equiv,
  riscv_bmr_x10_equiv,
  riscv_bmr_x11_equiv,
  riscv_bmr_x12_equiv
 ]
QED

(* ------------------------------------------------ *)
(* Connecting RISC-V and BSPEC contracts for return *)
(* ------------------------------------------------ *)

Theorem kernel_trap_return_riscv_pre_imp_bspec_pre_thm:
 bir_pre_riscv_to_bir
  (riscv_kernel_trap_return_pre pre_mscratch pre_x10 pre_mepc_mem pre_x1_mem
      pre_x2_mem pre_x3_mem pre_x4_mem pre_x5_mem pre_x6_mem pre_x7_mem
      pre_x8_mem pre_x9_mem pre_x10_mem pre_x11_mem pre_x12_mem pre_x13_mem
      pre_x14_mem pre_x15_mem pre_x16_mem pre_x17_mem pre_x18_mem pre_x19_mem
      pre_x20_mem pre_x21_mem pre_x22_mem pre_x23_mem pre_x24_mem pre_x25_mem
      pre_x26_mem pre_x27_mem pre_x28_mem pre_x29_mem pre_x30_mem pre_x31_mem)
  (bspec_kernel_trap_return_pre pre_mscratch pre_x10 pre_mepc_mem pre_x1_mem
      pre_x2_mem pre_x3_mem pre_x4_mem pre_x5_mem pre_x6_mem pre_x7_mem
      pre_x8_mem pre_x9_mem pre_x10_mem pre_x11_mem pre_x12_mem pre_x13_mem
      pre_x14_mem pre_x15_mem pre_x16_mem pre_x17_mem pre_x18_mem pre_x19_mem
      pre_x20_mem pre_x21_mem pre_x22_mem pre_x23_mem pre_x24_mem pre_x25_mem
      pre_x26_mem pre_x27_mem pre_x28_mem pre_x29_mem pre_x30_mem pre_x31_mem)
Proof
 rw [bir_pre_riscv_to_bir_def] >-
   (rw [bspec_kernel_trap_return_pre_def] >>
    FULL_SIMP_TAC (std_ss++HolBASimps.bir_is_bool_ss) [bir_extra_expsTheory.BExp_Aligned_def] >>
    FULL_SIMP_TAC (std_ss++HolBASimps.bir_is_bool_ss) [bir_immTheory.n2bs_def]) >>

 Q.PAT_X_ASSUM `bir_env_vars_are_initialised x y` (fn thm => ALL_TAC) >>

 Cases_on `bs` >> Cases_on `b0` >>
  
 FULL_SIMP_TAC (std_ss) [riscv_kernel_trap_return_pre_def, bspec_kernel_trap_return_pre_def,bir_extra_expsTheory.BExp_Aligned_def] >>

 fs [GSYM bir_and_equiv] >>

 FULL_SIMP_TAC (std_ss++holBACore_ss) [
   bir_eval_bin_pred_def,
   riscv_bmr_rel_EVAL,
   bir_immTheory.bool2b_def,
   bir_immTheory.bool2w_def,
   bir_envTheory.bir_env_read_def,bir_envTheory.bir_env_lookup_def
 ] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 8w)) = SOME (Imm64 pre_mepc_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 16w)) = SOME (Imm64 pre_x1_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 24w)) = SOME (Imm64 pre_x2_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 32w)) = SOME (Imm64 pre_x3_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 40w)) = SOME (Imm64 pre_x4_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 48w)) = SOME (Imm64 pre_x5_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 56w)) = SOME (Imm64 pre_x6_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 64w)) = SOME (Imm64 pre_x7_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 72w)) = SOME (Imm64 pre_x8_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 80w)) = SOME (Imm64 pre_x9_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 88w)) = SOME (Imm64 pre_x10_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 96w)) = SOME (Imm64 pre_x11_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 104w)) = SOME (Imm64 pre_x12_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 112w)) = SOME (Imm64 pre_x13_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 120w)) = SOME (Imm64 pre_x14_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 128w)) = SOME (Imm64 pre_x15_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 136w)) = SOME (Imm64 pre_x16_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 144w)) = SOME (Imm64 pre_x17_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 152w)) = SOME (Imm64 pre_x18_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 160w)) = SOME (Imm64 pre_x19_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 168w)) = SOME (Imm64 pre_x20_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 176w)) = SOME (Imm64 pre_x21_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 184w)) = SOME (Imm64 pre_x22_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 192w)) = SOME (Imm64 pre_x23_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 200w)) = SOME (Imm64 pre_x24_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 208w)) = SOME (Imm64 pre_x25_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 216w)) = SOME (Imm64 pre_x26_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 224w)) = SOME (Imm64 pre_x27_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 232w)) = SOME (Imm64 pre_x28_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 240w)) = SOME (Imm64 pre_x29_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 248w)) = SOME (Imm64 pre_x30_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 `bir_load_from_mem Bit8 Bit64 Bit64 mem_n BEnd_LittleEndian (w2n (pre_x10 + 256w)) = SOME (Imm64 pre_x31_mem)`
  by METIS_TAC [riscv_mem_load_dword_bir_load_from_mem] >>

 rw [bir_eval_bin_pred_64_mem_eq] >>
 fs [riscv_mem_load_dword_bir_load_from_mem,bir_val_true_def]
QED

Theorem kernel_trap_return_riscv_post_imp_bspec_post_thm:
 !ls. bir_post_bir_to_riscv
   (riscv_kernel_trap_return_post pre_mscratch pre_x10 pre_mepc_mem pre_x1_mem
      pre_x2_mem pre_x3_mem pre_x4_mem pre_x5_mem pre_x6_mem pre_x7_mem
      pre_x8_mem pre_x9_mem pre_x10_mem pre_x11_mem pre_x12_mem pre_x13_mem
      pre_x14_mem pre_x15_mem pre_x16_mem pre_x17_mem pre_x18_mem pre_x19_mem
      pre_x20_mem pre_x21_mem pre_x22_mem pre_x23_mem pre_x24_mem pre_x25_mem
      pre_x26_mem pre_x27_mem pre_x28_mem pre_x29_mem pre_x30_mem pre_x31_mem)
   (\l. (bspec_kernel_trap_return_post pre_mscratch pre_x10 pre_mepc_mem pre_x1_mem
      pre_x2_mem pre_x3_mem pre_x4_mem pre_x5_mem pre_x6_mem pre_x7_mem
      pre_x8_mem pre_x9_mem pre_x10_mem pre_x11_mem pre_x12_mem pre_x13_mem
      pre_x14_mem pre_x15_mem pre_x16_mem pre_x17_mem pre_x18_mem pre_x19_mem
      pre_x20_mem pre_x21_mem pre_x22_mem pre_x23_mem pre_x24_mem pre_x25_mem
      pre_x26_mem pre_x27_mem pre_x28_mem pre_x29_mem pre_x30_mem pre_x31_mem))
   ls
Proof
 once_rewrite_tac [bir_post_bir_to_riscv_def,bspec_kernel_trap_return_post_def] >>
 once_rewrite_tac [bspec_kernel_trap_return_post_def] >>
 once_rewrite_tac [bspec_kernel_trap_return_post_def] >>

 fs [GSYM bir_and_equiv] >>

 Cases_on `bs` >>
 Cases_on `b0` >>
 FULL_SIMP_TAC (std_ss++holBACore_ss) [
  bir_envTheory.bir_env_read_def, bir_envTheory.bir_env_check_type_def,
  bir_envTheory.bir_env_lookup_type_def, bir_envTheory.bir_env_lookup_def,bir_eval_bin_pred_def
 ] >>

 rw [bir_eval_bin_pred_exists_64_eq] >>

 FULL_SIMP_TAC (std_ss++holBACore_ss) [
  riscv_kernel_trap_return_post_def,
  riscv_bmr_rel_EVAL,bir_envTheory.bir_env_read_def,
  bir_envTheory.bir_env_check_type_def, bir_envTheory.bir_env_lookup_type_def,
  bir_envTheory.bir_env_lookup_def,bir_eval_bin_pred_def
 ]
QED

val _ = export_theory ();
