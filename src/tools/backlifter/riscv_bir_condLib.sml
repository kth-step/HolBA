structure riscv_bir_condLib :> riscv_bir_condLib =
struct

open HolKernel boolLib Parse bossLib;

open bir_lifting_machinesTheory;
open riscv_bir_condTheory;

type riscv_bir_cond_result = bir_condLib.bir_cond_result

val procID_tm = ``riscv_state_procID``;
val MEM8_tm = ``riscv_state_MEM8``;
val load_dword_tm = ``bir_riscv_extras$riscv_mem_load_dword``;

(* riscv_mem_load_dword m.MEM8 a *)
fun dest_load m tm =
  case strip_comb tm of
    (f, [x, addr]) =>
      if same_const f load_dword_tm andalso aconv x (mk_comb (MEM8_tm, m))
      then SOME addr else NONE
  | _ => NONE;

val riscv_info : bir_condLib.arch_info =
  { arch = "riscv",
    state_ty = ``:riscv_state``,
    bmr = ``riscv_bmr``,
    bmr_lifted = riscv_bmr_LIFTED,
    dest_load = dest_load,
    pc_of = fn m => list_mk_comb (``riscv_state_c_PC``,
                                  [m, mk_comb (procID_tm, m)]),
    load_thms = [bir_riscv_extrasTheory.riscv_mem_load_dword_def],
    pre_lifted = bir_pre_riscv_to_bir_lifted,
    post_lifted = bir_post_bir_to_riscv_lifted,
    post_lifted_PC = bir_post_bir_to_riscv_lifted_PC,
    post_cases_nil = bir_post_bir_to_riscv_cases_nil,
    post_cases_cons = bir_post_bir_to_riscv_cases_cons };

val riscv_cond_to_bir = bir_condLib.cond_to_bir riscv_info;
val riscv_pre_to_bir = bir_condLib.pre_to_bir riscv_info;
val riscv_post_to_bir = bir_condLib.post_to_bir riscv_info;
val riscv_post_cases_to_bir = bir_condLib.post_cases_to_bir riscv_info;

end
