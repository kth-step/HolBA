structure arm8_bir_condLib :> arm8_bir_condLib =
struct

open HolKernel boolLib Parse bossLib;

open bir_lifting_machinesTheory;
open arm8_bir_condTheory;

type arm8_bir_cond_result = bir_condLib.bir_cond_result

val REG_tm = ``arm8_state_REG``;
val MEM_tm = ``arm8_state_MEM``;
val load_64_tm = ``bir_arm8_backlifter$arm8_load_64``;

(* m.REG k *)
fun dest_reg m tm =
  case strip_comb tm of
    (f, [x, k]) =>
      if same_const f REG_tm andalso aconv x m then SOME k else NONE
  | _ => NONE;

(* arm8_load_64 m.MEM a *)
fun dest_load m tm =
  case strip_comb tm of
    (f, [x, addr]) =>
      if same_const f load_64_tm andalso aconv x (mk_comb (MEM_tm, m))
      then SOME addr else NONE
  | _ => NONE;

val arm8_info : bir_condLib.arch_info =
  { arch = "arm8",
    state_ty = ``:arm8_state``,
    bmr = ``arm8_bmr``,
    bmr_lifted = arm8_bmr_LIFTED,
    dest_reg = dest_reg,
    dest_load = dest_load,
    pc_of = fn m => mk_comb (``arm8_state_PC``, m),
    (* the lowest byte at a, not a + 0w *)
    load_thms = [REWRITE_RULE [wordsTheory.WORD_ADD_0]
                   bir_arm8_backlifterTheory.arm8_load_64_def],
    pre_lifted = bir_pre_arm8_to_bir_lifted,
    post_lifted = bir_post_bir_to_arm8_lifted,
    post_lifted_PC = bir_post_bir_to_arm8_lifted_PC,
    post_cases_nil = bir_post_bir_to_arm8_cases_nil,
    post_cases_cons = bir_post_bir_to_arm8_cases_cons };

val arm8_cond_to_bir = bir_condLib.cond_to_bir arm8_info;
val arm8_pre_to_bir = bir_condLib.pre_to_bir arm8_info;
val arm8_post_to_bir = bir_condLib.post_to_bir arm8_info;
val arm8_post_cases_to_bir = bir_condLib.post_cases_to_bir arm8_info;

end
