open HolKernel boolLib Parse bossLib;

open markerTheory;

open wordsTheory;

open bir_programSyntax bir_program_labelsTheory;
open bir_immTheory bir_valuesTheory bir_expTheory;
open bir_tsTheory bir_bool_expTheory bir_programTheory;
open bir_exp_equivTheory;

open bir_riscv_backlifterTheory;
open bir_backlifterLib;
open bir_riscv_extrasTheory;
open bir_compositionLib;

open bir_lifting_machinesTheory;
open bir_typing_expTheory;
open bir_htTheory;

open bir_smtLib;

open bir_symbTheory birs_auxTheory;
open HolBACoreSimps;
open bir_program_transfTheory;

open total_program_logicTheory;
open total_ext_program_logicTheory;
open symb_prop_transferTheory;

open jgmt_rel_bir_contTheory;

open pred_setTheory;

open program_logicSimps;

open bir_env_oldTheory;
open bir_program_varsTheory;

open isqrt_auxTheory;

val _ = new_theory "isqrt_spec_arm8";

(* ---------------- *)
(* Block boundaries *)
(* ---------------- *)

(* whole program *)

Definition isqrt_init_addr_def:
 isqrt_init_addr : word64 = 0x718w
End

Definition isqrt_end_addr_def:
 isqrt_end_addr : word64 = 0x734w
End

(* before loop *) 

Definition isqrt_init_addr_1_def:
 isqrt_init_addr_1 : word64 = 0x718w
End

Definition isqrt_end_addr_1_def:
 isqrt_end_addr_1 : word64 = 0x720w
End

(* loop body *)

Definition isqrt_init_addr_2_def:
 isqrt_init_addr_2 : word64 = 0x720w
End

Definition isqrt_end_addr_2_def:
 isqrt_end_addr_2 : word64 = 0x72cw
End

(* loop branch *)

Definition isqrt_init_addr_3_def:
 isqrt_init_addr_3 : word64 = 0x72cw
End

Definition isqrt_end_addr_3_loop_def:
 isqrt_end_addr_3_loop : word64 = 0x720w
End

Definition isqrt_end_addr_3_ret_def:
 isqrt_end_addr_3_ret : word64 = 0x734w
End

(* --------------- *)
(* ARMv8 contracts *)
(* --------------- *)

(* before loop contract *)

Definition arm8_isqrt_pre_1_def:
 arm8_isqrt_pre_1 (pre_x0:word64) (ms:arm8_state) : bool =
  (ms.REG 0w = pre_x0)
End

(* The postconditions of contracts 1 and 2 fix the PC to the end
   label, so that the contracts can also list the loop exit as an
   ending label that is never reached first, as needed for composition *)

Definition arm8_isqrt_post_1_def:
 arm8_isqrt_post_1 (pre_x0:word64) (ms:arm8_state) : bool =
  (ms.PC = isqrt_end_addr_1 /\
   ms.REG 1w = 0w /\
   ms.REG 3w = pre_x0)
End

(* loop body contract *)

Definition arm8_isqrt_pre_2_def:
 arm8_isqrt_pre_2 (pre_x1:word64) (pre_x3:word64) (ms:arm8_state) : bool =
  (ms.REG 1w = pre_x1 /\
   ms.REG 3w = pre_x3)
End

Definition arm8_isqrt_post_2_def:
 arm8_isqrt_post_2 (pre_x1:word64) (pre_x3:word64) (ms:arm8_state) : bool =
  (ms.PC = isqrt_end_addr_2 /\
   ms.REG 0w = pre_x1 /\
   ms.REG 1w = pre_x1 + 1w /\
   ms.REG 2w = (pre_x1 + 1w) * (pre_x1 + 1w) /\
   ms.REG 3w = pre_x3)
End

(* loop branch contract *)

Definition arm8_isqrt_pre_3_def:
 arm8_isqrt_pre_3 (pre_x0:word64) (pre_x1:word64) (pre_x2:word64)
  (pre_x3:word64) (ms:arm8_state) : bool =
  (ms.REG 0w = pre_x0 /\
   ms.REG 1w = pre_x1 /\
   ms.REG 2w = pre_x2 /\
   ms.REG 3w = pre_x3)
End

Definition arm8_isqrt_post_3_loop_def:
 arm8_isqrt_post_3_loop (pre_x0:word64) (pre_x1:word64) (pre_x2:word64)
  (pre_x3:word64) (ms:arm8_state) : bool =
  (ms.REG 0w = pre_x0 /\
   ms.REG 1w = pre_x1 /\
   ms.REG 2w = pre_x2 /\
   ms.REG 3w = pre_x3 /\
   pre_x2 <=+ pre_x3)
End

Definition arm8_isqrt_post_3_ret_def:
 arm8_isqrt_post_3_ret (pre_x0:word64) (pre_x1:word64) (pre_x2:word64)
  (pre_x3:word64) (ms:arm8_state) : bool =
  (ms.REG 0w = pre_x0 /\
   ms.REG 1w = pre_x1 /\
   ms.REG 2w = pre_x2 /\
   ms.REG 3w = pre_x3 /\
   pre_x3 <+ pre_x2)
End

Definition arm8_isqrt_post_3_def:
 arm8_isqrt_post_3 (pre_x0:word64) (pre_x1:word64) (pre_x2:word64)
  (pre_x3:word64) (ms:arm8_state) : bool =
  if ms.PC = isqrt_end_addr_3_loop then
    arm8_isqrt_post_3_loop pre_x0 pre_x1 pre_x2 pre_x3 ms
  else if ms.PC = isqrt_end_addr_3_ret then
    arm8_isqrt_post_3_ret pre_x0 pre_x1 pre_x2 pre_x3 ms
  else F
End

(* ----------------------- *)
(* Whole program contract  *)
(* ----------------------- *)

(*
   Starting at 0x718 with x0 = n, execution reaches the ret
   instruction at 0x734 with x0 = floor(sqrt(n)).

   The bound on n is needed for termination: the loop exits when
   x3 <+ (x1 * x1) in 64-bit arithmetic, so for n = (2^32 - 1)^2 the
   multiplication wraps at x1 = 2^32 (x2 = 0w) and the program loops
   forever (as does isqrt.c, since uint64_t arithmetic wraps). Below
   the bound, (x1 + 1)^2 never overflows (see isqrt_w2n_sq). *)

Definition arm8_isqrt_pre_def:
 arm8_isqrt_pre (pre_x0:word64) (ms:arm8_state) : bool =
  (ms.REG 0w = pre_x0 /\
   pre_x0 <+ 0xFFFFFFFE00000001w)
End

(* 0xFFFFFFFE00000001w = (2^32 - 1)^2. The bound on x0 rules out
   wrapped-around solutions such as x0 = 2^32 for pre_x0 = 5w *)
Definition arm8_isqrt_post_def:
 arm8_isqrt_post (pre_x0:word64) (ms:arm8_state) : bool =
  (ms.REG 0w <+ 0xFFFFFFFFw /\
   ms.REG 0w * ms.REG 0w <=+ pre_x0 /\
   pre_x0 <+ (ms.REG 0w + 1w) * (ms.REG 0w + 1w))
End

(* Validation: under the precondition bound, the postcondition says
   exactly x0 = ROOT 2 n *)

Theorem arm8_isqrt_post_ROOT:
 !pre_x0 ms.
  pre_x0 <+ 0xFFFFFFFE00000001w ==>
  (arm8_isqrt_post pre_x0 ms <=> w2n (ms.REG 0w) = ROOT 2 (w2n pre_x0))
Proof
 rpt strip_tac >>
 rw [arm8_isqrt_post_def, GSYM isqrt_ROOT_nat] >>
 Cases_on `w2n (ms.REG 0w) < 4294967295` >- (
  fs [WORD_LO, WORD_LS, isqrt_w2n_sq]
 ) >>
 fs [WORD_LO] >> disj1_tac >>
 qspecl_then [`4294967295`, `w2n (ms.REG 0w)`] mp_tac isqrt_sq_mono >>
 simp []
QED

(* Loop ingredients for proving the whole program contract from the
   three piece contracts with total_loop_rule_thm, using loop head
   isqrt_init_addr_2 (0x720) and exit set {isqrt_end_addr} (0x734):

   - contract 1 (with conseq) establishes arm8_isqrt_inv at 0x720
   - iteration: contract 2 then contract 3 (loop exit) from 0x720 back
     to 0x720 under inv /\ cond, decreasing the variant
   - exit: contract 2 then contract 3 (ret exit) from 0x720 to 0x734
     under inv /\ ~cond, establishing arm8_isqrt_post *)

Definition arm8_isqrt_inv_def:
 arm8_isqrt_inv (pre_x0:word64) (ms:arm8_state) : bool =
  (ms.REG 3w = pre_x0 /\
   pre_x0 <+ 0xFFFFFFFE00000001w /\
   ms.REG 1w <+ 0xFFFFFFFFw /\
   ms.REG 1w * ms.REG 1w <=+ pre_x0)
End

(* Checked at the loop head, where the body has not yet computed x2 *)
Definition arm8_isqrt_cond_def:
 arm8_isqrt_cond (ms:arm8_state) : bool =
  ((ms.REG 1w + 1w) * (ms.REG 1w + 1w) <=+ ms.REG 3w)
End

(* Decreases w.r.t. $< *)
Definition arm8_isqrt_variant_def:
 arm8_isqrt_variant (ms:arm8_state) : num =
  w2n (ms.REG 3w) - w2n (ms.REG 1w)
End

val _ = export_theory ();
