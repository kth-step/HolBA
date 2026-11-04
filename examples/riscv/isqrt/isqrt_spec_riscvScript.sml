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

val _ = new_theory "isqrt_spec_riscv";

(* ---------------- *)
(* Block boundaries *)
(* ---------------- *)

(* whole program *)

Definition isqrt_init_addr_def:
 isqrt_init_addr : word64 = 0x10488w
End

Definition isqrt_end_addr_def:
 isqrt_end_addr : word64 = 0x104a0w
End

(* before loop *) 

Definition isqrt_init_addr_1_def:
 isqrt_init_addr_1 : word64 = 0x10488w
End

Definition isqrt_end_addr_1_def:
 isqrt_end_addr_1 : word64 = 0x10490w
End

(* loop body *)

Definition isqrt_init_addr_2_def:
 isqrt_init_addr_2 : word64 = 0x10490w
End

Definition isqrt_end_addr_2_def:
 isqrt_end_addr_2 : word64 = 0x1049cw
End

(* loop branch *)

Definition isqrt_init_addr_3_def:
 isqrt_init_addr_3 : word64 = 0x1049cw
End

Definition isqrt_end_addr_3_loop_def:
 isqrt_end_addr_3_loop : word64 = 0x10490w
End

Definition isqrt_end_addr_3_ret_def:
 isqrt_end_addr_3_ret : word64 = 0x104a0w
End

(* ---------------- *)
(* RISC-V contracts *)
(* ---------------- *)

(* before loop contract *)

Definition riscv_isqrt_pre_1_def:
 riscv_isqrt_pre_1 (pre_x10:word64) (m:riscv_state) : bool =
  (m.c_gpr m.procID 10w = pre_x10)
End

(* The postconditions of contracts 1 and 2 fix the PC to the end
   label, so that the contracts can also list the loop exit as an
   ending label that is never reached first, as needed for composition *)

Definition riscv_isqrt_post_1_def:
 riscv_isqrt_post_1 (pre_x10:word64) (m:riscv_state) : bool =
  (m.c_PC m.procID = isqrt_end_addr_1 /\
   m.c_gpr m.procID 13w = pre_x10 /\
   m.c_gpr m.procID 15w = 0w)
End

(* loop body contract *)

Definition riscv_isqrt_pre_2_def:
 riscv_isqrt_pre_2 (pre_x13:word64) (pre_x15:word64) (m:riscv_state) : bool =
  (m.c_gpr m.procID 13w = pre_x13 /\
   m.c_gpr m.procID 15w = pre_x15)
End

Definition riscv_isqrt_post_2_def:
 riscv_isqrt_post_2 (pre_x13:word64) (pre_x15:word64) (m:riscv_state) : bool =
  (m.c_PC m.procID = isqrt_end_addr_2 /\
   m.c_gpr m.procID 10w = pre_x15 /\
   m.c_gpr m.procID 13w = pre_x13 /\
   m.c_gpr m.procID 14w = (pre_x15 + 1w) * (pre_x15 + 1w) /\
   m.c_gpr m.procID 15w = pre_x15 + 1w)
End

(* loop branch contract *)

(* The counter x15 is not used by the branch, but is needed
   to reestablish the loop invariant after an iteration *)

Definition riscv_isqrt_pre_3_def:
 riscv_isqrt_pre_3 (pre_x10:word64) (pre_x13:word64)
  (pre_x14:word64) (pre_x15:word64) (m:riscv_state) : bool =
  (m.c_gpr m.procID 10w = pre_x10 /\
   m.c_gpr m.procID 13w = pre_x13 /\
   m.c_gpr m.procID 14w = pre_x14 /\
   m.c_gpr m.procID 15w = pre_x15)
End

Definition riscv_isqrt_post_3_loop_def:
 riscv_isqrt_post_3_loop (pre_x10:word64) (pre_x13:word64)
  (pre_x14:word64) (pre_x15:word64) (m:riscv_state) : bool =
  (m.c_gpr m.procID 10w = pre_x10 /\
   m.c_gpr m.procID 13w = pre_x13 /\
   m.c_gpr m.procID 14w = pre_x14 /\
   m.c_gpr m.procID 15w = pre_x15 /\
   pre_x14 <=+ pre_x13)
End

Definition riscv_isqrt_post_3_ret_def:
 riscv_isqrt_post_3_ret (pre_x10:word64) (pre_x13:word64)
  (pre_x14:word64) (pre_x15:word64) (m:riscv_state) : bool =
  (m.c_gpr m.procID 10w = pre_x10 /\
   m.c_gpr m.procID 13w = pre_x13 /\
   m.c_gpr m.procID 14w = pre_x14 /\
   m.c_gpr m.procID 15w = pre_x15 /\
   pre_x13 <+ pre_x14)
End

Definition riscv_isqrt_post_3_def:
 riscv_isqrt_post_3 (pre_x10:word64) (pre_x13:word64)
  (pre_x14:word64) (pre_x15:word64) (m:riscv_state) : bool =
  if m.c_PC m.procID = isqrt_end_addr_3_loop then
    riscv_isqrt_post_3_loop pre_x10 pre_x13 pre_x14 pre_x15 m
  else if m.c_PC m.procID = isqrt_end_addr_3_ret then
    riscv_isqrt_post_3_ret pre_x10 pre_x13 pre_x14 pre_x15 m
  else F
End

(* ----------------------- *)
(* Whole program contract  *)
(* ----------------------- *)

(*
   Starting at 0x10488 with x10 = n, execution reaches the ret
   instruction at 0x104a0 with x10 = floor(sqrt(n)).

   The bound on n is needed for termination: the loop exits when
   x13 <+ (x15 * x15) in 64-bit arithmetic, so for n = (2^32 - 1)^2 the
   multiplication wraps at x15 = 2^32 (x14 = 0w) and the program loops
   forever (as does isqrt.c, since uint64_t arithmetic wraps). Below
   the bound, (x15 + 1)^2 never overflows (see isqrt_w2n_sq). *)

Definition riscv_isqrt_pre_def:
 riscv_isqrt_pre (pre_x10:word64) (m:riscv_state) : bool =
  (m.c_gpr m.procID 10w = pre_x10 /\
   pre_x10 <+ 0xFFFFFFFE00000001w)
End

(* 0xFFFFFFFE00000001w = (2^32 - 1)^2. The bound on x10 rules out
   wrapped-around solutions such as x10 = 2^32 for pre_x10 = 5w *)
Definition riscv_isqrt_post_def:
 riscv_isqrt_post (pre_x10:word64) (m:riscv_state) : bool =
  (m.c_gpr m.procID 10w <+ 0xFFFFFFFFw /\
   m.c_gpr m.procID 10w * m.c_gpr m.procID 10w <=+ pre_x10 /\
   pre_x10 <+ (m.c_gpr m.procID 10w + 1w) * (m.c_gpr m.procID 10w + 1w))
End

(* Validation: under the precondition bound, the postcondition says
   exactly x10 = ROOT 2 n *)

Theorem riscv_isqrt_post_ROOT:
 !pre_x10 m.
  pre_x10 <+ 0xFFFFFFFE00000001w ==>
  (riscv_isqrt_post pre_x10 m <=> w2n (m.c_gpr m.procID 10w) = ROOT 2 (w2n pre_x10))
Proof
 rpt strip_tac >>
 rw [riscv_isqrt_post_def, GSYM isqrt_ROOT_nat] >>
 Cases_on `w2n (m.c_gpr m.procID 10w) < 4294967295` >- (
  fs [WORD_LO, WORD_LS, isqrt_w2n_sq]
 ) >>
 fs [WORD_LO] >> disj1_tac >>
 qspecl_then [`4294967295`, `w2n (m.c_gpr m.procID 10w)`] mp_tac isqrt_sq_mono >>
 simp []
QED

(* Loop ingredients for proving the whole program contract from the
   three piece contracts with riscv_cont_loop_rule, using loop head
   isqrt_init_addr_2 (0x10490) and exit set {isqrt_end_addr} (0x104a0):

   - contract 1 (with conseq) establishes riscv_isqrt_inv at 0x10490
   - iteration: contract 2 then contract 3 (loop exit) from 0x10490 back
     to 0x10490 under inv /\ cond, decreasing the variant
   - exit: contract 2 then contract 3 (ret exit) from 0x10490 to 0x104a0
     under inv /\ ~cond, establishing riscv_isqrt_post *)

Definition riscv_isqrt_inv_def:
 riscv_isqrt_inv (pre_x10:word64) (m:riscv_state) : bool =
  (m.c_gpr m.procID 13w = pre_x10 /\
   pre_x10 <+ 0xFFFFFFFE00000001w /\
   m.c_gpr m.procID 15w <+ 0xFFFFFFFFw /\
   m.c_gpr m.procID 15w * m.c_gpr m.procID 15w <=+ pre_x10)
End

(* Checked at the loop head, where the body has not yet computed x14 *)
Definition riscv_isqrt_cond_def:
 riscv_isqrt_cond (m:riscv_state) : bool =
  ((m.c_gpr m.procID 15w + 1w) * (m.c_gpr m.procID 15w + 1w) <=+ m.c_gpr m.procID 13w)
End

(* Decreases w.r.t. $< *)
Definition riscv_isqrt_variant_def:
 riscv_isqrt_variant (m:riscv_state) : num =
  w2n (m.c_gpr m.procID 13w) - w2n (m.c_gpr m.procID 15w)
End

val _ = export_theory ();
