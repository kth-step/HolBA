open HolKernel Parse boolLib bossLib;

(* FIXME: avoid quse errors *)
open m0_stepLib;

open bir_immTheory;
open bir_programTheory;
open bir_tsTheory;
open bir_program_multistep_propsTheory;
open bir_auxiliaryTheory;

(* From lifter: *)
open bir_inst_liftingTheory;
open bir_lifting_machinesTheory;

(* From comp: *)
open total_program_logicTheory;
open total_ext_program_logicTheory;

open HolBASimps;
open HolBACoreSimps;
open program_logicSimps;

open bir_auxiliaryLib;

open m0_mod_stepLib;

open bir_riscv_extrasTheory;

val _ = new_theory "bir_riscv_backlifter";

(* FIXME: procID must never change *)
Definition riscv_weak_trs_def:
 riscv_weak_trs ls ms ms' = 
  ?n.
    ((n > 0) /\
     (FUNPOW_OPT riscv_bmr.bmr_step_fun n ms = SOME ms') /\
     ((ms'.c_PC ms'.procID) IN ls))
    /\
    !n'. (((n' < n) /\ (n' > 0)) ==>
          ?ms''.
            (FUNPOW_OPT riscv_bmr.bmr_step_fun n' ms = SOME ms'') /\
            (~((ms''.c_PC ms''.procID) IN ls)))
End

Definition riscv_ts_def:
 riscv_ts  = <|
    trs  := riscv_bmr.bmr_step_fun;
    weak := riscv_weak_trs;
    ctrl := (\st. (st.c_PC st.procID))
  |>
End

(* The main contract to be used for RISC-V composition *)
(* FIXME: generalize for both arm8 and riscv *)
Definition riscv_cont_def:
 riscv_cont mms l ls pre post =
    t_jgmt riscv_ts l ls
      (\ms. (riscv_bmr.bmr_extra ms)  /\
            (EVERY (bmr_ms_mem_contains riscv_bmr ms) mms) /\
            (pre ms))
      (\ms. (riscv_bmr.bmr_extra ms)  /\
            (EVERY (bmr_ms_mem_contains riscv_bmr ms) mms) /\
            (post ms))
End

(* FIXME: generalize for both arm8 and riscv *)
Definition bir_pre_riscv_to_bir_def:
  bir_pre_riscv_to_bir pre pre_bir = (
    bir_is_bool_exp pre_bir /\
    !ms bs.
    bmr_rel riscv_bmr bs ms ==>
    bir_env_vars_are_initialised bs.bst_environ (bir_vars_of_exp pre_bir) ==>
    pre ms ==>
    (bir_eval_exp pre_bir bs.bst_environ = SOME bir_val_true))
End

(* FIXME: generalize for both arm8 and riscv *)
Definition bir_post_bir_to_riscv_def:
  bir_post_bir_to_riscv post post_bir ls =
    !ms bs l.
    l IN ls ==>
    bmr_rel riscv_bmr bs ms ==>
    (bir_eval_exp (post_bir l) bs.bst_environ = SOME bir_val_true) ==>
    post ms
End

Theorem bload_64_to_riscv_load_64_thm:
 !bs ms. (bmr_rel riscv_bmr bs ms) ==>
    (!a.
       ((bir_eval_load
         (bir_env_read (BVar "MEM8" (BType_Mem Bit64 Bit8)) bs.bst_environ)
         (SOME (BVal_Imm (Imm64 a))) BEnd_LittleEndian Bit64) =
        SOME (BVal_Imm (Imm64 (riscv_mem_load_dword ms.MEM8 a)))))
Proof
REPEAT STRIP_TAC >>
Q.SUBGOAL_THEN
  `?mem_n.
   (bir_env_read (BVar "MEM8" (BType_Mem Bit64 Bit8)) bs.bst_environ =
     (SOME (BVal_Mem Bit64 Bit8 mem_n))) /\
   (ms.MEM8 = (\a. n2w (bir_load_mmap mem_n (w2n a)))) /\
   bir_env_var_is_declared bs.bst_environ
     (BVar "tmp_MEM8" (BType_Mem Bit64 Bit8))` ASSUME_TAC >-(
  FULL_SIMP_TAC std_ss [bir_lifting_machinesTheory.riscv_bmr_rel_EVAL] >>
  EXISTS_TAC ``mem_n:num|->num`` >>
  FULL_SIMP_TAC std_ss []
) >>
FULL_SIMP_TAC std_ss [bir_expTheory.bir_eval_load_FULL_REWRS, riscv_mem_load_dword_def] >>
FULL_SIMP_TAC (srw_ss()) []
QED

Theorem bool2w_and[local]:
 !a b. ((bool2w a) && (bool2w b)) = (bool2w (a /\ b))
Proof
REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bool2w_def] >>
Cases_on `a` >>
Cases_on `b` >>
EVAL_TAC
QED

Theorem imm_eq_to_val_eq[local]:
 !a b . ((BVal_Imm(Imm1 a)) = (BVal_Imm(Imm1 b))) = (a = b)
Proof
REPEAT STRIP_TAC >> EVAL_TAC
QED

(* TODO: handle floating-point registers *)
Definition riscv_vars_def:
 riscv_vars = {
  (BVar "x0" (BType_Imm Bit64));
  (BVar "tmp_x0" (BType_Imm Bit64));
  (BVar "x1" (BType_Imm Bit64));
  (BVar "tmp_x1" (BType_Imm Bit64));
  (BVar "x2" (BType_Imm Bit64));
  (BVar "tmp_x2" (BType_Imm Bit64));
  (BVar "x3" (BType_Imm Bit64));
  (BVar "tmp_x3" (BType_Imm Bit64));
  (BVar "x4" (BType_Imm Bit64));
  (BVar "tmp_x4" (BType_Imm Bit64));
  (BVar "x5" (BType_Imm Bit64));
  (BVar "tmp_x5" (BType_Imm Bit64));
  (BVar "x6" (BType_Imm Bit64));
  (BVar "tmp_x6" (BType_Imm Bit64));
  (BVar "x7" (BType_Imm Bit64));
  (BVar "tmp_x7" (BType_Imm Bit64));
  (BVar "x8" (BType_Imm Bit64));
  (BVar "tmp_x8" (BType_Imm Bit64));
  (BVar "x9" (BType_Imm Bit64));
  (BVar "tmp_x9" (BType_Imm Bit64));
  (BVar "x10" (BType_Imm Bit64));
  (BVar "tmp_x10" (BType_Imm Bit64));
  (BVar "x11" (BType_Imm Bit64));
  (BVar "tmp_x11" (BType_Imm Bit64));
  (BVar "x12" (BType_Imm Bit64));
  (BVar "tmp_x12" (BType_Imm Bit64));
  (BVar "x13" (BType_Imm Bit64));
  (BVar "tmp_x13" (BType_Imm Bit64));
  (BVar "x14" (BType_Imm Bit64));
  (BVar "tmp_x14" (BType_Imm Bit64));
  (BVar "x15" (BType_Imm Bit64));
  (BVar "tmp_x15" (BType_Imm Bit64));
  (BVar "x16" (BType_Imm Bit64));
  (BVar "tmp_x16" (BType_Imm Bit64));
  (BVar "x17" (BType_Imm Bit64));
  (BVar "tmp_x17" (BType_Imm Bit64));
  (BVar "x18" (BType_Imm Bit64));
  (BVar "tmp_x18" (BType_Imm Bit64));
  (BVar "x19" (BType_Imm Bit64));
  (BVar "tmp_x19" (BType_Imm Bit64));
  (BVar "x20" (BType_Imm Bit64));
  (BVar "tmp_x20" (BType_Imm Bit64));
  (BVar "x21" (BType_Imm Bit64));
  (BVar "tmp_x21" (BType_Imm Bit64));
  (BVar "x22" (BType_Imm Bit64));
  (BVar "tmp_x22" (BType_Imm Bit64));
  (BVar "x23" (BType_Imm Bit64));
  (BVar "tmp_x23" (BType_Imm Bit64));
  (BVar "x24" (BType_Imm Bit64));
  (BVar "tmp_x24" (BType_Imm Bit64));
  (BVar "x25" (BType_Imm Bit64));
  (BVar "tmp_x25" (BType_Imm Bit64));
  (BVar "x26" (BType_Imm Bit64));
  (BVar "tmp_x26" (BType_Imm Bit64));
  (BVar "x27" (BType_Imm Bit64));
  (BVar "tmp_x27" (BType_Imm Bit64));
  (BVar "x28" (BType_Imm Bit64));
  (BVar "tmp_x28" (BType_Imm Bit64));
  (BVar "x29" (BType_Imm Bit64));
  (BVar "tmp_x29" (BType_Imm Bit64));
  (BVar "x30" (BType_Imm Bit64));
  (BVar "tmp_x30" (BType_Imm Bit64));
  (BVar "x31" (BType_Imm Bit64));
  (BVar "tmp_x31" (BType_Imm Bit64));

  (BVar "f0" (BType_Imm Bit64));
  (BVar "tmp_f0" (BType_Imm Bit64));
  (BVar "f1" (BType_Imm Bit64));
  (BVar "tmp_f1" (BType_Imm Bit64));
  (BVar "f2" (BType_Imm Bit64));
  (BVar "tmp_f2" (BType_Imm Bit64));
  (BVar "f3" (BType_Imm Bit64));
  (BVar "tmp_f3" (BType_Imm Bit64));
  (BVar "f4" (BType_Imm Bit64));
  (BVar "tmp_f4" (BType_Imm Bit64));
  (BVar "f5" (BType_Imm Bit64));
  (BVar "tmp_f5" (BType_Imm Bit64));
  (BVar "f6" (BType_Imm Bit64));
  (BVar "tmp_f6" (BType_Imm Bit64));
  (BVar "f7" (BType_Imm Bit64));
  (BVar "tmp_f7" (BType_Imm Bit64));
  (BVar "f8" (BType_Imm Bit64));
  (BVar "tmp_f8" (BType_Imm Bit64));
  (BVar "f9" (BType_Imm Bit64));
  (BVar "tmp_f9" (BType_Imm Bit64));
  (BVar "f10" (BType_Imm Bit64));
  (BVar "tmp_f10" (BType_Imm Bit64));
  (BVar "f11" (BType_Imm Bit64));
  (BVar "tmp_f11" (BType_Imm Bit64));
  (BVar "f12" (BType_Imm Bit64));
  (BVar "tmp_f12" (BType_Imm Bit64));
  (BVar "f13" (BType_Imm Bit64));
  (BVar "tmp_f13" (BType_Imm Bit64));
  (BVar "f14" (BType_Imm Bit64));
  (BVar "tmp_f14" (BType_Imm Bit64));
  (BVar "f15" (BType_Imm Bit64));
  (BVar "tmp_f15" (BType_Imm Bit64));
  (BVar "f16" (BType_Imm Bit64));
  (BVar "tmp_f16" (BType_Imm Bit64));
  (BVar "f17" (BType_Imm Bit64));
  (BVar "tmp_f17" (BType_Imm Bit64));
  (BVar "f18" (BType_Imm Bit64));
  (BVar "tmp_f18" (BType_Imm Bit64));
  (BVar "f19" (BType_Imm Bit64));
  (BVar "tmp_f19" (BType_Imm Bit64));
  (BVar "f20" (BType_Imm Bit64));
  (BVar "tmp_f20" (BType_Imm Bit64));
  (BVar "f21" (BType_Imm Bit64));
  (BVar "tmp_f21" (BType_Imm Bit64));
  (BVar "f22" (BType_Imm Bit64));
  (BVar "tmp_f22" (BType_Imm Bit64));
  (BVar "f23" (BType_Imm Bit64));
  (BVar "tmp_f23" (BType_Imm Bit64));
  (BVar "f24" (BType_Imm Bit64));
  (BVar "tmp_f24" (BType_Imm Bit64));
  (BVar "f25" (BType_Imm Bit64));
  (BVar "tmp_f25" (BType_Imm Bit64));
  (BVar "f26" (BType_Imm Bit64));
  (BVar "tmp_f26" (BType_Imm Bit64));
  (BVar "f27" (BType_Imm Bit64));
  (BVar "tmp_f27" (BType_Imm Bit64));
  (BVar "f28" (BType_Imm Bit64));
  (BVar "tmp_f28" (BType_Imm Bit64));
  (BVar "f29" (BType_Imm Bit64));
  (BVar "tmp_f29" (BType_Imm Bit64));
  (BVar "f30" (BType_Imm Bit64));
  (BVar "tmp_f30" (BType_Imm Bit64));
  (BVar "f31" (BType_Imm Bit64));
  (BVar "tmp_f31" (BType_Imm Bit64));

  (BVar "MEM8" (BType_Mem Bit64 Bit8));
  (BVar "tmp_MEM8" (BType_Mem Bit64 Bit8));

  (BVar "tmp_PC" (BType_Imm Bit64));
  (BVar "tmp_COND" (BType_Imm Bit1))
 }
End

Definition riscv_wf_varset_def:
 riscv_wf_varset vset = (vset SUBSET riscv_vars)
End

Definition default_riscv_bir_state_def:
 default_riscv_bir_state ms =
  <| bst_pc := bir_block_pc (BL_Address (Imm64 (ms.c_PC ms.procID))) ;
     bst_environ := BEnv (
       ("x0"        =+ SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 0w))))
       (("tmp_x0"   =+ SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 0w))))
       (("x1"       =+ SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 1w))))
       (("tmp_x1"   =+ SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 1w))))
       (("x2"       =+ SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 2w))))
       (("tmp_x2"   =+ SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 2w))))
       (("x3"       =+ SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 3w))))
       (("tmp_x3"   =+ SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 3w))))
       (("x4"       =+ SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 4w))))
       (("tmp_x4"   =+ SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 4w))))
       (("x5"       =+ SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 5w))))
       (("tmp_x5"   =+ SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 5w))))
       (("x6"       =+ SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 6w))))
       (("tmp_x6"   =+ SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 6w))))
       (("x7"       =+ SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 7w))))
       (("tmp_x7"   =+ SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 7w))))
       (("x8"       =+ SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 8w))))
       (("tmp_x8"   =+ SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 8w))))
       (("x9"       =+ SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 9w))))
       (("tmp_x9"   =+ SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 9w))))
       (("x10"      =+ SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 10w))))
       (("tmp_x10"  =+ SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 10w))))
       (("x11"      =+ SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 11w))))
       (("tmp_x11"  =+ SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 11w))))
       (("x12"      =+ SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 12w))))
       (("tmp_x12"  =+ SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 12w))))
       (("x13"      =+ SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 13w))))
       (("tmp_x13"  =+ SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 13w))))
       (("x14"      =+ SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 14w))))
       (("tmp_x14"  =+ SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 14w))))
       (("x15"      =+ SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 15w))))
       (("tmp_x15"  =+ SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 15w))))
       (("x16"      =+ SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 16w))))
       (("tmp_x16"  =+ SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 16w))))
       (("x17"      =+ SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 17w))))
       (("tmp_x17"  =+ SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 17w))))
       (("x18"      =+ SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 18w))))
       (("tmp_x18"  =+ SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 18w))))
       (("x19"      =+ SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 19w))))
       (("tmp_x19"  =+ SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 19w))))
       (("x20"      =+ SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 20w))))
       (("tmp_x20"  =+ SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 20w))))
       (("x21"      =+ SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 21w))))
       (("tmp_x21"  =+ SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 21w))))
       (("x22"      =+ SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 22w))))
       (("tmp_x22"  =+ SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 22w))))
       (("x23"      =+ SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 23w))))
       (("tmp_x23"  =+ SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 23w))))
       (("x24"      =+ SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 24w))))
       (("tmp_x24"  =+ SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 24w))))
       (("x25"      =+ SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 25w))))
       (("tmp_x25"  =+ SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 25w))))
       (("x26"      =+ SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 26w))))
       (("tmp_x26"  =+ SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 26w))))
       (("x27"      =+ SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 27w))))
       (("tmp_x27"  =+ SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 27w))))
       (("x28"      =+ SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 28w))))
       (("tmp_x28"  =+ SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 28w))))
       (("x29"      =+ SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 29w))))
       (("tmp_x29"  =+ SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 29w))))
       (("x30"      =+ SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 30w))))
       (("tmp_x30"  =+ SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 30w))))
       (("x31"      =+ SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 31w))))
       (("tmp_x31"  =+ SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 31w))))

       (("f0"       =+ SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 0w))))
       (("tmp_f0"   =+ SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 0w))))
       (("f1"       =+ SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 1w))))
       (("tmp_f1"   =+ SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 1w))))
       (("f2"       =+ SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 2w))))
       (("tmp_f2"   =+ SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 2w))))
       (("f3"       =+ SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 3w))))
       (("tmp_f3"   =+ SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 3w))))
       (("f4"       =+ SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 4w))))
       (("tmp_f4"   =+ SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 4w))))
       (("f5"       =+ SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 5w))))
       (("tmp_f5"   =+ SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 5w))))
       (("f6"       =+ SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 6w))))
       (("tmp_f6"   =+ SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 6w))))
       (("f7"       =+ SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 7w))))
       (("tmp_f7"   =+ SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 7w))))
       (("f8"       =+ SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 8w))))
       (("tmp_f8"   =+ SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 8w))))
       (("f9"       =+ SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 9w))))
       (("tmp_f9"   =+ SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 9w))))
       (("f10"      =+ SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 10w))))
       (("tmp_f10"  =+ SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 10w))))
       (("f11"      =+ SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 11w))))
       (("tmp_f11"  =+ SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 11w))))
       (("f12"      =+ SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 12w))))
       (("tmp_f12"  =+ SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 12w))))
       (("f13"      =+ SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 13w))))
       (("tmp_f13"  =+ SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 13w))))
       (("f14"      =+ SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 14w))))
       (("tmp_x14"  =+ SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 14w))))
       (("f15"      =+ SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 15w))))
       (("tmp_f15"  =+ SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 15w))))
       (("f16"      =+ SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 16w))))
       (("tmp_f16"  =+ SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 16w))))
       (("f17"      =+ SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 17w))))
       (("tmp_f17"  =+ SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 17w))))
       (("f18"      =+ SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 18w))))
       (("tmp_f18"  =+ SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 18w))))
       (("f19"      =+ SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 19w))))
       (("tmp_f19"  =+ SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 19w))))
       (("f20"      =+ SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 20w))))
       (("tmp_f20"  =+ SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 20w))))
       (("f21"      =+ SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 21w))))
       (("tmp_f21"  =+ SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 21w))))
       (("f22"      =+ SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 22w))))
       (("tmp_f22"  =+ SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 22w))))
       (("f23"      =+ SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 23w))))
       (("tmp_f23"  =+ SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 23w))))
       (("f24"      =+ SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 24w))))
       (("tmp_f24"  =+ SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 24w))))
       (("f25"      =+ SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 25w))))
       (("tmp_f25"  =+ SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 25w))))
       (("f26"      =+ SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 26w))))
       (("tmp_f26"  =+ SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 26w))))
       (("f27"      =+ SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 27w))))
       (("tmp_f27"  =+ SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 27w))))
       (("f28"      =+ SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 28w))))
       (("tmp_f28"  =+ SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 28w))))
       (("f29"      =+ SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 29w))))
       (("tmp_f29"  =+ SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 29w))))
       (("f30"      =+ SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 30w))))
       (("tmp_f30"  =+ SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 30w))))
       (("f31"      =+ SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 31w))))
       (("tmp_f31"  =+ SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 31w))))

       (("MEM8"     =+ SOME (BVal_Mem Bit64 Bit8 (bir_mmap_w_w2n (bir_mf2mm ms.MEM8))))
       (("tmp_MEM8" =+ SOME (BVal_Mem Bit64 Bit8 (bir_mmap_w_w2n (bir_mf2mm ms.MEM8))))

       (("tmp_PC"   =+ SOME (BVal_Imm (Imm64 (ms.c_PC ms.procID))))
       (("tmp_COND" =+ SOME(BVal_Imm (Imm1 0w))) bir_env_map_empty))))
        ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
        )))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
     );
     bst_status := BST_Running
   |>
End

(*

Theorem default_riscv_bir_state_satisfies_rel_thm[local]:
 !ms. riscv_bmr.bmr_extra ms ==>
   bmr_rel riscv_bmr (default_riscv_bir_state ms) ms
Proof
FULL_SIMP_TAC std_ss [default_riscv_bir_state_def,
  bir_lifting_machinesTheory.riscv_bmr_rel_EVAL,
  bir_env_oldTheory.bir_env_var_is_declared_def,
  bir_envTheory.bir_var_name_def] >>
FULL_SIMP_TAC (srw_ss()) [
              bir_envTheory.bir_env_read_UPDATE,
              bir_envTheory.bir_var_name_def,
              bir_envTheory.bir_env_lookup_UPDATE,
              bir_envTheory.bir_var_type_def,
              bir_envTheory.bir_env_lookup_type_def] >>
FULL_SIMP_TAC std_ss [bir_valuesTheory.type_of_bir_val_def,
                      type_of_bir_imm_def,
                      bir_immTheory.type_of_bool2b] >>
FULL_SIMP_TAC std_ss [bir_lifting_machinesTheory.bmr_extra_RISCV] >>
FULL_SIMP_TAC (srw_ss()) [bir_exp_liftingTheory.bir_load_w2n_mf_simp_thm] >>
METIS_TAC []
QED

bir_env_read (BVar "f28" (BType_Imm Bit64)) (default_riscv_bir_state ms) =
SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 28w)))

*)

(*

val default_arm8_bir_state_satisfies_rel_thm = prove(
  ``!ms.
    arm8_bmr.bmr_extra ms ==>
    bmr_rel arm8_bmr (default_arm8_bir_state ms) ms``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [default_arm8_bir_state_def,
  bir_lifting_machinesTheory.arm8_bmr_rel_EVAL,
  bir_env_oldTheory.bir_env_var_is_declared_def,
  bir_envTheory.bir_var_name_def] >>
FULL_SIMP_TAC (srw_ss()) [
              bir_envTheory.bir_env_read_UPDATE,
              bir_envTheory.bir_var_name_def,
              bir_envTheory.bir_env_lookup_UPDATE,
              bir_envTheory.bir_var_type_def,
              bir_envTheory.bir_env_lookup_type_def] >>
FULL_SIMP_TAC std_ss [bir_valuesTheory.type_of_bir_val_def,
                      type_of_bir_imm_def,
                      bir_immTheory.type_of_bool2b] >>
FULL_SIMP_TAC std_ss [bir_lifting_machinesTheory.bmr_extra_ARM8] >>
FULL_SIMP_TAC (srw_ss()) [bir_exp_liftingTheory.bir_load_w2n_mf_simp_thm] >>
METIS_TAC []
);


val exist_bir_of_arm8_thm = prove(
  ``!ms vars.
    arm8_wf_varset vars ==>
    arm8_bmr.bmr_extra ms ==>
    ?bs.
      (bmr_rel arm8_bmr bs ms /\ (bs.bst_status = BST_Running) /\
       bir_env_vars_are_initialised bs.bst_environ vars)``,

REPEAT STRIP_TAC >> 
EXISTS_TAC ``default_arm8_bir_state ms`` >>
ASSUME_TAC (SPEC ``ms:arm8_state`` default_arm8_bir_state_satisfies_rel_thm) >>
REV_FULL_SIMP_TAC std_ss [] >>
STRIP_TAC >- (
  EVAL_TAC
) >>
irule bir_env_oldTheory.bir_env_vars_are_initialised_SUBSET >>
Q.EXISTS_TAC `arm8_vars` >>
FULL_SIMP_TAC std_ss [arm8_wf_varset_def] >>
SIMP_TAC std_ss [arm8_vars_def] >>
(* TODO: This proof is sloooow... *)
FULL_SIMP_TAC std_ss [bir_env_oldTheory.bir_env_vars_are_initialised_INSERT] >>
REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_env_oldTheory.bir_env_var_is_initialised_def] >>
FULL_SIMP_TAC std_ss [bir_envTheory.bir_var_name_def, default_arm8_bir_state_def,
                        bir_envTheory.bir_env_lookup_UPDATE] >>
EVAL_TAC  >>
FULL_SIMP_TAC std_ss [bir_valuesTheory.bir_val_t_11,
                      bir_immTheory.type_of_bir_imm_def,
                      bir_valuesTheory.type_of_bir_val_EQ_ELIMS]
);


val set_of_address_in_all_address_labels_thm = prove (
  ``!l adds.
    l IN {BL_Address (Imm64 ml') | ml' IN adds} ==>
    l IN {l | IS_BL_Address l}``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [pred_setTheory.GSPECIFICATION, bir_program_labelsTheory.IS_BL_Address_def]
);


val bir_exec_to_labels_TO_exec_to_addr_label_n =
  store_thm("bir_exec_to_labels_TO_exec_to_addr_label_n",
  ``!bs' ml' mls p bs l n n0.
    (bs'.bst_pc.bpc_label IN {BL_Address (Imm64 ml') | ml' IN mls}) ==>
    (bir_exec_to_labels {BL_Address (Imm64 ml') | ml' IN mls} p bs =
         BER_Ended l n n0 bs') ==>
    ?n' lo c_st c_addr_labels.
         (n' > 0) /\
         (c_st = n) /\
         (bir_exec_to_addr_label_n p bs n' =
           BER_Ended lo c_st c_addr_labels bs')``,

REPEAT STRIP_TAC >>
subgoal `bs'.bst_pc.bpc_label IN {l | IS_BL_Address l}` >- (
  METIS_TAC [set_of_address_in_all_address_labels_thm]
) >>
FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_exec_to_labels_def, bir_exec_to_addr_label_n_def,
				      bir_exec_to_labels_n_def] >>
subgoal `bir_pc_cond_impl (F,
	   (\pc.
	     (pc.bpc_index = 0) /\
	     pc.bpc_label IN {BL_Address (Imm64 ml') | ml' IN mls})) (F, (\pc. (pc.bpc_index = 0) /\ pc.bpc_label IN {l | IS_BL_Address l}))` >- (
  FULL_SIMP_TAC std_ss [bir_pc_cond_impl_def] >>
  REPEAT STRIP_TAC >>
  METIS_TAC [set_of_address_in_all_address_labels_thm]
) >>
IMP_RES_TAC bir_exec_steps_GEN_change_cond_Ended_SOME >>
Q.EXISTS_TAC `n2` >>
FULL_SIMP_TAC arith_ss [] >>
METIS_TAC []
);


(* Just a version of bir_is_lifted_prog_MULTI_STEP_EXEC phrased in a more handy way *)
val bir_is_lifted_prog_MULTI_STEP_EXEC_compute =
  prove(
  ``!mu bs bs' ms ml (p:'a bir_program_t) (r:(64, 8, 'b) bir_lifting_machine_rec_t)
      mms n' lo c_st c_addr_labels.
    bir_is_lifted_prog r mu mms p ==>
    bmr_rel r bs ms ==>
    MEM (BL_Address (Imm64 ml)) (bir_labels_of_program p) ==>
    (bs.bst_pc = bir_block_pc (BL_Address (Imm64 ml))) ==>
    EVERY (bmr_ms_mem_contains r ms) mms ==>
    (bir_exec_to_addr_label_n p bs n' =
         BER_Ended lo c_st c_addr_labels bs') ==>
    ~bir_state_is_terminated bs ==>
    ~bir_state_is_terminated bs' ==>
    ?ms' li.
    (FUNPOW_OPT r.bmr_step_fun c_addr_labels ms = SOME ms') /\
    bmr_ms_mem_unchanged r ms ms' mu /\
    EVERY (bmr_ms_mem_contains r ms') mms /\
    (bs'.bst_pc = bir_block_pc (BL_Address li)) /\
    MEM (BL_Address li) (bir_labels_of_program p) /\
    bmr_rel r bs' ms'
``,

REPEAT STRIP_TAC >>
ASSUME_TAC (ISPECL [``r:(64, 8, 'b) bir_lifting_machine_rec_t``, ``mu:64 word_interval_t``,
                    ``mms:(word64# word8 list) list``,
                    ``p:'a bir_program_t``] bir_is_lifted_prog_MULTI_STEP_EXEC) >>
REV_FULL_SIMP_TAC std_ss [] >>
QSPECL_X_ASSUM ``!n ms bs. _`` [`n'`, `ms`, `bs`] >>
REV_FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_state_is_terminated_def]
);


val bir_arm8_block_pc = prove(
  ``!bs ms ml.
    bmr_rel arm8_bmr bs ms ==>
    (arm_ts.ctrl ms = ml) ==>
    (bs.bst_status = BST_Running) ==>
    (bs.bst_pc = bir_block_pc (BL_Address (Imm64 ml)))``,

REPEAT GEN_TAC >>
REPEAT DISCH_TAC >>
FULL_SIMP_TAC (std_ss++holBACore_ss++bir_wm_SS)
  [arm8_bmr_rel_EVAL, bir_block_pc_def, arm_ts_def]
);


val bir_get_ht_conseq_from_m_ante = prove(
  ``!bs p bpre bpost mpre ms ml mls.
    bir_cont p bir_exp_true (BL_Address (Imm64 ml))
      {BL_Address (Imm64 ml') | ml' IN mls} {} bpre bpost ==>
    bir_pre_arm8_to_bir mpre bpre ==>
    mpre ms ==>
    bmr_rel arm8_bmr bs ms ==>
    (bs.bst_status = BST_Running) ==>
    bir_env_vars_are_initialised bs.bst_environ
      (bir_vars_of_program p UNION bir_vars_of_exp bpre) ==>
    (bs.bst_pc = bir_block_pc (BL_Address (Imm64 ml))) ==>
    (?bs'.
     (bir_weak_trs {BL_Address (Imm64 ml') | ml' IN mls} p bs =
       SOME bs') /\
     (bir_eval_exp (bpost bs'.bst_pc.bpc_label) bs'.bst_environ =
       SOME bir_val_true)
    )``,

REPEAT GEN_TAC >>
REPEAT DISCH_TAC >>
FULL_SIMP_TAC (std_ss++bir_wm_SS)
  [bir_cont_def, t_ext_jgmt_def, t_jgmt_def,
   bir_exec_to_labels_triple_precond_def,
   bir_exec_to_labels_triple_postcond_def, bir_ts_def] >>
PAT_X_ASSUM ``!s. _``
            (fn thm => ASSUME_TAC (SPEC ``bs:bir_state_t`` thm)) >>
FULL_SIMP_TAC std_ss [bir_env_oldTheory.bir_env_vars_are_initialised_UNION] >>
subgoal `bir_is_bool_exp_env bs.bst_environ bpre /\
         (bir_eval_exp bpre bs.bst_environ = SOME bir_val_true)` >- (
  METIS_TAC [bir_pre_arm8_to_bir_def, bir_bool_expTheory.bir_is_bool_exp_env_def]
) >>
FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss)
  [bir_bool_expTheory.bir_eval_exp_TF,
   bir_bool_expTheory.bir_is_bool_exp_env_REWRS,
   bir_block_pc_def] >>
REV_FULL_SIMP_TAC (std_ss++holBACore_ss) []
);


val bir_arm8_exec_in_end_label_set = prove(
  ``!c_addr_labels ms' bs bs' mls p n n' lo li.
    (* Execution from BIR HT *)
    (bir_exec_to_addr_label_n p bs n' = BER_Ended lo n c_addr_labels bs') ==>
    (n' > 0) ==>
    ~bir_state_is_terminated bs' ==>
    (bs'.bst_pc = bir_block_pc (BL_Address li)) ==>
    ((bir_block_pc (BL_Address li)).bpc_label IN
         {BL_Address (Imm64 ml') | ml' IN mls}) ==>
    (* BMR relation between the final states *)
    bmr_rel arm8_bmr bs' ms' ==>
    c_addr_labels > 0 /\
    ms'.PC IN mls``,

REPEAT GEN_TAC >>
REPEAT DISCH_TAC >>
subgoal `c_addr_labels > 0` >- (
  Cases_on `c_addr_labels = 0` >- (
    FULL_SIMP_TAC std_ss [bir_exec_to_addr_label_n_def, bir_exec_to_labels_n_def,
                          bir_exec_steps_GEN_SOME_EQ_Ended] >>
    FULL_SIMP_TAC arith_ss []
  ) >>
  FULL_SIMP_TAC arith_ss []
) >>
subgoal `ms'.PC IN mls` >- (
  subgoal `bs'.bst_pc = bir_block_pc (BL_Address (Imm64 ms'.PC))` >- (
    REV_FULL_SIMP_TAC (std_ss++holBACore_ss)
      [bir_state_is_terminated_def,
       GEN_ALL bir_lifting_machinesTheory.arm8_bmr_rel_EVAL]
  ) >>
  REV_FULL_SIMP_TAC (std_ss++holBACore_ss++pred_setLib.PRED_SET_ss)
    [bir_programTheory.bir_block_pc_def] >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) []
) >>
FULL_SIMP_TAC std_ss []
);


val bir_arm8_inter_exec_notin_end_label_set = prove(
  ``!mls p bs l n0 n' n'' lo lo' c_st c_st' bs' bs''.
    (bir_exec_to_labels {BL_Address (Imm64 ml') | ml' IN mls} p bs =
       BER_Ended l c_st n0 bs') ==>
    (bir_exec_to_addr_label_n p bs n'' = BER_Ended lo' c_st' n'' bs'') ==>
    c_st' < c_st ==>
    n'' > 0 ==>
    ~bir_state_is_terminated bs'' ==>
    bs''.bst_pc.bpc_label NOTIN
      {BL_Address (Imm64 ml') | ml' IN mls}``,

REPEAT STRIP_TAC >>
(* NOTE: The number of taken statement steps is c_st for both the to-label execution
 * and the to-addr-label-execution. *)
(* The number of PCs counted (= in mls) at c_st' statement steps must be 0. *)
subgoal `~bir_state_COUNT_PC (F,
	  (\pc.
	       (pc.bpc_index = 0) /\
	       pc.bpc_label IN {BL_Address (Imm64 ml') | ml' IN mls}))
	      (bir_exec_infinite_steps_fun p bs c_st')` >- (
  FULL_SIMP_TAC std_ss [bir_exec_to_labels_def, bir_exec_to_labels_n_def,
			bir_exec_steps_GEN_SOME_EQ_Ended] >>
  (* Ergo, at c_st' statement steps, the PC label is not in mls, which follows after
   * some arithmetic. *)
  QSPECL_X_ASSUM ``!(n:num). (n < c_st) ==> _`` [`c_st'`] >>
  REV_FULL_SIMP_TAC std_ss [] >>
  subgoal `c_st' > 0` >- (
    METIS_TAC [bir_exec_to_addr_label_n_def, bir_exec_to_labels_n_def,
	       bir_exec_steps_GEN_SOME_EQ_Ended_Running_steps,
	       bir_state_is_terminated_def]
  ) >>
  FULL_SIMP_TAC std_ss [NUM_LSONE_EQZ, bir_exec_infinite_steps_fun_COUNT_PCs_EQ_0] >>
  QSPECL_X_ASSUM ``!j. _`` [`PRE c_st'`] >>
  SUBGOAL_THEN ``SUC (PRE (c_st':num)) = c_st'`` (fn thm => FULL_SIMP_TAC std_ss [thm]) >- (
    FULL_SIMP_TAC arith_ss []
  ) >>
  METIS_TAC [NUM_PRE_LT]
) >>
(* So either PC at c_st' statement steps has index 0, or it is not in mls.
 * But PC has index 0... *)
subgoal `bs''.bst_pc.bpc_index = 0` >- (
  METIS_TAC [bir_exec_to_addr_label_n_ended_running, bir_state_is_terminated_def]
) >>
(* ... which proves the goal, after some identification of states. *)
FULL_SIMP_TAC std_ss [bir_state_COUNT_PC_def, bir_exec_to_addr_label_n_def,
		      bir_exec_to_labels_n_def,
		      bir_exec_steps_GEN_SOME_EQ_Ended] >>
REV_FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_state_is_terminated_def]
);


val bir_arm8_inter_exec = prove(
  ``!n' c_addr_labels n0 ms ml mls bs bs' p lo l c_st n mu mms.
    bir_is_lifted_prog arm8_bmr mu mms p ==>
    EVERY (bmr_ms_mem_contains arm8_bmr ms) mms ==>
    (arm_ts.ctrl ms = ml) ==>
    (MEM (BL_Address (Imm64 ml)) (bir_labels_of_program p)) ==>
    bmr_rel arm8_bmr bs ms ==>
    ~bir_state_is_terminated bs ==>
    (bs.bst_pc = bir_block_pc (BL_Address (Imm64 ml))) ==>
    (bir_exec_to_labels {BL_Address (Imm64 ml') | ml' IN mls} p bs = BER_Ended l c_st n0 bs') ==>
    ~bir_state_is_terminated bs' ==>
    (bir_exec_to_addr_label_n p bs n' = BER_Ended lo c_st c_addr_labels bs') ==>
    (!n''.
       n'' < c_addr_labels /\ n'' > 0 ==>
       ?ms''.
	 (FUNPOW_OPT arm8_bmr.bmr_step_fun n'' ms = SOME ms'') /\
	 ms''.PC NOTIN mls
    )``,

REPEAT STRIP_TAC >>
(* The given number of address labels has been reached by bir_exec_to_addr_label_n when
 * resulting Ended state bs' is not terminated *)
Q.SUBGOAL_THEN `c_addr_labels = n'` (fn thm => FULL_SIMP_TAC std_ss [thm]) >- (
  FULL_SIMP_TAC std_ss [bir_exec_to_addr_label_n_def, bir_exec_to_labels_n_def] >>
  METIS_TAC [bir_exec_steps_GEN_SOME_EQ_Ended_pc_counts]
) >>
(* For some smaller number of address labels n'', bir_exec_to_addr_label_n also Ends
 * (in bs'') *)
subgoal `?lo' c_st' c_addr_labels' bs''.
         bir_exec_to_addr_label_n p bs n'' =
           BER_Ended lo' c_st' c_addr_labels' bs''` >- (
  FULL_SIMP_TAC std_ss [bir_exec_to_addr_label_n_def, bir_exec_to_labels_n_def] >>
  METIS_TAC [bir_exec_steps_GEN_decrease_max_steps_Ended_SOME]
) >>
(* Since the later state bs' is Running, bs'' must be Running as well... *)
subgoal `~bir_state_is_terminated bs''` >- (
  FULL_SIMP_TAC std_ss [bir_exec_to_addr_label_n_def, bir_exec_to_labels_n_def] >>
  METIS_TAC [bir_exec_steps_GEN_decrease_max_steps_Ended_terminated]
) >>
(* ... with the given number of address labels reached. *)
Q.SUBGOAL_THEN `c_addr_labels' = n''` (fn thm => FULL_SIMP_TAC std_ss [thm]) >- (
  FULL_SIMP_TAC std_ss [bir_exec_to_addr_label_n_def, bir_exec_to_labels_n_def] >>
  METIS_TAC [bir_exec_steps_GEN_SOME_EQ_Ended_pc_counts]
) >>
(* Now, prove that there is some state ms'' such that ms'' and bs'' are related in the
 * sense of bmr_rel, with some additional sanity statements on PC and memory.
 * Furthermore, ms'' is reached from ms by n'' applications of the machine step. *)
subgoal `?ms'' li.
         bmr_rel arm8_bmr bs'' ms'' /\
         EVERY (bmr_ms_mem_contains arm8_bmr ms'') mms /\
         bmr_ms_mem_unchanged arm8_bmr ms ms'' mu /\
         MEM (BL_Address li) (bir_labels_of_program p) /\
         (bs''.bst_pc = bir_block_pc (BL_Address li)) /\
         (FUNPOW_OPT arm8_bmr.bmr_step_fun n'' ms = SOME ms'')` >- (
  IMP_RES_TAC bir_is_lifted_prog_MULTI_STEP_EXEC_compute >>
  METIS_TAC []
) >>
(* We have proven how some ms'' (in fact, the free variable ms'') can be reached
 * from ms by n'' applications of the machine step. It remains to prove that ms'' cannot
 * be a member of the Ending label set mls.
 * First, we prove a similar property for the label of bs'', then we translate this to
 * ms''. This can be easily done since both are word64 terms in different wrapping. *)
subgoal `bs''.bst_pc.bpc_label NOTIN
           {BL_Address (Imm64 ml') | ml' IN mls}` >- (
  subgoal `c_st' < c_st` >- (
    METIS_TAC [bir_exec_to_labels_def, bir_exec_to_addr_label_n_def,
	       bir_exec_to_labels_n_def,
	       bir_exec_steps_GEN_decrease_max_steps_Ended_steps_taken]
  ) >>
  METIS_TAC [bir_arm8_inter_exec_notin_end_label_set]
) >>
Q.EXISTS_TAC `ms''` >>
(* Prove correspondence between the labels of the machine state PC and the BIR PC. *)
subgoal `bs''.bst_pc = bir_block_pc (BL_Address (Imm64 ms''.PC))` >- (
  REV_FULL_SIMP_TAC (std_ss++holBACore_ss)
    [GEN_ALL arm8_bmr_rel_EVAL, bir_state_is_terminated_def]
) >>
FULL_SIMP_TAC (std_ss++holBACore_ss++bir_wm_SS++pred_setLib.PRED_SET_ss)
  [bir_block_pc_def]
);


val lift_contract_thm = store_thm("lift_contract_thm",
  ``!p mms ml mls mu mpre mpost bpre bpost.
      MEM (BL_Address (Imm64 ml)) (bir_labels_of_program p) ==>
      bir_cont p bir_exp_true (BL_Address (Imm64 ml))
	{BL_Address (Imm64 ml') | ml' IN mls} {} bpre bpost ==>
      bir_is_lifted_prog arm8_bmr mu mms p ==>
      arm8_wf_varset (bir_vars_of_program p UNION bir_vars_of_exp bpre) ==>
      bir_pre_arm8_to_bir mpre bpre ==>
      bir_post_bir_to_arm8 mpost bpost {BL_Address (Imm64 ml') | ml' IN mls} ==>
      arm8_cont mms ml mls mpre mpost``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [arm8_cont_def, t_jgmt_def] >>
REPEAT STRIP_TAC >>
(* 1. Among the assumptions we now also have the antecedents of the arm8
 *    HT. Combining these, exist_bir_of_arm8_thm gives that there is a
 *    Running BIR state bs where the variables of arm8_wf_varset are
 *    initialised which is related to (in the sense of bmr_rel) the the
 *    arm8 machine state ms. *)
IMP_RES_TAC (SPECL [``ms:arm8_state``,
                    ``(bir_vars_of_program p) UNION (bir_vars_of_exp bpre)``]
                  exist_bir_of_arm8_thm) >>

(* 2. The assumptions now allow us to prove the antecedents of the BIR HT
 *    and obtain the consequent. This states that the BIR weak transition
 *    from bs to some state in the Ending label set mls results in some
 *    state bs', in which the BIR postcondition bpost holds.
 *    Furthermore, the PC of bs points to the first statement in the block
 *    with label ml. *)
IMP_RES_TAC bir_arm8_block_pc >>
IMP_RES_TAC bir_get_ht_conseq_from_m_ante >>
FULL_SIMP_TAC std_ss [bir_weak_trs_EQ] >>

(* 3. Then, bir_is_lifted_prog_MULTI_STEP_EXEC is used to obtain the
 *    existence of some arm8 machine state ms' related to bs'
 *    (in the sense of bmr_rel) and some properties related to it. *)
IMP_RES_TAC bir_exec_to_labels_TO_exec_to_addr_label_n >>
IMP_RES_TAC bir_is_lifted_prog_MULTI_STEP_EXEC_compute >>
REV_FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>

(* 4. Give ms' as witness to goal and prove the easy goal conjuncts -
 *    all but arm_ts.weak ms mls ms', which is a statement on how ms
 *    and ms' are related through a weak transition *)
Q.EXISTS_TAC `ms'` >>
subgoal `arm8_bmr.bmr_extra ms'` >- (
  FULL_SIMP_TAC std_ss [bmr_rel_def]
) >>
subgoal `mpost ms'` >- (
  FULL_SIMP_TAC std_ss [bir_post_bir_to_arm8_def] >>
  QSPECL_X_ASSUM ``!ms. _``
    [`ms'`, `bs'`, `(bir_block_pc (BL_Address li)).bpc_label`] >>
  REV_FULL_SIMP_TAC std_ss []
) >>
FULL_SIMP_TAC std_ss [] >>

(* 5. Show that the weak transition in the goal exists *)
SIMP_TAC (std_ss++bir_wm_SS) [arm_ts_def,
                              arm_weak_trs_def] >>
Q.EXISTS_TAC `c_addr_labels` >>
(* 5a. Weak transition from initial state ms ends in final state ms':
 *     Machine-stepping from ms to ms' already exists among assumptions,
 *     PC of final state ms' must be in Ending label set mls due to BIR HT
 *     execution, plus the fact that bs' and ms' are related *)
IMP_RES_TAC bir_arm8_exec_in_end_label_set >>
FULL_SIMP_TAC std_ss [] >>

(* 5b. Machine steps from ms up until ms' is reached:
 *     This part of the proof is complex, see proof of lemma used *)
METIS_TAC [bir_state_is_terminated_def, bir_arm8_inter_exec]
);
*)


val _ = export_theory();
