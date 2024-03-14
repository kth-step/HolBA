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

open bir_arm8_backlifterTheory;

val _ = new_theory "bir_riscv_backlifter";

(* FIXME: procID must never change? *)
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

Definition default_riscv_bir_env_basic_def:
 default_riscv_bir_env_basic ms env_map =
 (("MEM8"     =+ SOME (BVal_Mem Bit64 Bit8 (bir_mmap_w_w2n (bir_mf2mm ms.MEM8))))
 (("tmp_MEM8" =+ SOME (BVal_Mem Bit64 Bit8 (bir_mmap_w_w2n (bir_mf2mm ms.MEM8))))
 (("tmp_PC"   =+ SOME (BVal_Imm (Imm64 (ms.c_PC ms.procID))))
 (("tmp_COND" =+ SOME (BVal_Imm (Imm1 0w))) env_map))))
End

Definition default_riscv_bir_env_FPRS_def:
 default_riscv_bir_env_FPRS ms env_map =
   ("f0"       =+ SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 0w))))
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
   (("tmp_f14"  =+ SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 14w))))
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
   env_map)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
End

Definition default_riscv_bir_env_GPRS_def:
 default_riscv_bir_env_GPRS ms env_map =
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
  env_map)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
End

Definition default_riscv_bir_state_def:
 default_riscv_bir_state ms =
  <| bst_pc := bir_block_pc (BL_Address (Imm64 (ms.c_PC ms.procID))) ;
     bst_environ := BEnv
       (default_riscv_bir_env_GPRS ms
        (default_riscv_bir_env_FPRS ms
         (default_riscv_bir_env_basic ms bir_env_map_empty)));
     bst_status := BST_Running
   |>
End

Theorem default_riscv_bir_state_GPRS_read[local]:
 !ms.
  bir_env_read (BVar "x0" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 0w))) /\
  bir_env_read (BVar "x1" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 1w))) /\
  bir_env_read (BVar "x2" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 2w))) /\
  bir_env_read (BVar "x3" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 3w))) /\
  bir_env_read (BVar "x4" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 4w))) /\
  bir_env_read (BVar "x5" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 5w))) /\
  bir_env_read (BVar "x6" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 6w))) /\
  bir_env_read (BVar "x7" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 7w))) /\
  bir_env_read (BVar "x8" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 8w))) /\
  bir_env_read (BVar "x9" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 9w))) /\
  bir_env_read (BVar "x10" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 10w))) /\
  bir_env_read (BVar "x11" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 11w))) /\
  bir_env_read (BVar "x12" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 12w))) /\
  bir_env_read (BVar "x13" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 13w))) /\
  bir_env_read (BVar "x14" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 14w))) /\
  bir_env_read (BVar "x15" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 15w))) /\
  bir_env_read (BVar "x16" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 16w))) /\
  bir_env_read (BVar "x17" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 17w))) /\
  bir_env_read (BVar "x18" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 18w))) /\
  bir_env_read (BVar "x19" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 19w))) /\
  bir_env_read (BVar "x20" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 20w))) /\
  bir_env_read (BVar "x21" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 21w))) /\
  bir_env_read (BVar "x22" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 22w))) /\
  bir_env_read (BVar "x23" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 23w))) /\
  bir_env_read (BVar "x24" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 24w))) /\
  bir_env_read (BVar "x25" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 25w))) /\
  bir_env_read (BVar "x26" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 26w))) /\
  bir_env_read (BVar "x27" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 27w))) /\
  bir_env_read (BVar "x28" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 28w))) /\
  bir_env_read (BVar "x29" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 29w))) /\
  bir_env_read (BVar "x30" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 30w))) /\
  bir_env_read (BVar "x31" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 31w)))
Proof
  rw [default_riscv_bir_state_def,
      default_riscv_bir_env_GPRS_def,
      bir_envTheory.bir_env_read_UPDATE,
      bir_envTheory.bir_var_name_def,
      bir_envTheory.bir_env_lookup_UPDATE,
      bir_envTheory.bir_var_type_def,
      bir_valuesTheory.type_of_bir_val_def,
      type_of_bir_imm_def,
      bir_immTheory.type_of_bool2b]
QED

Theorem default_riscv_bir_state_GPRS_read_tmp[local]:
 !ms.
  bir_env_read (BVar "tmp_x0" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 0w))) /\
  bir_env_read (BVar "tmp_x1" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 1w))) /\
  bir_env_read (BVar "tmp_x2" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 2w))) /\
  bir_env_read (BVar "tmp_x3" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 3w))) /\
  bir_env_read (BVar "tmp_x4" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 4w))) /\
  bir_env_read (BVar "tmp_x5" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 5w))) /\
  bir_env_read (BVar "tmp_x6" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 6w))) /\
  bir_env_read (BVar "tmp_x7" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 7w))) /\
  bir_env_read (BVar "tmp_x8" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 8w))) /\
  bir_env_read (BVar "tmp_x9" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 9w))) /\
  bir_env_read (BVar "tmp_x10" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 10w))) /\
  bir_env_read (BVar "tmp_x11" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 11w))) /\
  bir_env_read (BVar "tmp_x12" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 12w))) /\
  bir_env_read (BVar "tmp_x13" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 13w))) /\
  bir_env_read (BVar "tmp_x14" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 14w))) /\
  bir_env_read (BVar "tmp_x15" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 15w))) /\
  bir_env_read (BVar "tmp_x16" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 16w))) /\
  bir_env_read (BVar "tmp_x17" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 17w))) /\
  bir_env_read (BVar "tmp_x18" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 18w))) /\
  bir_env_read (BVar "tmp_x19" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 19w))) /\
  bir_env_read (BVar "tmp_x20" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 20w))) /\
  bir_env_read (BVar "tmp_x21" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 21w))) /\
  bir_env_read (BVar "tmp_x22" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 22w))) /\
  bir_env_read (BVar "tmp_x23" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 23w))) /\
  bir_env_read (BVar "tmp_x24" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 24w))) /\
  bir_env_read (BVar "tmp_x25" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 25w))) /\
  bir_env_read (BVar "tmp_x26" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 26w))) /\
  bir_env_read (BVar "tmp_x27" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 27w))) /\
  bir_env_read (BVar "tmp_x28" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 28w))) /\
  bir_env_read (BVar "tmp_x29" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 29w))) /\
  bir_env_read (BVar "tmp_x30" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 30w))) /\
  bir_env_read (BVar "tmp_x31" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_gpr ms.procID 31w)))
Proof
  rw [default_riscv_bir_state_def,
      default_riscv_bir_env_GPRS_def,
      bir_envTheory.bir_env_read_UPDATE,
      bir_envTheory.bir_var_name_def,
      bir_envTheory.bir_env_lookup_UPDATE,
      bir_envTheory.bir_var_type_def,
      bir_valuesTheory.type_of_bir_val_def,
      type_of_bir_imm_def,
      bir_immTheory.type_of_bool2b]
QED

Theorem default_riscv_bir_state_GPRS_lookup_type[local]:
  !ms.
  bir_env_lookup_type "x0" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "x0" (BType_Imm Bit64)))  /\
  bir_env_lookup_type "x1" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "x1" (BType_Imm Bit64))) /\
  bir_env_lookup_type "x2" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "x2" (BType_Imm Bit64))) /\
  bir_env_lookup_type "x3" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "x3" (BType_Imm Bit64))) /\
  bir_env_lookup_type "x4" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "x4" (BType_Imm Bit64))) /\
  bir_env_lookup_type "x5" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "x5" (BType_Imm Bit64))) /\
  bir_env_lookup_type "x6" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "x6" (BType_Imm Bit64))) /\
    bir_env_lookup_type "x7" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "x7" (BType_Imm Bit64))) /\
  bir_env_lookup_type "x8" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "x8" (BType_Imm Bit64))) /\
  bir_env_lookup_type "x9" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "x9" (BType_Imm Bit64))) /\
  bir_env_lookup_type "x10" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "x10" (BType_Imm Bit64))) /\
  bir_env_lookup_type "x11" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "x11" (BType_Imm Bit64))) /\
  bir_env_lookup_type "x12" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "x12" (BType_Imm Bit64))) /\
  bir_env_lookup_type "x13" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "x13" (BType_Imm Bit64))) /\
  bir_env_lookup_type "x14" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "x14" (BType_Imm Bit64))) /\
  bir_env_lookup_type "x15" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "x15" (BType_Imm Bit64))) /\
  bir_env_lookup_type "x16" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "x16" (BType_Imm Bit64))) /\
  bir_env_lookup_type "x17" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "x17" (BType_Imm Bit64))) /\
  bir_env_lookup_type "x18" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "x18" (BType_Imm Bit64))) /\
  bir_env_lookup_type "x19" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "x19" (BType_Imm Bit64))) /\
  bir_env_lookup_type "x20" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "x20" (BType_Imm Bit64))) /\
  bir_env_lookup_type "x21" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "x21" (BType_Imm Bit64))) /\
  bir_env_lookup_type "x22" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "x22" (BType_Imm Bit64))) /\
  bir_env_lookup_type "x23" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "x23" (BType_Imm Bit64))) /\
  bir_env_lookup_type "x24" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "x24" (BType_Imm Bit64))) /\
  bir_env_lookup_type "x25" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "x25" (BType_Imm Bit64))) /\
  bir_env_lookup_type "x26" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "x26" (BType_Imm Bit64))) /\
  bir_env_lookup_type "x27" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "x27" (BType_Imm Bit64))) /\
  bir_env_lookup_type "x28" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "x28" (BType_Imm Bit64))) /\
  bir_env_lookup_type "x29" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "x29" (BType_Imm Bit64))) /\
  bir_env_lookup_type "x30" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "x30" (BType_Imm Bit64))) /\
  bir_env_lookup_type "x31" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "x31" (BType_Imm Bit64)))
Proof
  rw [default_riscv_bir_state_def,
      default_riscv_bir_env_GPRS_def,
      bir_env_oldTheory.bir_env_var_is_declared_def,
      bir_envTheory.bir_var_name_def,
      bir_envTheory.bir_env_read_UPDATE,
      bir_envTheory.bir_var_name_def,
      bir_envTheory.bir_env_lookup_UPDATE,
      bir_envTheory.bir_var_type_def,
      bir_envTheory.bir_env_lookup_type_def,
      bir_valuesTheory.type_of_bir_val_def,
     type_of_bir_imm_def]
QED

Theorem default_riscv_bir_state_GPRS_lookup_type_tmp[local]:
  !ms.
  bir_env_lookup_type "tmp_x0" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "tmp_x0" (BType_Imm Bit64))) /\
  bir_env_lookup_type "tmp_x1" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "tmp_x1" (BType_Imm Bit64))) /\
  bir_env_lookup_type "tmp_x2" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "tmp_x2" (BType_Imm Bit64))) /\
  bir_env_lookup_type "tmp_x3" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "tmp_x3" (BType_Imm Bit64))) /\
  bir_env_lookup_type "tmp_x4" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "tmp_x4" (BType_Imm Bit64))) /\
  bir_env_lookup_type "tmp_x5" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "tmp_x5" (BType_Imm Bit64))) /\
  bir_env_lookup_type "tmp_x6" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "tmp_x6" (BType_Imm Bit64))) /\
  bir_env_lookup_type "tmp_x7" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "tmp_x7" (BType_Imm Bit64))) /\
  bir_env_lookup_type "tmp_x8" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "tmp_x8" (BType_Imm Bit64))) /\
  bir_env_lookup_type "tmp_x9" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "tmp_x9" (BType_Imm Bit64))) /\
  bir_env_lookup_type "tmp_x10" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "tmp_x10" (BType_Imm Bit64))) /\
  bir_env_lookup_type "tmp_x11" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "tmp_x11" (BType_Imm Bit64))) /\
  bir_env_lookup_type "tmp_x12" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "tmp_x12" (BType_Imm Bit64))) /\
  bir_env_lookup_type "tmp_x13" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "tmp_x13" (BType_Imm Bit64))) /\
  bir_env_lookup_type "tmp_x14" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "tmp_x14" (BType_Imm Bit64))) /\
  bir_env_lookup_type "tmp_x15" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "tmp_x15" (BType_Imm Bit64))) /\
  bir_env_lookup_type "tmp_x16" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "tmp_x16" (BType_Imm Bit64))) /\
  bir_env_lookup_type "tmp_x17" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "tmp_x17" (BType_Imm Bit64))) /\
  bir_env_lookup_type "tmp_x18" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "tmp_x18" (BType_Imm Bit64))) /\
  bir_env_lookup_type "tmp_x19" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "tmp_x19" (BType_Imm Bit64))) /\
  bir_env_lookup_type "tmp_x20" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "tmp_x20" (BType_Imm Bit64))) /\
  bir_env_lookup_type "tmp_x21" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "tmp_x21" (BType_Imm Bit64))) /\
  bir_env_lookup_type "tmp_x22" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "tmp_x22" (BType_Imm Bit64))) /\
  bir_env_lookup_type "tmp_x23" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "tmp_x23" (BType_Imm Bit64))) /\
  bir_env_lookup_type "tmp_x24" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "tmp_x24" (BType_Imm Bit64))) /\
  bir_env_lookup_type "tmp_x25" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "tmp_x25" (BType_Imm Bit64))) /\
  bir_env_lookup_type "tmp_x26" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "tmp_x26" (BType_Imm Bit64))) /\
  bir_env_lookup_type "tmp_x27" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "tmp_x27" (BType_Imm Bit64))) /\
  bir_env_lookup_type "tmp_x28" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "tmp_x28" (BType_Imm Bit64))) /\
  bir_env_lookup_type "tmp_x29" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "tmp_x29" (BType_Imm Bit64))) /\
  bir_env_lookup_type "tmp_x30" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "tmp_x30" (BType_Imm Bit64))) /\
  bir_env_lookup_type "tmp_x31" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "tmp_x31" (BType_Imm Bit64)))
Proof
  rw [default_riscv_bir_state_def,
      default_riscv_bir_env_GPRS_def,
      bir_env_oldTheory.bir_env_var_is_declared_def,
      bir_envTheory.bir_var_name_def,
      bir_envTheory.bir_env_read_UPDATE,
      bir_envTheory.bir_var_name_def,
      bir_envTheory.bir_env_lookup_UPDATE,
      bir_envTheory.bir_var_type_def,
      bir_envTheory.bir_env_lookup_type_def,
      bir_valuesTheory.type_of_bir_val_def,
     type_of_bir_imm_def]
QED

Theorem default_riscv_bir_state_FPRS_read[local]:
 !ms.
  bir_env_read (BVar "f0" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 0w))) /\
  bir_env_read (BVar "f1" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 1w))) /\
  bir_env_read (BVar "f2" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 2w))) /\
  bir_env_read (BVar "f3" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 3w))) /\
  bir_env_read (BVar "f4" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 4w))) /\
  bir_env_read (BVar "f5" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 5w))) /\
  bir_env_read (BVar "f6" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 6w))) /\
  bir_env_read (BVar "f7" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 7w))) /\
  bir_env_read (BVar "f8" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 8w))) /\
  bir_env_read (BVar "f9" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 9w))) /\
  bir_env_read (BVar "f10" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 10w))) /\
  bir_env_read (BVar "f11" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 11w))) /\
  bir_env_read (BVar "f12" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 12w))) /\
  bir_env_read (BVar "f13" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 13w))) /\
  bir_env_read (BVar "f14" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 14w))) /\
  bir_env_read (BVar "f15" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 15w))) /\
  bir_env_read (BVar "f16" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 16w))) /\
  bir_env_read (BVar "f17" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 17w))) /\
  bir_env_read (BVar "f18" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 18w))) /\
  bir_env_read (BVar "f19" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 19w))) /\
  bir_env_read (BVar "f20" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 20w))) /\
  bir_env_read (BVar "f21" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 21w))) /\
  bir_env_read (BVar "f22" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 22w))) /\
  bir_env_read (BVar "f23" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 23w))) /\
  bir_env_read (BVar "f24" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 24w))) /\
  bir_env_read (BVar "f25" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 25w))) /\
  bir_env_read (BVar "f26" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 26w))) /\
  bir_env_read (BVar "f27" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 27w))) /\
  bir_env_read (BVar "f28" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 28w))) /\
  bir_env_read (BVar "f29" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 29w))) /\
  bir_env_read (BVar "f30" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 30w))) /\
  bir_env_read (BVar "f31" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 31w)))
Proof
  rw [default_riscv_bir_state_def,
      default_riscv_bir_env_GPRS_def,
      default_riscv_bir_env_FPRS_def,
      bir_envTheory.bir_env_read_UPDATE,
      bir_envTheory.bir_var_name_def,
      bir_envTheory.bir_env_lookup_UPDATE,
      bir_envTheory.bir_var_type_def,
      bir_valuesTheory.type_of_bir_val_def,
      type_of_bir_imm_def,
      bir_immTheory.type_of_bool2b]
QED

Theorem default_riscv_bir_state_FPRS_read_tmp[local]:
 !ms.
  bir_env_read (BVar "tmp_f0" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 0w))) /\
  bir_env_read (BVar "tmp_f1" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 1w))) /\
  bir_env_read (BVar "tmp_f2" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 2w))) /\
  bir_env_read (BVar "tmp_f3" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 3w))) /\
  bir_env_read (BVar "tmp_f4" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 4w))) /\
  bir_env_read (BVar "tmp_f5" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 5w))) /\
  bir_env_read (BVar "tmp_f6" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 6w))) /\
  bir_env_read (BVar "tmp_f7" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 7w))) /\
  bir_env_read (BVar "tmp_f8" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 8w))) /\
  bir_env_read (BVar "tmp_f9" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 9w))) /\
  bir_env_read (BVar "tmp_f10" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 10w))) /\
  bir_env_read (BVar "tmp_f11" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 11w))) /\
  bir_env_read (BVar "tmp_f12" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 12w))) /\
  bir_env_read (BVar "tmp_f13" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 13w))) /\
  bir_env_read (BVar "tmp_f14" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 14w))) /\
  bir_env_read (BVar "tmp_f15" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 15w))) /\
  bir_env_read (BVar "tmp_f16" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 16w))) /\
  bir_env_read (BVar "tmp_f17" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 17w))) /\
  bir_env_read (BVar "tmp_f18" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 18w))) /\
  bir_env_read (BVar "tmp_f19" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 19w))) /\
  bir_env_read (BVar "tmp_f20" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 20w))) /\
  bir_env_read (BVar "tmp_f21" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 21w))) /\
  bir_env_read (BVar "tmp_f22" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 22w))) /\
  bir_env_read (BVar "tmp_f23" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 23w))) /\
  bir_env_read (BVar "tmp_f24" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 24w))) /\
  bir_env_read (BVar "tmp_f25" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 25w))) /\
  bir_env_read (BVar "tmp_f26" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 26w))) /\
  bir_env_read (BVar "tmp_f27" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 27w))) /\
  bir_env_read (BVar "tmp_f28" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 28w))) /\
  bir_env_read (BVar "tmp_f29" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 29w))) /\
  bir_env_read (BVar "tmp_f30" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 30w))) /\
  bir_env_read (BVar "tmp_f31" (BType_Imm Bit64)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Imm (Imm64 (ms.c_fpr ms.procID 31w)))
Proof
  rw [default_riscv_bir_state_def,
      default_riscv_bir_env_GPRS_def,
      default_riscv_bir_env_FPRS_def,
      bir_envTheory.bir_env_read_UPDATE,
      bir_envTheory.bir_var_name_def,
      bir_envTheory.bir_env_lookup_UPDATE,
      bir_envTheory.bir_var_type_def,
      bir_valuesTheory.type_of_bir_val_def,
      type_of_bir_imm_def,
      bir_immTheory.type_of_bool2b]
QED

Theorem default_riscv_bir_state_FPRS_lookup_type[local]:
  !ms.
  bir_env_lookup_type "f0" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "f0" (BType_Imm Bit64)))  /\
  bir_env_lookup_type "f1" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "f1" (BType_Imm Bit64))) /\
  bir_env_lookup_type "f2" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "f2" (BType_Imm Bit64))) /\
  bir_env_lookup_type "f3" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "f3" (BType_Imm Bit64))) /\
  bir_env_lookup_type "f4" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "f4" (BType_Imm Bit64))) /\
  bir_env_lookup_type "f5" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "f5" (BType_Imm Bit64))) /\
  bir_env_lookup_type "f6" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "f6" (BType_Imm Bit64))) /\
  bir_env_lookup_type "f7" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "f7" (BType_Imm Bit64))) /\
  bir_env_lookup_type "f8" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "f8" (BType_Imm Bit64))) /\
  bir_env_lookup_type "f9" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "f9" (BType_Imm Bit64))) /\
  bir_env_lookup_type "f10" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "f10" (BType_Imm Bit64))) /\
  bir_env_lookup_type "f11" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "f11" (BType_Imm Bit64))) /\
  bir_env_lookup_type "f12" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "f12" (BType_Imm Bit64))) /\
  bir_env_lookup_type "f13" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "f13" (BType_Imm Bit64))) /\
  bir_env_lookup_type "f14" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "f14" (BType_Imm Bit64))) /\
  bir_env_lookup_type "f15" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "f15" (BType_Imm Bit64))) /\
  bir_env_lookup_type "f16" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "f16" (BType_Imm Bit64))) /\
  bir_env_lookup_type "f17" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "f17" (BType_Imm Bit64))) /\
  bir_env_lookup_type "f18" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "f18" (BType_Imm Bit64))) /\
  bir_env_lookup_type "f19" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "f19" (BType_Imm Bit64))) /\
  bir_env_lookup_type "f20" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "f20" (BType_Imm Bit64))) /\
  bir_env_lookup_type "f21" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "f21" (BType_Imm Bit64))) /\
  bir_env_lookup_type "f22" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "f22" (BType_Imm Bit64))) /\
  bir_env_lookup_type "f23" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "f23" (BType_Imm Bit64))) /\
  bir_env_lookup_type "f24" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "f24" (BType_Imm Bit64))) /\
  bir_env_lookup_type "f25" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "f25" (BType_Imm Bit64))) /\
  bir_env_lookup_type "f26" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "f26" (BType_Imm Bit64))) /\
  bir_env_lookup_type "f27" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "f27" (BType_Imm Bit64))) /\
  bir_env_lookup_type "f28" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "f28" (BType_Imm Bit64))) /\
  bir_env_lookup_type "f29" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "f29" (BType_Imm Bit64))) /\
  bir_env_lookup_type "f30" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "f30" (BType_Imm Bit64))) /\
  bir_env_lookup_type "f31" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "f31" (BType_Imm Bit64)))
Proof
  rw [default_riscv_bir_state_def,
      default_riscv_bir_env_GPRS_def,
      default_riscv_bir_env_FPRS_def,
      bir_env_oldTheory.bir_env_var_is_declared_def,
      bir_envTheory.bir_var_name_def,
      bir_envTheory.bir_env_read_UPDATE,
      bir_envTheory.bir_var_name_def,
      bir_envTheory.bir_env_lookup_UPDATE,
      bir_envTheory.bir_var_type_def,
      bir_envTheory.bir_env_lookup_type_def,
      bir_valuesTheory.type_of_bir_val_def,
     type_of_bir_imm_def]
QED

Theorem default_riscv_bir_state_FPRS_lookup_type_tmp[local]:
  !ms.
  bir_env_lookup_type "tmp_f0" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "tmp_f0" (BType_Imm Bit64))) /\
  bir_env_lookup_type "tmp_f1" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "tmp_f1" (BType_Imm Bit64))) /\
  bir_env_lookup_type "tmp_f2" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "tmp_f2" (BType_Imm Bit64))) /\
  bir_env_lookup_type "tmp_f3" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "tmp_f3" (BType_Imm Bit64))) /\
  bir_env_lookup_type "tmp_f4" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "tmp_f4" (BType_Imm Bit64))) /\
  bir_env_lookup_type "tmp_f5" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "tmp_f5" (BType_Imm Bit64))) /\
  bir_env_lookup_type "tmp_f6" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "tmp_f6" (BType_Imm Bit64))) /\
  bir_env_lookup_type "tmp_f7" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "tmp_f7" (BType_Imm Bit64))) /\
  bir_env_lookup_type "tmp_f8" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "tmp_f8" (BType_Imm Bit64))) /\
  bir_env_lookup_type "tmp_f9" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "tmp_f9" (BType_Imm Bit64))) /\
  bir_env_lookup_type "tmp_f10" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "tmp_f10" (BType_Imm Bit64))) /\
  bir_env_lookup_type "tmp_f11" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "tmp_f11" (BType_Imm Bit64))) /\
  bir_env_lookup_type "tmp_f12" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "tmp_f12" (BType_Imm Bit64))) /\
  bir_env_lookup_type "tmp_f13" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "tmp_f13" (BType_Imm Bit64))) /\
  bir_env_lookup_type "tmp_f14" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "tmp_f14" (BType_Imm Bit64))) /\
  bir_env_lookup_type "tmp_f15" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "tmp_f15" (BType_Imm Bit64))) /\
  bir_env_lookup_type "tmp_f16" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "tmp_f16" (BType_Imm Bit64))) /\
  bir_env_lookup_type "tmp_f17" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "tmp_f17" (BType_Imm Bit64))) /\
  bir_env_lookup_type "tmp_f18" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "tmp_f18" (BType_Imm Bit64))) /\
  bir_env_lookup_type "tmp_f19" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "tmp_f19" (BType_Imm Bit64))) /\
  bir_env_lookup_type "tmp_f20" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "tmp_f20" (BType_Imm Bit64))) /\
  bir_env_lookup_type "tmp_f21" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "tmp_f21" (BType_Imm Bit64))) /\
  bir_env_lookup_type "tmp_f22" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "tmp_f22" (BType_Imm Bit64))) /\
  bir_env_lookup_type "tmp_f23" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "tmp_f23" (BType_Imm Bit64))) /\
  bir_env_lookup_type "tmp_f24" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "tmp_f24" (BType_Imm Bit64))) /\
  bir_env_lookup_type "tmp_f25" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "tmp_f25" (BType_Imm Bit64))) /\
  bir_env_lookup_type "tmp_f26" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "tmp_f26" (BType_Imm Bit64))) /\
  bir_env_lookup_type "tmp_f27" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "tmp_f27" (BType_Imm Bit64))) /\
  bir_env_lookup_type "tmp_f28" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "tmp_f28" (BType_Imm Bit64))) /\
  bir_env_lookup_type "tmp_f29" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "tmp_f29" (BType_Imm Bit64))) /\
  bir_env_lookup_type "tmp_f30" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "tmp_f30" (BType_Imm Bit64))) /\
  bir_env_lookup_type "tmp_f31" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "tmp_f31" (BType_Imm Bit64)))
Proof
  rw [default_riscv_bir_state_def,
      default_riscv_bir_env_GPRS_def,
      default_riscv_bir_env_FPRS_def,
      bir_env_oldTheory.bir_env_var_is_declared_def,
      bir_envTheory.bir_var_name_def,
      bir_envTheory.bir_env_read_UPDATE,
      bir_envTheory.bir_var_name_def,
      bir_envTheory.bir_env_lookup_UPDATE,
      bir_envTheory.bir_var_type_def,
      bir_envTheory.bir_env_lookup_type_def,
      bir_valuesTheory.type_of_bir_val_def,
     type_of_bir_imm_def]
QED

Theorem default_riscv_bir_state_basic_env_read[local]:
 !ms.
 bir_env_read (BVar "MEM8" (BType_Mem Bit64 Bit8)) (default_riscv_bir_state ms).bst_environ =
   SOME (BVal_Mem Bit64 Bit8 (bir_mmap_w_w2n (bir_mf2mm ms.MEM8)))
Proof
  rw [default_riscv_bir_state_def,
      default_riscv_bir_env_GPRS_def,
      default_riscv_bir_env_FPRS_def,
      default_riscv_bir_env_basic_def,
      bir_envTheory.bir_env_read_UPDATE,
      bir_envTheory.bir_var_name_def,
      bir_envTheory.bir_env_lookup_UPDATE,
      bir_envTheory.bir_var_type_def,
      bir_valuesTheory.type_of_bir_val_def,
      type_of_bir_imm_def,
      bir_immTheory.type_of_bool2b]
QED

Theorem default_riscv_bir_state_basic_lookup_type[local]:
 !ms.
  bir_env_lookup_type "tmp_MEM8" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "tmp_MEM8" (BType_Mem Bit64 Bit8))) /\
  bir_env_lookup_type "tmp_PC" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "tmp_PC" (BType_Imm Bit64))) /\
  bir_env_lookup_type "tmp_COND" (default_riscv_bir_state ms).bst_environ =
   SOME (bir_var_type (BVar "tmp_COND" (BType_Imm Bit1)))
Proof
  rw [default_riscv_bir_state_def,
      default_riscv_bir_env_GPRS_def,
      default_riscv_bir_env_FPRS_def,
      default_riscv_bir_env_basic_def,
      bir_env_oldTheory.bir_env_var_is_declared_def,
      bir_envTheory.bir_var_name_def,
      bir_envTheory.bir_env_read_UPDATE,
      bir_envTheory.bir_var_name_def,
      bir_envTheory.bir_env_lookup_UPDATE,
      bir_envTheory.bir_var_type_def,
      bir_envTheory.bir_env_lookup_type_def,
      bir_valuesTheory.type_of_bir_val_def,
     type_of_bir_imm_def]
QED

Theorem default_riscv_bir_state_satisfies_rel_thm[local]:
 !ms. riscv_bmr.bmr_extra ms ==>
   bmr_rel riscv_bmr (default_riscv_bir_state ms) ms
Proof
strip_tac >> strip_tac >>
FULL_SIMP_TAC std_ss [bir_lifting_machinesTheory.riscv_bmr_rel_EVAL,
 bir_env_oldTheory.bir_env_var_is_declared_def,bir_envTheory.bir_var_name_def] >>
fs [
  default_riscv_bir_state_GPRS_read,
  default_riscv_bir_state_GPRS_read_tmp,
  default_riscv_bir_state_GPRS_lookup_type,
  default_riscv_bir_state_GPRS_lookup_type_tmp,
  default_riscv_bir_state_FPRS_read,
  default_riscv_bir_state_FPRS_read_tmp,
  default_riscv_bir_state_FPRS_lookup_type,
  default_riscv_bir_state_FPRS_lookup_type_tmp,
  default_riscv_bir_state_basic_env_read,
  default_riscv_bir_state_basic_lookup_type
 ] >>
FULL_SIMP_TAC std_ss [default_riscv_bir_state_def,bir_lifting_machinesTheory.bmr_extra_RISCV] >>
FULL_SIMP_TAC (srw_ss()) [bir_exp_liftingTheory.bir_load_w2n_mf_simp_thm] >>
METIS_TAC []
QED

Theorem exist_bir_of_riscv_thm:
 !ms vars.
    riscv_wf_varset vars ==>
    riscv_bmr.bmr_extra ms ==>
    ?bs.
      (bmr_rel riscv_bmr bs ms /\ (bs.bst_status = BST_Running) /\
       bir_env_vars_are_initialised bs.bst_environ vars)
Proof
REPEAT STRIP_TAC >> 
EXISTS_TAC ``default_riscv_bir_state ms`` >>
ASSUME_TAC (SPEC ``ms:riscv_state`` default_riscv_bir_state_satisfies_rel_thm) >>
REV_FULL_SIMP_TAC std_ss [] >>
STRIP_TAC >- (
  EVAL_TAC
) >>
irule bir_env_oldTheory.bir_env_vars_are_initialised_SUBSET >>
Q.EXISTS_TAC `riscv_vars` >>
FULL_SIMP_TAC std_ss [riscv_wf_varset_def] >>
SIMP_TAC std_ss [riscv_vars_def] >>
FULL_SIMP_TAC std_ss [bir_env_oldTheory.bir_env_vars_are_initialised_INSERT] >>
REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [bir_env_oldTheory.bir_env_var_is_initialised_def] >>
FULL_SIMP_TAC std_ss [bir_envTheory.bir_var_name_def, default_riscv_bir_state_def,
                        bir_envTheory.bir_env_lookup_UPDATE] >>
EVAL_TAC  >>
FULL_SIMP_TAC std_ss [bir_valuesTheory.bir_val_t_11,
                      bir_immTheory.type_of_bir_imm_def,
                      bir_valuesTheory.type_of_bir_val_EQ_ELIMS]
QED

Theorem set_of_address_in_all_address_labels_thm[local]:
!l adds.
    l IN {BL_Address (Imm64 ml') | ml' IN adds} ==>
    l IN {l | IS_BL_Address l}
Proof
REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [pred_setTheory.GSPECIFICATION, bir_program_labelsTheory.IS_BL_Address_def]
QED

Theorem bir_is_lifted_prog_MULTI_STEP_EXEC_compute[local]:
!mu bs bs' ms ml (p:'a bir_program_t) (r:(64, 8, 'b) bir_lifting_machine_rec_t)
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
Proof
REPEAT STRIP_TAC >>
ASSUME_TAC (ISPECL [``r:(64, 8, 'b) bir_lifting_machine_rec_t``, ``mu:64 word_interval_t``,
                    ``mms:(word64# word8 list) list``,
                    ``p:'a bir_program_t``] bir_is_lifted_prog_MULTI_STEP_EXEC) >>
REV_FULL_SIMP_TAC std_ss [] >>
QSPECL_X_ASSUM ``!n ms bs. _`` [`n'`, `ms`, `bs`] >>
REV_FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_state_is_terminated_def]
QED

Theorem bir_riscv_block_pc[local]:
 !bs ms ml.
    bmr_rel riscv_bmr bs ms ==>
    (riscv_ts.ctrl ms = ml) ==>
    (bs.bst_status = BST_Running) ==>
    (bs.bst_pc = bir_block_pc (BL_Address (Imm64 ml)))
Proof
REPEAT GEN_TAC >>
REPEAT DISCH_TAC >>
FULL_SIMP_TAC (std_ss++holBACore_ss++bir_wm_SS)
  [riscv_bmr_rel_EVAL, bir_block_pc_def, riscv_ts_def]
QED

Theorem riscv_bir_get_ht_conseq_from_m_ante[local]:
!bs p bpre bpost mpre ms ml mls.
    bir_cont p bir_exp_true (BL_Address (Imm64 ml))
      {BL_Address (Imm64 ml') | ml' IN mls} {} bpre bpost ==>
    bir_pre_riscv_to_bir mpre bpre ==>
    mpre ms ==>
    bmr_rel riscv_bmr bs ms ==>
    (bs.bst_status = BST_Running) ==>
    bir_env_vars_are_initialised bs.bst_environ
      (bir_vars_of_program p UNION bir_vars_of_exp bpre) ==>
    (bs.bst_pc = bir_block_pc (BL_Address (Imm64 ml))) ==>
    (?bs'.
     (bir_weak_trs {BL_Address (Imm64 ml') | ml' IN mls} p bs =
       SOME bs') /\
     (bir_eval_exp (bpost bs'.bst_pc.bpc_label) bs'.bst_environ =
       SOME bir_val_true)
    )
Proof
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
  METIS_TAC [bir_pre_riscv_to_bir_def, bir_bool_expTheory.bir_is_bool_exp_env_def]
) >>
FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss)
  [bir_bool_expTheory.bir_eval_exp_TF,
   bir_bool_expTheory.bir_is_bool_exp_env_REWRS,
   bir_block_pc_def] >>
REV_FULL_SIMP_TAC (std_ss++holBACore_ss) []
QED

Theorem bir_riscv_exec_in_end_label_set[local]:
 !c_addr_labels ms' bs bs' mls p n n' lo li.
    (* Execution from BIR HT *)
    (bir_exec_to_addr_label_n p bs n' = BER_Ended lo n c_addr_labels bs') ==>
    (n' > 0) ==>
    ~bir_state_is_terminated bs' ==>
    (bs'.bst_pc = bir_block_pc (BL_Address li)) ==>
    ((bir_block_pc (BL_Address li)).bpc_label IN
         {BL_Address (Imm64 ml') | ml' IN mls}) ==>
    (* BMR relation between the final states *)
    bmr_rel riscv_bmr bs' ms' ==>
    c_addr_labels > 0 /\
    (ms'.c_PC ms'.procID) IN mls
Proof
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
subgoal `(ms'.c_PC ms'.procID) IN mls` >- (
  subgoal `bs'.bst_pc = bir_block_pc (BL_Address (Imm64 (ms'.c_PC ms'.procID)))` >- (
    REV_FULL_SIMP_TAC (std_ss++holBACore_ss)
      [bir_state_is_terminated_def,
       GEN_ALL bir_lifting_machinesTheory.riscv_bmr_rel_EVAL]
  ) >>
  REV_FULL_SIMP_TAC (std_ss++holBACore_ss++pred_setLib.PRED_SET_ss)
    [bir_programTheory.bir_block_pc_def] >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) []
) >>
FULL_SIMP_TAC std_ss []
QED

Theorem bir_inter_exec_notin_end_label_set[local]:
 !mls p bs l n0 n' n'' lo lo' c_st c_st' bs' bs''.
    (bir_exec_to_labels {BL_Address (Imm64 ml') | ml' IN mls} p bs =
       BER_Ended l c_st n0 bs') ==>
    (bir_exec_to_addr_label_n p bs n'' = BER_Ended lo' c_st' n'' bs'') ==>
    c_st' < c_st ==>
    n'' > 0 ==>
    ~bir_state_is_terminated bs'' ==>
    bs''.bst_pc.bpc_label NOTIN
      {BL_Address (Imm64 ml') | ml' IN mls}
Proof
REPEAT STRIP_TAC >>
subgoal `~bir_state_COUNT_PC (F,
	  (\pc.
	       (pc.bpc_index = 0) /\
	       pc.bpc_label IN {BL_Address (Imm64 ml') | ml' IN mls}))
	      (bir_exec_infinite_steps_fun p bs c_st')` >- (
  FULL_SIMP_TAC std_ss [bir_exec_to_labels_def, bir_exec_to_labels_n_def,
			bir_exec_steps_GEN_SOME_EQ_Ended] >>
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
subgoal `bs''.bst_pc.bpc_index = 0` >- (
  METIS_TAC [bir_exec_to_addr_label_n_ended_running, bir_state_is_terminated_def]
) >>
FULL_SIMP_TAC std_ss [bir_state_COUNT_PC_def, bir_exec_to_addr_label_n_def,
		      bir_exec_to_labels_n_def,
		      bir_exec_steps_GEN_SOME_EQ_Ended] >>
REV_FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_state_is_terminated_def]
QED

Theorem bir_riscv_inter_exec[local]:
 !n' c_addr_labels n0 ms ml mls bs bs' p lo l c_st n mu mms.
    bir_is_lifted_prog riscv_bmr mu mms p ==>
    EVERY (bmr_ms_mem_contains riscv_bmr ms) mms ==>
    (riscv_ts.ctrl ms = ml) ==>
    (MEM (BL_Address (Imm64 ml)) (bir_labels_of_program p)) ==>
    bmr_rel riscv_bmr bs ms ==>
    ~bir_state_is_terminated bs ==>
    (bs.bst_pc = bir_block_pc (BL_Address (Imm64 ml))) ==>
    (bir_exec_to_labels {BL_Address (Imm64 ml') | ml' IN mls} p bs = BER_Ended l c_st n0 bs') ==>
    ~bir_state_is_terminated bs' ==>
    (bir_exec_to_addr_label_n p bs n' = BER_Ended lo c_st c_addr_labels bs') ==>
    (!n''.
       n'' < c_addr_labels /\ n'' > 0 ==>
       ?ms''.
	 (FUNPOW_OPT riscv_bmr.bmr_step_fun n'' ms = SOME ms'') /\
	 (ms''.c_PC ms''.procID) NOTIN mls)
Proof
REPEAT STRIP_TAC >>
Q.SUBGOAL_THEN `c_addr_labels = n'` (fn thm => FULL_SIMP_TAC std_ss [thm]) >- (
  FULL_SIMP_TAC std_ss [bir_exec_to_addr_label_n_def, bir_exec_to_labels_n_def] >>
  METIS_TAC [bir_exec_steps_GEN_SOME_EQ_Ended_pc_counts]
) >>
subgoal `?lo' c_st' c_addr_labels' bs''.
         bir_exec_to_addr_label_n p bs n'' =
           BER_Ended lo' c_st' c_addr_labels' bs''` >- (
  FULL_SIMP_TAC std_ss [bir_exec_to_addr_label_n_def, bir_exec_to_labels_n_def] >>
  METIS_TAC [bir_exec_steps_GEN_decrease_max_steps_Ended_SOME]
) >>
subgoal `~bir_state_is_terminated bs''` >- (
  FULL_SIMP_TAC std_ss [bir_exec_to_addr_label_n_def, bir_exec_to_labels_n_def] >>
  METIS_TAC [bir_exec_steps_GEN_decrease_max_steps_Ended_terminated]
) >>
Q.SUBGOAL_THEN `c_addr_labels' = n''` (fn thm => FULL_SIMP_TAC std_ss [thm]) >- (
  FULL_SIMP_TAC std_ss [bir_exec_to_addr_label_n_def, bir_exec_to_labels_n_def] >>
  METIS_TAC [bir_exec_steps_GEN_SOME_EQ_Ended_pc_counts]
) >>
subgoal `?ms'' li.
         bmr_rel riscv_bmr bs'' ms'' /\
         EVERY (bmr_ms_mem_contains riscv_bmr ms'') mms /\
         bmr_ms_mem_unchanged riscv_bmr ms ms'' mu /\
         MEM (BL_Address li) (bir_labels_of_program p) /\
         (bs''.bst_pc = bir_block_pc (BL_Address li)) /\
         (FUNPOW_OPT riscv_bmr.bmr_step_fun n'' ms = SOME ms'')` >- (
  IMP_RES_TAC bir_is_lifted_prog_MULTI_STEP_EXEC_compute >>
  METIS_TAC []
) >>
subgoal `bs''.bst_pc.bpc_label NOTIN
           {BL_Address (Imm64 ml') | ml' IN mls}` >- (
  subgoal `c_st' < c_st` >- (
    METIS_TAC [bir_exec_to_labels_def, bir_exec_to_addr_label_n_def,
	       bir_exec_to_labels_n_def,
	       bir_exec_steps_GEN_decrease_max_steps_Ended_steps_taken]
  ) >>
  METIS_TAC [bir_inter_exec_notin_end_label_set]
) >>
Q.EXISTS_TAC `ms''` >>
subgoal `bs''.bst_pc = bir_block_pc (BL_Address (Imm64 (ms''.c_PC ms''.procID)))` >- (
  REV_FULL_SIMP_TAC (std_ss++holBACore_ss)
    [GEN_ALL riscv_bmr_rel_EVAL, bir_state_is_terminated_def]
) >>
FULL_SIMP_TAC (std_ss++holBACore_ss++bir_wm_SS++pred_setLib.PRED_SET_ss)
  [bir_block_pc_def]
QED

Theorem riscv_lift_contract_thm:
  !p mms ml mls mu mpre mpost bpre bpost.
    MEM (BL_Address (Imm64 ml)) (bir_labels_of_program p) ==>
    bir_cont p bir_exp_true (BL_Address (Imm64 ml))
	{BL_Address (Imm64 ml') | ml' IN mls} {} bpre bpost ==>
      bir_is_lifted_prog riscv_bmr mu mms p ==>
      riscv_wf_varset (bir_vars_of_program p UNION bir_vars_of_exp bpre) ==>
      bir_pre_riscv_to_bir mpre bpre ==>
      bir_post_bir_to_riscv mpost bpost {BL_Address (Imm64 ml') | ml' IN mls} ==>
      riscv_cont mms ml mls mpre mpost
Proof
REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [riscv_cont_def, t_jgmt_def] >>
REPEAT STRIP_TAC >>
IMP_RES_TAC (SPECL [``ms:riscv_state``,
                    ``(bir_vars_of_program p) UNION (bir_vars_of_exp bpre)``]
                  exist_bir_of_riscv_thm) >>
IMP_RES_TAC bir_riscv_block_pc >>
IMP_RES_TAC riscv_bir_get_ht_conseq_from_m_ante >>
FULL_SIMP_TAC std_ss [bir_weak_trs_EQ] >>
IMP_RES_TAC bir_exec_to_labels_TO_exec_to_addr_label_n >>
IMP_RES_TAC bir_is_lifted_prog_MULTI_STEP_EXEC_compute >>
REV_FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
Q.EXISTS_TAC `ms'` >>
subgoal `riscv_bmr.bmr_extra ms'` >- (
 FULL_SIMP_TAC std_ss [bmr_rel_def]
) >>
subgoal `mpost ms'` >- (
  FULL_SIMP_TAC std_ss [bir_post_bir_to_riscv_def] >>
  QSPECL_X_ASSUM ``!ms. _``
    [`ms'`, `bs'`, `(bir_block_pc (BL_Address li)).bpc_label`] >>
  REV_FULL_SIMP_TAC std_ss []
) >>
FULL_SIMP_TAC std_ss [] >>
SIMP_TAC (std_ss++bir_wm_SS) [riscv_ts_def,
                              riscv_weak_trs_def] >>
Q.EXISTS_TAC `c_addr_labels` >>
IMP_RES_TAC bir_riscv_exec_in_end_label_set >>
FULL_SIMP_TAC std_ss [] >>
METIS_TAC [bir_state_is_terminated_def, bir_riscv_inter_exec]
QED

val _ = export_theory();
