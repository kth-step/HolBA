open HolKernel boolLib Parse bossLib;

open markerTheory;

open bir_programSyntax bir_program_labelsTheory;
open bir_immTheory bir_valuesTheory bir_expTheory;
open bir_tsTheory bir_bool_expTheory bir_programTheory;

open bir_arm8_backlifterTheory;
open bir_backlifterLib;
open bir_compositionLib;

open bir_lifting_machinesTheory;
open bir_typing_expTheory;
open bir_htTheory;

open total_program_logicTheory;
open total_ext_program_logicTheory;

open jgmt_rel_bir_contTheory;

open pred_setTheory;

open program_logicSimps;

open bir_env_oldTheory;
open bir_program_varsTheory;

open maxTheory;
open max_spec_arm8Theory;
open max_spec_birTheory;
open max_symb_transfTheory;

val _ = new_theory "max_prop";

(* --------------------------------- *)
(* Backlifting BIR contract to ARMv8 *)
(* --------------------------------- *)

val arm8_cont_max_thm =
 get_arm8_contract_thm
  bspec_cont_max max_init_addr_def [max_end_addr_def]
  bir_max_progbin_def
  arm8_max_pre_def arm8_max_post_def
  bir_max_prog_def
  [bspec_max_pre_def]
  bspec_max_pre_def max_arm8_pre_imp_bspec_pre_thm
  [bspec_max_post_def] max_arm8_post_imp_bspec_post_thm
  bir_max_arm8_lift_THM;

Theorem arm8_cont_max:
 arm8_cont bir_max_progbin max_init_addr {max_end_addr}
  (arm8_max_pre pre_x0 pre_x1)
  (arm8_max_post pre_x0 pre_x1)
Proof
 ACCEPT_TAC arm8_cont_max_thm
QED

(* ------------------------ *)
(* Unfolded ARMv8 contract  *)
(* ------------------------ *)

val readable_thm = computeLib.RESTR_EVAL_RULE [``arm8_weak_trs``] arm8_cont_max;
(*
val readable_thm =
    []
   ⊢ ∀s. s.PC = 1816w ⇒
         (¬s.SCTLR_EL1.E0E ∧ s.PSTATE.EL = 0w ∧ s.exception = NoException ∧
          ¬s.SCTLR_EL1.SA0 ∧ ¬s.TCR_EL1.TBI0 ∧ ¬s.TCR_EL1.TBI1) ∧
         (s.MEM 1816w = 31w ∧ s.MEM 1817w = 0w ∧ s.MEM 1818w = 1w ∧
          s.MEM 1819w = 235w ∧ s.MEM 1820w = 0w ∧ s.MEM 1821w = 32w ∧
          s.MEM 1822w = 129w ∧ s.MEM 1823w = 154w ∧ s.MEM 1824w = 192w ∧
          s.MEM 1825w = 3w ∧ s.MEM 1826w = 95w ∧ s.MEM 1827w = 214w ∧
          s.MEM 1828w = 224w ∧ s.MEM 1829w = 0w ∧ s.MEM 1830w = 128w ∧
          s.MEM 1831w = 82w ∧ s.MEM 1832w = 192w ∧ s.MEM 1833w = 3w ∧
          s.MEM 1834w = 95w ∧ s.MEM 1835w = 214w) ∧ s.REG 0w = pre_x0 ∧
         s.REG 1w = pre_x1 ⇒
         ∃s'.
           (∃n. (n > 0 ∧
                 FUNPOW (λx. option_CASE x NONE NextStateARM8) n (SOME s) =
                 SOME s' ∧ s'.PC ∈ {1824w}) ∧
                ∀n'.
                  n' < n ∧ n' > 0 ⇒
                  ∃ms''.
                    FUNPOW (λx. option_CASE x NONE NextStateARM8) n' (SOME s) =
                    SOME ms'' ∧ ms''.PC ∉ {1824w}) ∧
           (¬s'.SCTLR_EL1.E0E ∧ s'.PSTATE.EL = 0w ∧
            s'.exception = NoException ∧ ¬s'.SCTLR_EL1.SA0 ∧
            ¬s'.TCR_EL1.TBI0 ∧ ¬s'.TCR_EL1.TBI1) ∧
           (s'.MEM 1816w = 31w ∧ s'.MEM 1817w = 0w ∧ s'.MEM 1818w = 1w ∧
            s'.MEM 1819w = 235w ∧ s'.MEM 1820w = 0w ∧ s'.MEM 1821w = 32w ∧
            s'.MEM 1822w = 129w ∧ s'.MEM 1823w = 154w ∧ s'.MEM 1824w = 192w ∧
            s'.MEM 1825w = 3w ∧ s'.MEM 1826w = 95w ∧ s'.MEM 1827w = 214w ∧
            s'.MEM 1828w = 224w ∧ s'.MEM 1829w = 0w ∧ s'.MEM 1830w = 128w ∧
            s'.MEM 1831w = 82w ∧ s'.MEM 1832w = 192w ∧ s'.MEM 1833w = 3w ∧
            s'.MEM 1834w = 95w ∧ s'.MEM 1835w = 214w) ∧
           (s'.REG 0w = pre_x0 ∨ s'.REG 0w = pre_x1) ∧ pre_x0 ≤₊ s'.REG 0w ∧
           pre_x1 ≤₊ s'.REG 0w: thm
*)

Theorem arm8_cont_max_full = GEN_ALL readable_thm;

val _ = export_theory ();
