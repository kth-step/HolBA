open HolKernel Parse boolLib bossLib;
open wordsTheory bitstringTheory HolBACoreSimps;
open bir_auxiliaryTheory bir_immTheory bir_valuesTheory;
open bir_imm_expTheory bir_mem_expTheory bir_envTheory;
open bir_expTheory bir_programTheory bir_typingTheory;
open bir_immSyntax bir_valuesSyntax bir_envSyntax bir_mem_expSyntax;
open bir_imm_expSyntax bir_expSyntax;
open wordsLib;

val _ = new_theory "HolBACore";

(* This is a dummy theory used for loading everything in the core
   directory. This is useful for testing and building a heap. *)

val _ = export_theory();
