open HolKernel Parse boolLib bossLib;
open wordsTheory bitstringTheory;
open bir_auxiliaryTheory bir_immTheory bir_valuesTheory;
open bir_imm_expTheory bir_mem_expTheory bir_envTheory;
open bir_expTheory bir_programTheory bir_typingTheory;
open bir_immSyntax bir_valuesSyntax bir_envSyntax bir_mem_expSyntax;
open bir_imm_expSyntax bir_expSyntax;
open wordsLib;

val _ = new_theory "bir";


val _ = export_theory();
