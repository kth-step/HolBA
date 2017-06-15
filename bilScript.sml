(* ========================================================================= *)
(* FILE          : bilScript.sml                                             *)
(* DESCRIPTION   : A model of BAP Intermediate Language.                     *)
(*                 Based on Anthony Fox's binary words treatment.            *)
(* AUTHOR        : (c) Roberto Metere, KTH - Royal Institute of Technology   *)
(* DATE          : 2015                                                      *)
(* ========================================================================= *)

open HolKernel Parse boolLib bossLib;
open wordsTheory bitstringTheory;
open bil_auxiliaryTheory bil_immTheory bil_valuesTheory;
open bil_imm_expTheory bil_mem_expTheory bil_envTheory;
open bil_expTheory bil_programTheory bil_typingTheory;
open wordsLib;

val _ = new_theory "bil";


val _ = export_theory();
