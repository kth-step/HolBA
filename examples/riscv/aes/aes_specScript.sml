open HolKernel boolLib Parse bossLib;

open distribute_generic_stuffLib;

open bir_programSyntax bir_program_labelsTheory;
open bir_immTheory bir_valuesTheory bir_expTheory bir_exp_immTheory;
open bir_tsTheory bir_bool_expTheory bir_programTheory;

open bir_symbLib;

open distribute_generic_stuffTheory;

open aesTheory;

val _ = new_theory "aes_spec";

(* ------------------ *)
(* Program boundaries *)
(* ------------------ *)

Definition aes_init_addr_def:
 aes_init_addr : word64 = 0x088w
End

Definition aes_end_addr_def:
 aes_end_addr : word64 = 0x208w
End

(* -------------- *)
(* BSPEC contract *)
(* -------------- *)

val registervars_tm = ``[
    BVar "x31" (BType_Imm Bit64);
    BVar "x30" (BType_Imm Bit64);
    BVar "x29" (BType_Imm Bit64);
    BVar "x28" (BType_Imm Bit64);
    BVar "x18" (BType_Imm Bit64);
    BVar "x17" (BType_Imm Bit64);
    BVar "x16" (BType_Imm Bit64);
    BVar "x15" (BType_Imm Bit64);
    BVar "x14" (BType_Imm Bit64);
    BVar "x13" (BType_Imm Bit64);
    BVar "x12" (BType_Imm Bit64);
    BVar "x11" (BType_Imm Bit64);
    BVar "x10" (BType_Imm Bit64);
    BVar "x9" (BType_Imm Bit64);
    BVar "x8" (BType_Imm Bit64);
    BVar "x7" (BType_Imm Bit64);
    BVar "x6" (BType_Imm Bit64);
    BVar "x5" (BType_Imm Bit64);
    BVar "x2" (BType_Imm Bit64);
    BVar "x1" (BType_Imm Bit64)
  ]
``;

Definition bir_aes_registervars_def:
 bir_aes_registervars = ^registervars_tm
End

val bspec_aes_pre_tm = bslSyntax.bandl
 (List.map (mem_addrs_aligned_prog_disj_bir_tm o
   stringSyntax.fromHOLstring o fst o bir_envSyntax.dest_BVar)
  ((fst o listSyntax.dest_list) registervars_tm));

Definition bspec_aes_pre_def:
  bspec_aes_pre : bir_exp_t =
   ^bspec_aes_pre_tm
End

val _ = export_theory ();
