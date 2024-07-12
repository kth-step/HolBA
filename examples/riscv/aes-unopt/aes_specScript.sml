open HolKernel boolLib Parse bossLib;

(*
open bir_programSyntax bir_program_labelsTheory;
open bir_immTheory bir_valuesTheory bir_expTheory bir_exp_immTheory;
open bir_tsTheory bir_bool_expTheory bir_programTheory;
*)

open bir_predLib;

open aesTheory;

val _ = new_theory "aes_spec";

(* ------------------ *)
(* Program boundaries *)
(* ------------------ *)

Definition aes_init_addr_def: (* *)
 aes_init_addr : word64 = 0x628w
End

Definition aes_end_addr_def: (* 0xaf4w, 0x7b0w, 0x6f0w, 0x6b0w *)
 aes_end_addr : word64 = 0x7b0w (* 122m theory build time *)
End

(* -------------- *)
(* BSPEC contract *)
(* -------------- *)

val vars_of_prog_thm =
(SIMP_CONV (std_ss++HolBASimps.VARS_OF_PROG_ss++pred_setLib.PRED_SET_ss)
   [bir_aes_prog_def] THENC
  EVAL)
 ``bir_vars_of_program (bir_aes_prog : 'observation_type bir_program_t)``;

val all_vars = (pred_setSyntax.strip_set o snd o dest_eq o concl) vars_of_prog_thm;
val registervars = List.filter ((fn s => s <> "MEM8") o (stringSyntax.fromHOLstring o fst o bir_envSyntax.dest_BVar)) all_vars;
val registervars_tm = listSyntax.mk_list (registervars, (type_of o hd) registervars);

Definition bir_aes_registervars_def:
 bir_aes_registervars = ^registervars_tm
End

val rounds = 14; (* actually, could be 10, 12 or 14 depending on key size; but simplify for now *)
val roundsrn = "x11";

val blocksize = 128; (* bits *)
val roundkeysize = blocksize;
val roundkeys = rounds + 1;

val rkrn = "x10";
val rkbufsz = (roundkeysize div 8) * roundkeys;
val Te_rn = "x14";
val Te_sz = 4*4*256; (* optimization lookup table (S-box, shift, etc) *)
val inblkrn = "x12";
val blksz = blocksize div 8;
val sprn = "x2";


val bspec_aes_pre_tm = bslSyntax.bandl
 ([bslSyntax.beq (bslSyntax.bden (bslSyntax.bvarimm64 roundsrn), bslSyntax.bconst64 rounds),
   mem_addrs_stack_disj_reg_bir_tm sprn rkrn,
   mem_addrs_stack_disj_reg_bir_tm sprn inblkrn,
   mem_addrs_stack_disj_reg_bir_tm sprn Te_rn,
   mem_area_disj_reg_bir_tm (rkrn, rkbufsz) (inblkrn, blksz),
   mem_area_disj_reg_bir_tm (Te_rn, Te_sz)  (inblkrn, blksz),
   mem_area_disj_reg_bir_tm (Te_rn, Te_sz)  (rkrn, rkbufsz)]
  @(List.map (mem_addrs_aligned_prog_disj_bir_tm o
   stringSyntax.fromHOLstring o fst o bir_envSyntax.dest_BVar)
      ((fst o listSyntax.dest_list) registervars_tm)));

Definition bspec_aes_pre_def:
  bspec_aes_pre : bir_exp_t =
   ^bspec_aes_pre_tm
End

val _ = export_theory ();
