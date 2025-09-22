open HolKernel boolLib Parse bossLib;

open bir_predLib;

val _ = new_theory "aes_unopt_spec";

(* ------------------ *)
(* Program boundaries *)
(* ------------------ *)

Definition aes_init_addr_def: (* *)
 aes_init_addr : word64 = 0x628w
End

Definition aes_end_addr_def: (* 0xaf4w, 0x7b0w, 0x6f0w, 0x6b0w *)
 aes_end_addr : word64 = 0xaf4w (* 0x7b0w (* 122m theory build time *) *)
End

(* -------------- *)
(* BSPEC contract *)
(* -------------- *)
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
  @(List.map (mem_addrs_aligned_prog_disj_bir_tm mem_params_standard)
      [sprn, rkrn, inblkrn, Te_rn]));

Definition bspec_aes_pre_def:
  bspec_aes_pre : bir_exp_t =
   ^bspec_aes_pre_tm
End

val _ = export_theory ();
