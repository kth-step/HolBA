open HolKernel boolLib Parse bossLib;

open markerTheory;

open wordsTheory;

open bir_programSyntax bir_program_labelsTheory;
open bir_immTheory bir_valuesTheory bir_expTheory;
open bir_tsTheory bir_bool_expTheory bir_programTheory;

open bir_riscv_backlifterTheory;
open bir_backlifterLib;
open bir_compositionLib;

open bir_lifting_machinesTheory;
open bir_typing_expTheory;
open bir_htTheory;

open bir_predLib;
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

val _ = new_theory "chacha_spec";

(* ------------- *)
(* ChaCha theory *)
(* ------------- *)

(*
op line (a:idx) (b:idx) (d:idx) (s:int) (m:state) : state =
  let m = m.[a <- (m.[a] + m.[b])] in
  let m = m.[d <- W32.rol (m.[d] +^ m.[a]) s] in m.
*)

Definition chacha_line:
 chacha_line (a:word32) (b:word32) (d:word32) (s:word32)
  (m:word32 -> word32) =
  let m = (a =+ (m a) + (m b)) m in
  let m = (d =+ ((m a) ?? (m d)) #<<~ s) m in
  m
End

(*
op quarter_round a b c d : shuffle =
  line a b d 16 \oo
  line c d b 12 \oo
  line a b d 8  \oo
  line c d b 7.
*)

Definition chacha_quarter_round:
 chacha_quarter_round (a:word32) (b:word32) (c:word32) (d:word32) =
  chacha_line a b d 16w o 
  chacha_line c d b 12w o 
  chacha_line a b d 8w o 
  chacha_line c d b 7w 
End

(*
EVAL ``(chacha_quarter_round
 0x11111111w 0x01020304w 0x9b8d6f43w 0x01234567w) (\x. 0w)``
*)

(*
op column_round : shuffle =
  quarter_round 0 4 8  12 \oo
  quarter_round 1 5 9  13 \oo
  quarter_round 2 6 10 14 \oo
  quarter_round 3 7 11 15.
*)
        
Definition chacha_column_round:
 chacha_column_round =
  chacha_quarter_round 0w 4w 8w 12w o
  chacha_quarter_round 1w 5w 9w 13w o
  chacha_quarter_round 2w 6w 10w 14w o
  chacha_quarter_round 3w 7w 11w 15w
End

(*
op diagonal_round : shuffle =
  quarter_round 0 5 10 15 \oo
  quarter_round 1 6 11 12 \oo
  quarter_round 2 7 8  13 \oo
  quarter_round 3 4 9  14.
*)

Definition chacha_diagonal_round:
 chacha_diagonal_round =
  chacha_quarter_round 0w 5w 10w 15w o
  chacha_quarter_round 1w 6w 11w 12w o
  chacha_quarter_round 2w 7w 8w 13w o
  chacha_quarter_round 3w 4w 9w 14w
End

(*
op double_round: shuffle =
  column_round \oo diagonal_round.
*)

Definition chacha_double_round:
 chacha_double_round =
  chacha_column_round o chacha_diagonal_round
End

(* ---------------- *)
(* Block boundaries *)
(* ---------------- *)

(* keysetup *)

Definition chacha_keysetup_init_addr_def:
 chacha_keysetup_init_addr : word64 = 0x10488w
End

Definition chacha_keysetup_end_addr_def:
 chacha_keysetup_end_addr : word64 = (*0x106a8w*) 0x1053cw
End

(* ivsetup *)

Definition chacha_ivsetup_init_addr_def:
 chacha_ivsetup_init_addr : word64 = 0x106bcw
End

Definition chacha_ivsetup_end_addr_def:
 chacha_ivsetup_end_addr : word64 = 0x10778w
End

(* quarterround *)

Definition chacha_quarterround_init_addr_def:
  chacha_quarterround_init_addr : word64 = 0x108a0w
End

Definition chacha_quarterround_end_addr_def:
 chacha_quarterround_end_addr : word64 = 0x108b4w
End

(* --------------- *)
(* BSPEC contracts *)
(* --------------- *)

(* keysetup *)

val bspec_chacha_keysetup_pre_tm = bslSyntax.bandl [
  mem_addrs_aligned_prog_disj_bir_tm mem_params_standard "x10",
  mem_addrs_aligned_prog_disj_bir_tm mem_params_standard "x11"
];

Definition bspec_chacha_keysetup_pre_def:
 bspec_chacha_keysetup_pre : bir_exp_t =
  ^bspec_chacha_keysetup_pre_tm
End

(* ivsetup *)

val bspec_chacha_ivsetup_pre_tm = bslSyntax.bandl [
  mem_addrs_aligned_prog_disj_bir_tm mem_params_standard "x10",
  mem_addrs_aligned_prog_disj_bir_tm mem_params_standard "x11"
];

Definition bspec_chacha_ivsetup_pre_def:
 bspec_chacha_ivsetup_pre : bir_exp_t =
  ^bspec_chacha_ivsetup_pre_tm
End

(* quarterround *)

val bspec_chacha_quarterround_pre_tm = bslSyntax.bandl [
  mem_addrs_aligned_prog_disj_bir_tm mem_params_standard "x10",
  mem_addrs_aligned_prog_disj_bir_tm mem_params_standard "x11",
  mem_addrs_aligned_prog_disj_bir_tm mem_params_standard "x12"
];

Definition bspec_chacha_quarterround_pre_def:
 bspec_chacha_quarterround_pre : bir_exp_t =
  ^bspec_chacha_quarterround_pre_tm
End

val _ = export_theory ();
