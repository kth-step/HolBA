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

val _ = new_theory "poly1305_spec";

(****************************************************************)
(************ HACL* - Specification   **********************)
(*
let encode (w:word) =
  (pow2 (8 * length w)) `fadd` (little_endian w)

let rec poly (txt:text) (r:e:elem) : Tot elem (decreases (length txt)) =
  if length txt = 0 then zero
  else
    let a = poly (Seq.tail txt) r in
    let n = encode (Seq.head txt) in
    (n `fadd` a) `fmul` r

let encode_r (rb:word_16) =
  (little_endian rb) &| 0x0ffffffc0ffffffc0ffffffc0fffffff

let finish (a:elem) (s:word_16) : Tot tag =
  let n = (a + little_endian s) % pow2 128 in
  little_bytes 16ul n

let rec encode_bytes (txt:bytes) : Tot text (decreases (length txt)) =
  if length txt = 0 then createEmpty
  else
    let w, txt = split txt (min (length txt) 16) in
    append_last (encode_bytes txt) w

let poly1305 (msg:bytes) (k:key) : Tot tag =
  let text = encode_bytes msg in
  let r = encode_r (slice k 0 16) in
  let s = slice k 16 32 in
  finish (poly text r) s
*)

(* ** libjade EasyCrypt spec matches the poly HACL* function over Zp ** *)

(*
type Zp_msg = zp list. 

op poly1305_loop (r : zp) (m : Zp_msg) (n : int) =
  foldl (fun h i => (h + oget (onth m i)) * r) Zp.zero (iota_ 0 n).

op poly1305_ref (r : zp) (s : int) (m : Zp_msg) =
  let n = size m in
  let h' = poly1305_loop r m n
      in  (((asint h') %% 2^128) + s) %% 2^128.
*)

(* ** libjade imperative version *)

(*
   proc poly1305(r:zp, s : int, m : Zp_msg) = {
       var h,n,i;

       n <- size m;
       i <- 0;
       h <- Zp.zero;

       while (i < n) {
         h <- (h + oget (onth m i)) * r;
         i <- i + 1;
       }
       return (((asint h) %% 2^128) + s) %% 2^128;
   }
*)

(* ---------------- *)
(* Block boundaries *)
(* ---------------- *)

(* U8TO32 *)

Definition poly1305_u8to32_init_addr_def:
 poly1305_u8to32_init_addr : word64 = 0x10488w
End

Definition poly1305_u8to32_end_addr_def:
 poly1305_u8to32_end_addr : word64 = 0x104b4w
End

(* --------------- *)
(* BSPEC contracts *)
(* --------------- *)

val bspec_poly1305_u8to32_pre_tm = bslSyntax.bandl [
  mem_addrs_aligned_prog_disj_bir_tm mem_params_standard "x10"
];

Definition bspec_poly1305_u8to32_pre_def:
 bspec_poly1305_u8to32_pre : bir_exp_t =
  ^bspec_poly1305_u8to32_pre_tm
End

val _ = export_theory ();
