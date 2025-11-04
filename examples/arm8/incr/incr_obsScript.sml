open HolKernel boolLib Parse bossLib;

open bir_obs_modelLib;

open bslSyntax;

open incrTheory;

val _ = new_theory "incr_obs";

val mem_bounds =
 let
   open wordsSyntax;
   val (mem_base, mem_len) = (Arbnum.fromHexString "0xFFCC0000",
                              Arbnum.fromHexString  "0x10000");
   val mem_end = (Arbnum.- (Arbnum.+ (mem_base, mem_len), Arbnum.fromInt 128));
 in
   pairSyntax.mk_pair
       (mk_wordi (mem_base, 64),
        mk_wordi (mem_end, 64))
  end;

fun prog_obs_inst prog obs_type = proginst_fun_gen obs_type prog;

val bir_incr_prog_obs =
 let 
   val prog_tm = (snd o dest_eq o concl) bir_incr_prog_def;
   val prog_tm = inst [Type`:'observation_type` |-> Type`:'obs_type`] prog_tm;
   val om = get_obs_model "mem_address_pc";
 in
   (#add_obs om) mem_bounds (prog_obs_inst prog_tm (#obs_hol_type om))
 end;

Definition incr_obs_prog_def:
 incr_obs_prog = ^bir_incr_prog_obs
End

val _ = export_theory ();
