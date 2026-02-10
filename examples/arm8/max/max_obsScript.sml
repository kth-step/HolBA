open HolKernel boolLib Parse bossLib;

open bir_obs_modelLib;

open bslSyntax;

open maxTheory;

val _ = new_theory "max_obs";

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

val bir_max_obs_prog =
 let
   val prog_tm = (snd o dest_eq o concl) bir_max_prog_def;
   val om = get_obs_model "mem_address_pc";
 in
   (#add_obs om) mem_bounds (proginst_fun_gen (#obs_hol_type om) prog_tm)
 end;

Definition bir_max_obs_prog_def:
 bir_max_obs_prog = ^bir_max_obs_prog
End

val _ = export_theory ();
