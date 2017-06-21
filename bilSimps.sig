signature bilSimps =
sig
   include Abbrev

   (* Rewrite rules for all the types defined as part of the bil formalisation. *)
   val bil_TYPES_ss : simpLib.ssfrag;

   (* Simple rewrites *)
   val bil_SIMPLE_REWRS_ss : simpLib.ssfrag

   (* All bil stuff *)
   val bil_ss : simpLib.ssfrag
end
