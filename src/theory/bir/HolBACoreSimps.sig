signature HolBACoreSimps =
sig
   include Abbrev

   (* a list over rewrite theorems for all HolBA BIR types *)
   val bir_TYPES_thms : thm list;

   (* Rewrite rules for all the types defined as part of the HolBIR formalisation. *)
   val bir_TYPES_ss : simpLib.ssfrag;

   (* Simple rewrites *)
   val bir_SIMPLE_REWRS_ss : simpLib.ssfrag

   (* All holBA stuff *)
   val holBACore_ss : simpLib.ssfrag

   (* Simplifies bir_var_set_is_well_typed of variable sets *)
   val bir_var_set_is_well_typed_ss : simpLib.ssfrag

   (* Simplifies intersections of variable sets *)
   val bir_inter_var_set_ss : simpLib.ssfrag

   (* Simplifies unions of variable sets *)
   val bir_union_var_set_ss : simpLib.ssfrag

   (* Simplifies loads from stores *)
   val bir_load_store_ss : simpLib.ssfrag
end
