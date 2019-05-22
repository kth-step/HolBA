signature bir_expSimps =
sig
   include Abbrev

   (* Experimental SS for use with simplifying boolean expressions *)
   val bir_is_bool_ss : simpLib.ssfrag

   (* For usage when having case statements of type/ value option. *)
   val bir_type_val_opt_ss : simpLib.ssfrag
end
