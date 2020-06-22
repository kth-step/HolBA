signature ScamvSimps =
sig
   include Abbrev

   (* Simplifies loads from stores *)
   val bir_load_store_ss : simpLib.ssfrag		      
end
