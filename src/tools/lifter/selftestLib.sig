open Abbrev
open bir_inst_liftingLibTypes
open PPBackEnd
open bir_inst_liftingLib

signature test_bmr = sig
  type lift_inst_cache

  (* For printing stylish comments to log *)
  val print_log_with_style : pp_style list -> bool -> string -> unit
  (* For printing basic comments to log *)
  val print_log : bool -> string -> unit
  (* This lifts single instructions, but uses a cache to remedy duplication of computation *)
  val lift_instr_cached :
     bool ->
       num * num ->
	 thm * thm ->
	   lift_inst_cache ->
	     num ->
	       string ->
		 string option ->
		   thm option * bir_inst_liftingExn_data option * string *
		   lift_inst_cache
  (* For lifting a single instruction *)
  val lift_instr :
     num ->
       num ->
	 num ->
	   string ->
	     string option ->
	       thm option * bir_inst_liftingExn_data option * string
  (* For lifting a list of instructions *)
  val lift_instr_list :
     num ->
       num ->
	 num ->
	   string list ->
	     int * int *
	     (thm option * bir_inst_liftingExn_data option * string) list
  (* Prints the final results *)
  val final_results : string -> string list -> unit
end

signature selftestLib = sig

  (* TODO: Put test instances here? *)
  val sty_OK : pp_style list
  val sty_CACHE : pp_style list
  val sty_FAIL : pp_style list
  val sty_HEADER : pp_style list

end
