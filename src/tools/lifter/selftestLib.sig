(* Dummy so that we don't have to make separate Holmake stuff for test_bmr*)
signature selftestLib = sig

  include PPBackEnd;

end;

signature test_bmr = sig
  type lift_inst_cache;

  include Arbnum;
  include Abbrev;
  include bir_inst_liftingLibTypes;

  (* For printing stylish comments to log *)
  val print_log_with_style : PPBackEnd.pp_style list -> bool -> string -> unit
  (* For printing basic comments to log *)
  val print_log : bool -> string -> unit
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
