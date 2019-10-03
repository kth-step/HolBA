signature bir_prog_gen_sliceLib = sig

  (* ---------------------- *)
  (* Hamed's entry function *)
  (* ---------------------- *)

  (* parameters:
       - name of the .da file we want to extract slices from
       - the base address where the program will be located in memory
       - length of the snippet to be taken
       (base and length are used to make sure that jumps don't happen outside the allowed region (is that the snippet?)
   *)
  val bir_prog_gen_arm8_slice : int -> string list

end
