signature bir_embexp_paramsLib = sig

  (* platform parameters *)
  (* ======================================== *)
  val bir_embexp_params_code   : Arbnum.num (* base address for placement *)
  val bir_embexp_params_memory : Arbnum.num * Arbnum.num (* base, length *)

end
