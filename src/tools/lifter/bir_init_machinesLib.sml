structure bir_init_machinesLib =
struct
local

  open HolKernel Parse boolLib bossLib;

  open listSyntax;
  open combinSyntax;

  open bir_envSyntax;
  open bir_lifting_machinesTheory;

  val evalthis = snd o dest_eq o concl o EVAL;

  val libname  = "bir_init_machinesLib"
  val ERR      = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname

in

  (*
  val bmr_rec = bir_lifting_machinesLib_instances.m0_bmr_rec_LittleEnd_Process;
  *)

  fun get_init_state_from_bmr_rec (bmr_rec :bir_lifting_machinesLib.bmr_rec) =
    let
      val bmr_const = #bmr_const bmr_rec;

      val bmr_imms = evalthis “(^bmr_const).bmr_imms”;
      val bmr_mem  = evalthis “(^bmr_const).bmr_mem”;

      val bvar_imms = evalthis “MAP (\x. case x of BMLI bv _ => bv) (^bmr_imms)”;
      val bvar_mem  = evalthis “(\x. case x of BMLM bv _ => bv) (^bmr_mem)”;
      val all_bvars = (bvar_mem)::((fst o dest_list) bvar_imms);

      (* the following is copied and adapted from src/tools/exec/bir_exec_envLib.sml -- to create default environment from a list of bir variables *)
      val var_pairs = List.map dest_BVar all_bvars;
      val var_assigns = List.map (fn (n,t) =>
           (n, ((snd o dest_eq o concl o EVAL) ``SOME (bir_default_value_of_type ^t)``))) var_pairs;

      fun list_mk_update ([], env) = env
	| list_mk_update (h::l, env) = list_mk_update (l, mk_comb (mk_update h, env));

      val bir_env_map_empty = evalthis “(\x. case x of BEnv env => env) bir_env_empty”;
      val env_map = list_mk_update (var_assigns, bir_env_map_empty);
    in
      “BEnv (^env_map)”
    end;


  val init_state_arm8 =
    get_init_state_from_bmr_rec
      bir_lifting_machinesLib_instances.arm8_bmr_rec;

  val init_state_m0_LittleEnd_Main =
    get_init_state_from_bmr_rec
      bir_lifting_machinesLib_instances.m0_bmr_rec_LittleEnd_Main;

  val init_state_m0_BigEnd_Main =
    get_init_state_from_bmr_rec
      bir_lifting_machinesLib_instances.m0_bmr_rec_BigEnd_Main;

  val init_state_m0_LittleEnd_Process =
    get_init_state_from_bmr_rec
      bir_lifting_machinesLib_instances.m0_bmr_rec_LittleEnd_Process;

  val init_state_m0_BigEnd_Process =
    get_init_state_from_bmr_rec
      bir_lifting_machinesLib_instances.m0_bmr_rec_BigEnd_Process;

  val init_state_riscv =
    get_init_state_from_bmr_rec
      bir_lifting_machinesLib_instances.riscv_bmr_rec;


(* some simple assertions *)
  val _ = if identical (init_state_m0_LittleEnd_Main) (init_state_m0_BigEnd_Main) then () else
          raise ERR "assertion m0 \"LE_M == BE_M\"" "the states are expected to be identical terms";

  val _ = if identical (init_state_m0_LittleEnd_Main) (init_state_m0_LittleEnd_Process) then () else
          raise ERR "assertion m0 \"LE_M == LE_P\"" "the states are expected to be identical terms";

  val _ = if identical (init_state_m0_LittleEnd_Main) (init_state_m0_BigEnd_Process) then () else
          raise ERR "assertion m0 \"LE_M == BE_P\"" "the states are expected to be identical terms";

end (* local *)

end (* struct *)
