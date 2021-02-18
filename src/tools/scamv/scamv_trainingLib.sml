structure scamv_trainingLib =
struct

local
  (* error handling *)
  val libname  = "scamv_trainingLib"
  val ERR      = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname

  fun isPrimedRun s = String.isSuffix "_" s;
  fun remove_prime str = bir_utilLib.remove_suffix "_" str;
in
fun compute_training_state current_full_specs current_obs_projection
                           current_word_rel current_path_id path_struct =
    let
      open HolKernel Parse boolSyntax;
      open scamv_path_structLib;
      open bir_rel_synthLib;
      open bir_utilLib;
      open experimentsLib;
	    fun training_input_mining  tries =
		      if tries > 0
		      then
		        let val new_path = case get_distinct_path current_path_id path_struct of
                                   [] => raise ERR "training_branch_predictor"
                                               ("no paths found distinct from path "
                                                ^ PolyML.makestring current_path_id)
                                 | p::_ => p
                val new_spec =  lookup_spec (path_id_of new_path) (path_id_of new_path) current_full_specs;
                val new_spec = case new_spec of
                                   NONE => raise ERR "training_branch_predictor"
                                                 ("no path spec found that exercises path "
                                                  ^ PolyML.makestring (path_id_of new_path))
                                 | SOME s => s
			          val new_word_relation =  make_word_relation (rel_synth_jit new_spec current_obs_projection path_struct) false;
                val _ = print ("Training path: " ^ PolyML.makestring new_path);
				  val training_relation = mk_conj (new_word_relation, current_word_rel);
				  val _ = print ("Calling Z3 to get training state\n")
		        in
			        (Z3_SAT_modelLib.Z3_GET_SAT_MODEL training_relation)
			        handle e => training_input_mining (tries - 1)
		        end
		      else raise ERR "training_branch_predictor" "not enough paths";
    in
	    training_input_mining (num_paths path_struct)
      |> List.partition (isPrimedRun o fst)
      |> (List.map (fn (r,v) => (remove_prime r,v)) o #1)
      |> to_sml_Arbnums
      |> (fn st =>
            if embexp_params_checkmemrange st then st else
            raise ERR "scamv_process_model"
                   ("s_train" ^ " memory contains mapping out of experiment range." ^
                    "is there a problem with the constraints?")
         )

      |> (fn st =>
       let
        val _ = min_verb 1 (fn () =>
          (print "s_train:\n";
           machstate_print st;
           print "\n"));
       in
         st
       end)
    end;

end
    
end
