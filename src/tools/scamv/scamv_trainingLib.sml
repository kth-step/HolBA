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
open HolKernel Parse boolSyntax;
open scamv_path_structLib;
open bir_machstate_importLib;
open experimentsLib;

type training_state = (int * machineState option);
val current_training_states: (training_state list option ref) = ref NONE;

fun get_training_states current_path_id =
    let
      val st_list = List.filter (fn (id,_) => not (id = current_path_id))
				(valOf (!current_training_states))
    in
      case st_list of
	[] => raise ERR "get_training_states" ("no paths found distinct from path "
					       ^ PolyML.makestring current_path_id)
      | sts => sts
      | _ => raise ERR "get_training_states" "error in the training branch predictor"
    end;

fun print_debug x = let val _ = print ("Reached here! \n") in x end;
fun compute_training_state current_full_specs current_obs_projection
                           current_word_rel current_path_id path_struct =
  let
    val _ = if (num_paths path_struct) > 1 then ()
	    else raise ERR "compute_training_state" "not enough paths";
    fun training_input_mining np =
      let
	open bir_rel_synthLib;
	open bir_utilLib;
	        fun training_rel_solving new_path =
		    let
			val _ =  min_verb 5 (fn () =>
						(print ("Training path: " ^ PolyML.makestring new_path)))
			val new_spec =  lookup_spec (path_id_of new_path) (path_id_of new_path) current_full_specs;
			val new_spec = case new_spec of
					   NONE => raise ERR "training_branch_predictor"
                                                 ("no path spec found that exercises path "
                                                  ^ PolyML.makestring (path_id_of new_path))
					 | SOME s => s
			val new_word_relation =  make_word_relation (rel_synth_jit new_spec current_obs_projection path_struct true) false;
			val training_relation = mk_conj (new_word_relation, current_word_rel);
			val _ = min_verb 6 (fn () =>
					       (print (term_to_string training_relation);
						print "\n"));
			val _ = print ("Calling Z3 to get training state\n")
		    in
			SOME (Z3_SAT_modelLib.Z3_GET_SAT_MODEL training_relation)
			handle e => NONE
		    end
      in
	case training_rel_solving np of
	  SOME mt => (mt
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
			       val _ = min_verb 5 (fn () =>
						    (print "s_train:\n";
						     machstate_print st;
						     print "\n"));
			     in
			       (path_id_of np, SOME st)
			     end))
	| NONE => (path_id_of np, NONE)
    end
  in
      case !current_training_states of
	  NONE =>
	  let
	      val _ = current_training_states := SOME (List.map training_input_mining path_struct)
	  in get_training_states current_path_id end
	| SOME st_list => get_training_states current_path_id
  end;

end
    
end
