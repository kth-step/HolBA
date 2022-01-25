signature bir_machstate_importLib =
sig
  include Abbrev;
  val merge_machstate_into_bir_state : term -> experimentsLib.machineState -> term;
  val merge_json_into_bir_state : term -> Json.json -> term;

  (* first argument is the program (to initialise PC, etc.) *)
  val scamv_machstate_to_bir_state : term -> experimentsLib.machineState -> term;
  val scamv_json_to_bir_state : term -> Json.json -> term;
end
