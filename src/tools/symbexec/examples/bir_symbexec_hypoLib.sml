structure bir_symbexec_hypoLib =
struct

local
(*
  open bir_symbexec_stateLib;
*)
  open bir_block_collectionLib;
  open bir_cfgLib;

  val ERR      = Feedback.mk_HOL_ERR "bir_symbexec_hypoLib"
  val wrap_exn = Feedback.wrap_exn   "bir_symbexec_hypoLib"

(* TODO: when this is done, move it to bir_cfgLib *)
(* TODO: add loop breaking by remembering traces of visited labels! execution time impact? *)
fun cfg_trav_depth travfun state0 n_dict []          = state0
  | cfg_trav_depth travfun state0 n_dict (l::l_todo) =
  let
    fun get_node l_ =
      lookup_block_dict_value n_dict l_
        "cfg_trav_depth"
        ("couldn't find cfg node: " ^ (term_to_string l_));
    val n:cfg_node = get_node l;
    val l_succ = #CFGN_targets n;
    val n_succ = List.map get_node l_succ;
    val (state1, n_new:cfg_node list) = travfun n n_succ state0;
    val l_new = List.map #CFGN_lbl_tm n_new;
  in
    cfg_trav_depth travfun state1 n_dict (l_new@l_todo)
  end;

fun mem_eq eq x [] = false
  | mem_eq eq x (y::ys) =
      eq (x,y) orelse
      mem_eq eq x ys;

fun cfg_trav_depth_to_end travfun state0 n_dict l_entry l_end =
  let val res =
   cfg_trav_depth (fn n => fn n_succ => fn s =>
    let
      val is_end = mem_eq (fn (x,y) => identical x y) (#CFGN_lbl_tm n) l_end;
      val (s', n_newo) = travfun n n_succ is_end s;
      val n_new = if isSome n_newo then
                    valOf n_newo
                  else
                    if is_end then [] else n_succ;
      val _ = if not is_end then () else
              print (".");
    in
      (s', n_new)
    end
  ) state0 n_dict l_entry;
  in
   print ("\n"); res
  end;

in (* outermost local *)

(* (# node travs, # paths, # paths with asserts) *)
fun collect_trav_info bl_dict n_dict l_entry l_end =
  cfg_trav_depth_to_end (fn n => fn n_succ => fn is_end => fn (i1,i2,i3) =>
    let
      val l = #CFGN_lbl_tm n;
      val bl = lookup_block_dict_value bl_dict l
               "collect_trav_info"
               ("couldn't find block: " ^ (term_to_string l));
      open bir_programSyntax;
      open bir_expSyntax;
      val (_, stmts, _) = dest_bir_block bl;
      val s_tms = (fst o listSyntax.dest_list) stmts;
      val (num_stmtsbr, num_assertbr) = List.foldl (fn (t,(i_,ia_)) =>
            if is_BStmt_Assert t then
              (i_,ia_ + i_)
            else (
            if is_BStmt_Assign t then
              if (is_BExp_IfThenElse o snd o dest_BStmt_Assign) t then i_ * 2 else i_
            else
              i_
            , ia_)
          ) (1,0) s_tms;

(*
      val _ = if num_stmtsbr > 1 andalso length n_succ < 2 then
                print_term bl
              else ();
*)

      val n_newo = NONE; (*SOME (if is_end then [] else (flatten (List.tabulate (num_stmtsbr, K n_succ))));*)

      val i1_inc = if is_end then 0 else 1;
      val i2_inc = if is_end then 1 else 0;
      val i3_inc = i2_inc + (if is_end then 0 else num_assertbr);

      val i1' = i1 + i1_inc;
      val i2' = i2 + i2_inc;
      val i3' = i3 + i3_inc;
    in
      ((i1', i2', i3'), n_newo)
    end
  ) (0, 0, 0) n_dict l_entry l_end;

end (* outermost local *)

end (* struct *)
