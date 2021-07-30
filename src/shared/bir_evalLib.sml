structure bir_evalLib :> bir_evalLib =
struct

open HolKernel Parse boolLib bossLib bir_programSyntax pairSyntax optionSyntax;

fun cons_obs_tm ob_o (obs,st) =
    if is_none ob_o
    then (obs,st)
    else (dest_some ob_o :: obs, st)

fun bir_eval_exec prog st =
    let val (_,_,status) = dest_bir_state st;
    in
      if not (is_BST_Running status)
      then ([], st)
      else
        let val (ob_tm, st') = (dest_pair o rhs o concl) (EVAL “bir_exec_step ^prog ^st”)
        in
          cons_obs_tm ob_tm (bir_eval_exec prog st')
        end
    end;

end
