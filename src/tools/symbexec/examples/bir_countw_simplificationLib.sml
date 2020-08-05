structure bir_countw_simplificationLib =
struct
local

  open bir_constpropLib;
  open bir_symbexecLib;

  open bir_envSyntax;
  open bir_expSyntax;

  open bir_exp_helperLib;

(*
val var = bv_countw_fr;
*)
fun expand_exp vals var =
  let
    val symbv = (valOf o Redblackmap.peek) (vals, var)
                handle Option => raise ERR "expand_exp" ((term_to_string var) ^ " not found");
    val exp = case symbv of
                 SymbValBE (be,_) => be
               | _ => raise ERR "expand_exp" "unhandled symbolic value type";

    val vars = get_birexp_vars exp;

    val valsl = ((Redblackmap.listItems) vals);
    val subexps_raw = List.filter ((fn x => List.exists (fn y => x = y) vars) o fst) valsl;
    (* recursion on varexpressions first *)
    val subexps = List.map (fn (x, _) => (x, expand_exp vals x)) subexps_raw;

    val exp_ = List.foldl (fn ((bv, e), exp_) => subst_exp (bv, e, exp_)) exp subexps;
  in
    exp_
  end;

(*
(hd(SYST_get_env syst))

val syst = List.nth(systs,0)

val env = (SYST_get_env syst);
val pred = (SYST_get_pred syst);

val (p::ps) = pred;
val benvmap = ((snd o dest_comb) ``BEnv (K NONE)``);

simple_pred_to_benvmap pred benvmap
*)

(*
             mk_comb (combinSyntax.mk_update (``2:num``,``"c"``),
                      ``\x. if x = 5:num then "a" else "b"``)
*)

open bir_exp_immSyntax;

val benvmap_empty = ((snd o dest_comb) ``BEnv (K NONE)``);
val bvalo_true = ``SOME (BVal_Imm (Imm1 1w))``;
val bvalo_false = ``SOME (BVal_Imm (Imm1 0w))``;
fun simple_pred_to_benvmap [] benvmap = benvmap
  | simple_pred_to_benvmap (p::ps) benvmap =
      let
        val benvmap_ =
          if not (is_BExp_Den p) then
            if not (is_BExp_UnaryExp p) orelse
               not ((fst o dest_BExp_UnaryExp) p = BIExp_Not_tm) orelse
               not ((is_BExp_Den o snd o dest_BExp_UnaryExp) p)
            then
              let
                val _ = print (term_to_string p);
                val _ = print "\n\n";
              in
                benvmap
              end
            else
              let
                val p_ = (snd o dest_BExp_UnaryExp) p;
                val (vn, _) = (dest_BVar o dest_BExp_Den) p_;
              in
                mk_comb (combinSyntax.mk_update(vn,bvalo_false), benvmap)
              end
          else
          let val (vn, _) = (dest_BVar o dest_BExp_Den) p; in
             mk_comb (combinSyntax.mk_update(vn,bvalo_true), benvmap)
          end
      in
        simple_pred_to_benvmap ps benvmap_
      end;

fun simple_p_to_subst p =
  if is_BExp_UnaryExp p andalso
     (fst o dest_BExp_UnaryExp) p = BIExp_Not_tm then
    subst [((snd o dest_BExp_UnaryExp) p) |-> ``(BExp_Const (Imm1 0w))``]
  else
    subst [p |-> ``(BExp_Const (Imm1 1w))``];

fun simple_pred_to_subst pred exp =
  List.foldl (fn (p, exp) => simple_p_to_subst p exp) exp pred;


in (* local *)

(*
val syst = hd systs;
*)
fun eval_countw_in_syst syst =
  let
    val pred = (SYST_get_pred syst);
    val env  = (SYST_get_env  syst);
    val vals = (SYST_get_vals syst);

    val bv_countw = mk_BVar_string ("countw", ``(BType_Imm Bit64)``);
    val bv_countw_fr = (valOf o Redblackmap.peek) (env, bv_countw)
                       handle Option =>
                       raise ERR "eval_countw_in_syst"
                                 ("couldn't find countw");

(*
    val benv = mk_BEnv (simple_pred_to_benvmap pred benvmap_empty);
*)
    val benv = ``BEnv (K NONE)``;
    val exp_ = expand_exp vals bv_countw_fr;
(*
    val exp = simple_pred_to_subst pred exp_;
*)
    val exp = exp_;
  in
    (snd o dest_eq o concl o EVAL) ``bir_eval_exp ^exp ^benv``
  end;

end (* local *)
end (* struct *)
