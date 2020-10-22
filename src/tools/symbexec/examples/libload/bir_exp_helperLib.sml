structure bir_exp_helperLib =
struct
local

  open pred_setTheory;

  val conv_to_varset = SIMP_CONV (std_ss++HolBACoreSimps.holBACore_ss)
                                 ([INSERT_UNION_EQ,UNION_EMPTY]@HolBASimps.common_exp_defs);

  val ERR      = Feedback.mk_HOL_ERR "bir_exp_helperLib"
  val wrap_exn = Feedback.wrap_exn   "bir_exp_helperLib"
in

(*
val exp = ``
BExp_UnaryExp BIExp_Not
          (BExp_BinExp BIExp_Or
             (BExp_UnaryExp BIExp_Not
                (BExp_BinPred BIExp_Equal
                   (BExp_Den (BVar "PSR_N" BType_Bool))
                   (BExp_Den (BVar "PSR_V" BType_Bool))))
             (BExp_Den (BVar "PSR_Z" BType_Bool)))
``
*)

fun simpleholset_to_list t =
  if pred_setSyntax.is_empty t then [] else
  if not (pred_setSyntax.is_insert t) then
    raise ERR "simpleholset_to_list" ("cannot handle syntax: " ^ (term_to_string t))
  else
    let val (x, rset) = pred_setSyntax.dest_insert t in
      x::(simpleholset_to_list rset)
    end;

fun get_birexp_vars exp =
  let
    val exp_vars = (snd o dest_eq o concl o conv_to_varset) ``(bir_vars_of_exp ^exp)``;
    val vars = (simpleholset_to_list) exp_vars;
  in
    vars
  end;

local
  (* helper, TODO: needs to be moved more centrally
     (taken from bir_exp_to_wordsLib.type_of_bir_exp_CONV) *)
  (* could probably be improved by properly building simplification set *)
  (* also, does it really need srw_ss if there are just BIR expression constructors around? *)
  fun type_of_bir_exp_CONV term =
    (* Manual test
    val term = ``
      BExp_BinExp BIExp_Plus
        (BExp_Const (Imm32 20w))
        (BExp_Const (Imm32 22w))
    ``;
    val thm = type_of_bir_exp_CONV ``type_of_bir_exp ^term``;
    *)
    let
      open bir_immTheory
      open bir_valuesTheory
      open bir_envTheory
      open bir_exp_memTheory
      open bir_bool_expTheory
      open bir_extra_expsTheory
      open bir_nzcv_expTheory
      val type_of_bir_exp_thms = [
        type_of_bir_exp_def,
        bir_var_type_def,
        bir_type_is_Imm_def,
        type_of_bir_imm_def,
        BExp_Aligned_type_of,
        BExp_unchanged_mem_interval_distinct_type_of,
        bir_number_of_mem_splits_REWRS,
        BType_Bool_def,
        bir_exp_true_def,
        bir_exp_false_def,
        BExp_MSB_type_of,
        BExp_nzcv_ADD_DEFS,
        BExp_nzcv_SUB_DEFS,
        n2bs_def,
        BExp_word_bit_def,
        BExp_Align_type_of,
        BExp_ror_type_of,
        BExp_LSB_type_of,
        BExp_word_bit_exp_type_of,
        BExp_ADD_WITH_CARRY_type_of,
        BExp_word_reverse_type_of,
        BExp_ror_exp_type_of
      ]
      val conv = SIMP_CONV (srw_ss()) type_of_bir_exp_thms
    in
      conv term
    end
      handle e => raise wrap_exn "type_of_bir_exp_CONV" e;
in
  fun get_type_of_bir_exp exp =
    (snd o dest_eq o concl o type_of_bir_exp_CONV) (bir_typing_expSyntax.mk_type_of_bir_exp exp);
end

end (* local *)

end (* struct *)
