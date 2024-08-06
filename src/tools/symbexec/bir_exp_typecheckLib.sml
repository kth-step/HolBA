structure bir_exp_typecheckLib =
struct

local

open HolKernel Parse boolLib bossLib;
open computeLib;

open bir_exp_substitutionsTheory;
open bir_expTheory;

open bir_symbTheory;
open birs_auxTheory;

open birs_auxLib;

  (* error handling *)
  val libname = "bir_exp_typecheckLib"
  val ERR = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname

in (* local *)

(* TODO: we really have to put this in a central place... *)
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
      open bir_interval_expTheory;
      open bir_typing_expTheory;
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
        BExp_ror_exp_type_of,
        bir_immtype_of_size_def
      ]
      val conv = SIMP_CONV (srw_ss()) type_of_bir_exp_thms
    in
      conv term
    end
      handle _ => raise ERR "type_of_bir_exp_CONV" "conversion failed";

 val typecheck_dict = ref ((Redblackmap.mkDict Term.compare) : (term, thm) Redblackmap.dict);
 fun typecheck_add (k_tm, tc_thm) = typecheck_dict := Redblackmap.insert (!typecheck_dict, k_tm, tc_thm);
 fun typecheck_lookup k_tm = 
      SOME (Redblackmap.find (!typecheck_dict, k_tm))
      handle NotFound => NONE;

fun check_typeof thm =
  let
     open optionSyntax;
     open bir_valuesSyntax;
     open bir_typing_expSyntax;
     
     val (term,result) = (dest_eq o concl) thm;
     val k_tm = dest_type_of_bir_exp term;
     val _ = if is_none result orelse
                (is_some result andalso
                 ((fn x => is_BType_Imm x orelse is_BType_Mem x) o dest_some) result) then () else
               raise ERR "check_typeof" "didn't reach the result";
  in (typecheck_add (k_tm, thm); thm) end

fun gettype_CONV term =
  let
     val thm = type_of_bir_exp_CONV term;
  in
    thm
  end
  handle _ => raise ERR "gettype_CONV" ("ill-typed term: " ^ Parse.term_to_string term);

(*
val bexp_term = ``type_of_bir_exp (BExp_BinPred BIExp_LessOrEqual
          (BExp_Den (BVar "countw" (BType_Imm Bit64)))
          (BExp_Const (Imm64 0xFFFFFFFFFFFFFFFEw)))``;
val term = bexp_term;
type_of_bir_exp_DIRECT_CONV bexp_term
*)
 fun type_of_bir_exp_DIRECT_CONV term =
   let
     open bir_typing_expSyntax;

     val _ = if is_type_of_bir_exp term then () else
               raise ERR "type_of_bir_exp_DIRECT_CONV" "cannot handle term";

     val k_tm = dest_type_of_bir_exp term;
     val tc_thm_o = typecheck_lookup k_tm;
   in
    if isSome tc_thm_o then ((*print "successss!!!!\n";*) valOf tc_thm_o) else
    let
     val thm_opened = (REWRITE_CONV [Once bir_typing_expTheory.type_of_bir_exp_def]) term;
     val sub_typeof_exps = GEN_match_extract is_type_of_bir_exp [] [(snd o dest_eq o concl) thm_opened];
     val numberoffoundexps =
       length (List.filter (isSome o typecheck_lookup o dest_type_of_bir_exp) sub_typeof_exps);
     (*val _ = print ("found typeofs: " ^ (Int.toString numberoffoundexps) ^ "\n");*)
     
     val typeof_thms = List.map type_of_bir_exp_DIRECT_CONV sub_typeof_exps;

     val thm = CONV_RULE (RAND_CONV (REWRITE_CONV typeof_thms THENC gettype_CONV)) thm_opened;
    in
      check_typeof thm
    end
   end
  handle _ => raise ERR "type_of_bir_exp_DIRECT_CONV" ("ill-typed term: " ^ Parse.term_to_string term);

val type_of_bir_exp_DIRECT_CONV = Profile.profile "type_of_bir_exp_DIRECT_CONV" type_of_bir_exp_DIRECT_CONV;


end (* local *)

end (* struct *)
