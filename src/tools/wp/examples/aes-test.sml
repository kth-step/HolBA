open HolKernel Parse;

open bir_wpTheory bir_wpLib;

open listSyntax;

open aesBinaryTheory;
open bir_expLib;

open bir_wp_simpLib;
open bir_wp_expLib;

open aesSimpWpTheory;


val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = set_trace "bir_inst_lifting.DEBUG_LEVEL" 1;



val prop = (snd o dest_eq o concl) aes_wp_taut_thm;
val wp = List.nth((snd o strip_comb o snd o dest_comb) prop, 1);

val wp_ = (snd o dest_eq o concl o (REWRITE_CONV [bir_exp_and_def, bir_exp_imp_def, bir_exp_or_def, bir_exp_not_def])) wp;


  fun bir_exp_nonstandards exp =
    let
      val ef = bir_exp_nonstandards;
    in
      if is_BExp_Const exp then []
      else if is_BExp_Den exp then []
      else if is_BExp_Cast exp then
        let
          val (castt, exp, sz) = (dest_BExp_Cast) exp;
          val casttstr = castt_to_string castt;
          val szstr = (Int.toString o size_of_bir_immtype_t) sz;
        in
          ef exp
        end

      else if is_BExp_UnaryExp exp then
        let
          val (uop, exp) = (dest_BExp_UnaryExp) exp;
          val uopstr = uop_to_string uop;
        in
          ef exp
        end

      else if is_BExp_BinExp exp then
        let
          val (bop, exp1, exp2) = (dest_BExp_BinExp) exp;
          val bopstr = bop_to_string bop;
        in
          (ef exp1)@(ef exp2)
        end

      else if is_BExp_BinPred exp then
        let
          val (bpredop, exp1, exp2) = (dest_BExp_BinPred) exp;
          val bpredopstr = bpredop_to_string bpredop;
        in
          (ef exp1)@(ef exp2)
        end

      else if is_BExp_MemEq exp then
        let
          val (exp1, exp2) = (dest_BExp_MemEq) exp;
        in
          (ef exp1)@(ef exp2)
        end

      else if is_BExp_IfThenElse exp then
        let
          val (expc, expt, expf) = (dest_BExp_IfThenElse) exp;
        in
          (ef expc)@(ef expt)@(ef expf)
        end

      else if is_BExp_Load exp then
        let
          val (expm, expad, endi, sz) = (dest_BExp_Load) exp;
          val endistr = endi_to_string endi;
          val szstr = (Int.toString o size_of_bir_immtype_t) sz;
        in
          (ef expm)@(ef expad)
        end

      else if is_BExp_Store exp then
        let
          val (expm, expad, endi, expv) = (dest_BExp_Store) exp;
          val endistr = endi_to_string endi;
        in
          (ef expm)@(ef expad)@(ef expv)
        end

      else
        [exp]

    end;


fun count_nodes term =
  if is_comb term then
    let
      val (left, right) = dest_comb term;
    in
      (count_nodes left) + (count_nodes right)
    end
  else
    1;



val problist = bir_exp_nonstandards wp_;

val n_nodes = count_nodes wp_;



val _ = bir_exp_pretty_print wp_;



