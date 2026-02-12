open HolKernel Parse;

open bir_wpTheory bir_wpLib;

open listSyntax;

open aesBinaryTheory;
open bir_expLib;

open bir_wp_simpLib;
open bir_wp_expLib;

open aesSimpWpTheory;
open aesWpsTheory;


(*
val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = set_trace "bir_inst_lifting.DEBUG_LEVEL" 1;
*)





(* ---------------------------------------------------------------------------------------- *)




(* quick fix, has to be revisited *)
(*val lbl_list = List.map (term_to_string o snd o gen_dest_Imm o dest_BL_Address) (bir_wp_fmap_to_dom_list wps1);*)
val lbl_list = (gen_lbl_list o snd o dest_eq o concl) aes_wps1_def;

val wp_def_list = aes_post_def::(List.map
      (fn lbl_str =>
      let
        val (_, (def_thm, _)) = hd (DB.find (bir_wpLib.wps_id_prefix ^ lbl_str));
      in def_thm end
      ) (tl (List.rev lbl_list)));

(*
val wp_list = List.map (snd o dest_eq o concl) wp_def_list;

fun print_wp_list _ [] = ()
  | print_wp_list doPretty (wp::wp_l) =
      let
        val _ = print "\r\n\r\n";
        val _ = if doPretty then
                  bir_exp_pretty_print wp
                else
                  print (term_to_string wp)
                ;
      in
        print_wp_list doPretty wp_l
      end;

val _ = print_wp_list false wp_list;
*)

val _ = print "\r\n";
val _ = print "===========\r\n";
val _ = print "weakest precondition evaluation:\r\n";
(*
val (lbl_last, wp_last) = (dest_pair o snd o dest_fupdate) wps1;
*)


fun eval_through [] thm = [thm]
  | eval_through (lbl_str::lbls) thm_in =
      let
        val (_, (def_thm, _)) = hd (DB.find (bir_wpLib.wps_id_prefix ^ lbl_str));
        val thm = REWRITE_RULE [thm_in] def_thm;
        val thm_evald = (EVAL o snd o dest_eq o concl) thm;
        val thm_new = (TRANS thm thm_evald);
        val _ = print ("remaining: " ^ (Int.toString (List.length lbls)) ^ "  \r");
      in
        thm_new::(eval_through lbls thm_new)
      end;


val lbl_list_todo = List.take ((tl (List.rev lbl_list)), 70);

val wp_w_subst1 =
  let
    val lbl_str = List.last lbl_list_todo;
    val (_, (def_thm, _)) = hd (DB.find (bir_wpLib.wps_id_prefix ^ lbl_str));
  in
    (snd o dest_eq o concl) (computeLib.RESTR_EVAL_CONV [``bir_exp_subst1``] ((fst o dest_eq o concl) def_thm))
  end;


val timer_start = Lib.start_time ();
val _ = print "\r\n===========\r\n";
val out_thms = eval_through lbl_list_todo aes_post_def;
val out_thm = List.last out_thms;
val _ = print "\r\n===========\r\n";
val _ = Lib.end_time timer_start;

val wp_ = (snd o dest_eq o concl) out_thm;
(* ---------------------------------------------------------------------------------------- *)

(*
val prop = (snd o dest_eq o concl) aes_wp_taut_thm;
val wp = (snd o dest_comb o snd o dest_comb) prop;
*)

val wp = (snd o dest_eq o concl) wp_simp_def;
val wp_ = (snd o dest_eq o concl o (REWRITE_CONV [bir_exp_and_def, bir_exp_imp_def, bir_exp_or_def, bir_exp_not_def])) wp;

(* ---------------------------------------------------------------------------------------- *)





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



  fun syntax_fns n d m = HolKernel.syntax_fns {n = n, dest = d, make = m} "bir_exp_substitutions"
  val syntax_fns3 = syntax_fns 3 HolKernel.dest_triop HolKernel.mk_triop;
  val (bir_exp_subst1_tm, mk_bir_exp_subst1, dest_bir_exp_subst1, is_bir_exp_subst1) = syntax_fns3 "bir_exp_subst1";


  fun bir_exp_nonstandards_wsubst1 exp =
    let
      val ef = bir_exp_nonstandards_wsubst1;
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

      else if is_bir_exp_subst1 exp then
        let
          val (v, ve, e) = (dest_bir_exp_subst1) exp;
        in
          (ef ve)@(ef e)
        end

      else
        [exp]
    end;


  fun bir_exp_count_bir_nodes exp =
    let
      val ef = bir_exp_count_bir_nodes;
    in
      if is_BExp_Const exp then 1
      else if is_BExp_Den exp then 1
      else if is_BExp_Cast exp then
        let
          val (castt, exp, sz) = (dest_BExp_Cast) exp;
          val casttstr = castt_to_string castt;
          val szstr = (Int.toString o size_of_bir_immtype_t) sz;
        in
          1+(ef exp)
        end

      else if is_BExp_UnaryExp exp then
        let
          val (uop, exp) = (dest_BExp_UnaryExp) exp;
          val uopstr = uop_to_string uop;
        in
          1+(ef exp)
        end

      else if is_BExp_BinExp exp then
        let
          val (bop, exp1, exp2) = (dest_BExp_BinExp) exp;
          val bopstr = bop_to_string bop;
        in
          1+(ef exp1)+(ef exp2)
        end

      else if is_BExp_BinPred exp then
        let
          val (bpredop, exp1, exp2) = (dest_BExp_BinPred) exp;
          val bpredopstr = bpredop_to_string bpredop;
        in
          1+(ef exp1)+(ef exp2)
        end

      else if is_BExp_MemEq exp then
        let
          val (exp1, exp2) = (dest_BExp_MemEq) exp;
        in
          1+(ef exp1)+(ef exp2)
        end

      else if is_BExp_IfThenElse exp then
        let
          val (expc, expt, expf) = (dest_BExp_IfThenElse) exp;
        in
          1+(ef expc)+(ef expt)+(ef expf)
        end

      else if is_BExp_Load exp then
        let
          val (expm, expad, endi, sz) = (dest_BExp_Load) exp;
          val endistr = endi_to_string endi;
          val szstr = (Int.toString o size_of_bir_immtype_t) sz;
        in
          1+(ef expm)+(ef expad)
        end

      else if is_BExp_Store exp then
        let
          val (expm, expad, endi, expv) = (dest_BExp_Store) exp;
          val endistr = endi_to_string endi;
        in
          1+(ef expm)+(ef expad)+(ef expv)
        end

      else if is_bir_exp_subst1 exp then
        let
          val (v, ve, e) = (dest_bir_exp_subst1) exp;
        in
          1+(ef ve)+(ef e)
        end

      else
        raise (ERR "bir_exp_count_bir_nodes" "not an allowed structure")
    end;


  fun bir_exp_count_subst1 exp =
    let
      val ef = bir_exp_count_subst1;
    in
      if is_BExp_Const exp then 0
      else if is_BExp_Den exp then 0
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
          (ef exp1)+(ef exp2)
        end

      else if is_BExp_BinPred exp then
        let
          val (bpredop, exp1, exp2) = (dest_BExp_BinPred) exp;
          val bpredopstr = bpredop_to_string bpredop;
        in
          (ef exp1)+(ef exp2)
        end

      else if is_BExp_MemEq exp then
        let
          val (exp1, exp2) = (dest_BExp_MemEq) exp;
        in
          (ef exp1)+(ef exp2)
        end

      else if is_BExp_IfThenElse exp then
        let
          val (expc, expt, expf) = (dest_BExp_IfThenElse) exp;
        in
          (ef expc)+(ef expt)+(ef expf)
        end

      else if is_BExp_Load exp then
        let
          val (expm, expad, endi, sz) = (dest_BExp_Load) exp;
          val endistr = endi_to_string endi;
          val szstr = (Int.toString o size_of_bir_immtype_t) sz;
        in
          (ef expm)+(ef expad)
        end

      else if is_BExp_Store exp then
        let
          val (expm, expad, endi, expv) = (dest_BExp_Store) exp;
          val endistr = endi_to_string endi;
        in
          (ef expm)+(ef expad)+(ef expv)
        end

      else if is_bir_exp_subst1 exp then
        let
          val (v, ve, e) = (dest_bir_exp_subst1) exp;
        in
          1+(ef ve)+(ef e)
        end

      else
        raise (ERR "bir_exp_count_subst1" "not an allowed structure")
    end;


fun count_leaves term =
  if wordsSyntax.is_n2w term then
    1
  else if stringSyntax.is_string term then
    1
  else if is_comb term then
    let
      val (left, right) = dest_comb term;
    in
      (count_leaves left) + (count_leaves right)
    end
  else
    1;




val problist_pre = bir_exp_nonstandards_wsubst1 wp_w_subst1;
val n_prob_pre = List.length problist_pre;
val n_nodes_pre = bir_exp_count_bir_nodes wp_w_subst1;
val n_substs_pre = bir_exp_count_subst1 wp_w_subst1;
(*
((fst o dest_comb) wp_w_subst1)
((fst o dest_comb o snd o dest_comb) wp_w_subst1)
((fst o dest_comb o snd o dest_comb o snd o dest_comb o snd o dest_comb) wp_w_subst1)
((fst o dest_comb) wp_)
((fst o dest_comb o snd o dest_comb) wp_)

val n_leaves_pre = count_leaves wp_w_subst1;
val str_wp_pre = bir_expLib.bir_exp_to_string wp_w_subst1;
val sz_str_wp_pre = String.size str_wp_pre;
*)

val problist = bir_exp_nonstandards wp_;
val n_prob = List.length problist;
val n_nodes = bir_exp_count_bir_nodes wp_;
val n_substs_pre = bir_exp_count_subst1 wp_;
(*
val n_leaves = count_leaves wp_;
val str_wp = bir_expLib.bir_exp_to_string wp_;
val sz_str_wp = String.size str_wp;
*)







val _ = bir_exp_pretty_print wp_;



