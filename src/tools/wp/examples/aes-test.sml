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
        val (_, (def_thm, _)) = hd (DB.find ("bir_wp_comp_wps_iter_step2_wp_" ^ lbl_str));
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
        val (_, (def_thm, _)) = hd (DB.find ("bir_wp_comp_wps_iter_step2_wp_" ^ lbl_str));
        val thm = REWRITE_RULE [thm_in] def_thm;
        val thm_evald = (EVAL o snd o dest_eq o concl) thm;
        val thm_new = (TRANS thm thm_evald);
        val _ = print ("remaining: " ^ (Int.toString (List.length lbls)) ^ "  \r");
      in
        thm_new::(eval_through lbls thm_new)
      end;


val lbl_list_todo = List.take ((tl (List.rev lbl_list)), 90);


val timer_start = Lib.start_time ();
val _ = print "\r\n===========\r\n";
val out_thms = eval_through lbl_list_todo aes_post_def;
val out_thm = List.last out_thms;
val _ = print "\r\n===========\r\n";
val _ = Lib.end_time timer_start;

val wp_ = (snd o dest_eq o concl) out_thm;
(* ---------------------------------------------------------------------------------------- *)

val prop = (snd o dest_eq o concl) aes_wp_taut_thm;
val wp = List.nth((snd o strip_comb o snd o dest_comb) prop, 1);

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
val probnum = List.length problist;

val n_nodes = count_nodes wp_;



val _ = bir_exp_pretty_print wp_;



