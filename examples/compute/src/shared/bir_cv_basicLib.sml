structure bir_cv_basicLib :> bir_cv_basicLib =
struct

open HolKernel Parse boolLib bossLib ;
open finite_mapSyntax ;
open bir_basicSyntax bir_cv_basicSyntax ;
open bir_cv_basicTheory ;
open optionSyntax ;


fun assert_correct tm thm = assert (fn (x,y) => (Term.compare (x, y)) = EQUAL) (tm, lhs (concl thm))


val ERR = mk_HOL_ERR "bir_cv_basicLib" ;

(* TODO : Handle FUPDATE_LIST (|++) as well *)
(* Given a term representing an fmap made from successive FUPDATE, 
*  outputs a theorem of the form : fmap_tm = alist_to_fmap l *)
fun fmap_to_alist_conv (fmap_tm : term) : thm =
    if is_fempty fmap_tm then GSYM (EVAL ``alist_to_fmap ([]:(num # num) list)``)
    else let 
      (* Destroy the outer fupdate *)
      val (rest_fmap_tm, pair_tm) = dest_fupdate fmap_tm ;
      (* Recursive call : rest_fmap_tm = alist_to_fmap l *)
      val aux_fmap_thm = fmap_to_alist_conv rest_fmap_tm ;
      (* Gets the list from the recursive call *)
      val aux_list_tm = rand (rhs (concl aux_fmap_thm)) ;
      (* Creates the new list *)
      val new_list_tm = listSyntax.mk_cons (pair_tm, aux_list_tm) ;
      (* Use alist_to_fmap_thm to get a theorem from the recursive call *)
      val rw_thm = GSYM $ REWRITE_CONV [Once alistTheory.alist_to_fmap_thm, GSYM aux_fmap_thm] ``alist_to_fmap ^new_list_tm`` ;
      val _ = assert_correct fmap_tm rw_thm ;
  in rw_thm end

(* Given a BVal_Mem, outputs a theorem of the form :
*  bir_val_mem = from_cv_val v *)
fun bir_val_mem_conv (bir_val_mem_tm : term) : thm =
  let 
    (* Get the underlying fmap of the value *)
    val (addr_ty_tm, val_ty_tm, fmap_tm) = dest_val_mem bir_val_mem_tm ;
    (* Convert it to fmap *)
    val fmap_thm = fmap_to_alist_conv fmap_tm ;
    val alist_tm = rand (rhs (concl fmap_thm)) ;
    (* Create the BCVVal_Mem term *)
    val cv_val_mem_tm = ``BCVVal_Mem ^addr_ty_tm ^val_ty_tm ^alist_tm`` ;
    val rw_thm = GSYM $ REWRITE_CONV [GSYM fmap_thm, from_cv_val_def] ``from_cv_val ^cv_val_mem_tm`` ;
    val _ = assert_correct bir_val_mem_tm rw_thm ;
  in rw_thm end


(* Given a BVal_Imm, outputs a theorem of the form :
*  bir_val_imm = from_cv_val v *)
fun bir_val_imm_conv (bir_val_imm_tm : term) : thm =
  let 
    (* Get the underlying fmap of the value *)
    val imm_tm = dest_val_imm bir_val_imm_tm ;
    (* Create the BCVVal_Mem term *)
    val cv_val_mem_tm = ``BCVVal_Imm ^imm_tm`` ;
    val rw_thm = GSYM $ REWRITE_CONV [from_cv_val_def] ``from_cv_val ^cv_val_mem_tm`` ;
    val _ = assert_correct bir_val_imm_tm rw_thm ;
  in rw_thm end


(* Convert any BVal_xxx to a theorem : bir_val = from_cv_val *)
fun bir_val_conv (bir_val_tm : term) : thm = 
  if is_val_mem bir_val_tm then
    bir_val_mem_conv bir_val_tm
  else 
    bir_val_imm_conv bir_val_tm

fun bir_val_option_conv (bir_val_option_tm : term) : thm = 
  if is_none bir_val_option_tm then
    GSYM (REWRITE_CONV [from_cv_val_def, from_cv_val_option_def] ``from_cv_val_option NONE``)
  else let 
    val bir_val_tm = dest_some bir_val_option_tm ;
    val bir_val_thm = bir_val_conv bir_val_tm ;
    val cv_val_tm = rand (rhs (concl bir_val_thm)) ;
    val rw_thm = GSYM $REWRITE_CONV [Once from_cv_val_def, Once from_cv_val_option_def, GSYM bir_val_thm] 
      ``from_cv_val_option (SOME ^cv_val_tm)`` ;
    val _ = assert_correct bir_val_option_tm rw_thm ;
    in rw_thm end

(* Convert any BExp_xxx to a theorem : bir_exp = from_cv_exp *)
fun bir_exp_conv (bir_exp_tm : term) : thm = 
  if is_exp_const bir_exp_tm then
    GSYM $ REWRITE_CONV [from_cv_exp_def] ``from_cv_exp ^(mk_cv_exp_const (dest_exp_const bir_exp_tm))``
  else if is_exp_mem_const bir_exp_tm then
    let 
      val (t1,t2,fmap_tm) = (dest_exp_mem_const bir_exp_tm) ;
      val alist_thm = fmap_to_alist_conv fmap_tm ;
      val alist_tm = rand (rhs (concl alist_thm)) ;
      val rw_thm = GSYM $ REWRITE_CONV [from_cv_exp_def, GSYM alist_thm] ``from_cv_exp ^(mk_cv_exp_mem_const (t1,t2,alist_tm))``
      val _ = assert_correct bir_exp_tm rw_thm ;
    in
      rw_thm
    end
  else if is_exp_den bir_exp_tm then
    GSYM $ REWRITE_CONV [from_cv_exp_def] ``from_cv_exp ^(mk_cv_exp_den (dest_exp_den bir_exp_tm))``
  else if is_exp_bin_exp bir_exp_tm then
    let
      val (t1,t2,t3) = dest_exp_bin_exp bir_exp_tm ;
      val t2_thm = bir_exp_conv t2 ;
      val t2_tm = rand (rhs (concl t2_thm)) ;
      val t3_thm = bir_exp_conv t3 ;
      val t3_tm = rand (rhs (concl t3_thm)) ;
      val rw_thm = GSYM $ REWRITE_CONV [from_cv_exp_def, GSYM t2_thm, GSYM t3_thm] ``from_cv_exp ^(mk_cv_exp_bin_exp (t1,t2_tm,t3_tm))``
      val _ = assert_correct bir_exp_tm rw_thm ;
    in
      rw_thm
    end
  else if is_exp_unary_exp bir_exp_tm then
    let
      val (t1,t2) = dest_exp_unary_exp bir_exp_tm ;
      val t2_thm = bir_exp_conv t2 ;
      val t2_tm = rand (rhs (concl t2_thm)) ;
      val rw_thm = GSYM $ REWRITE_CONV [from_cv_exp_def, GSYM t2_thm] ``from_cv_exp ^(mk_cv_exp_unary_exp (t1,t2_tm))``
      val _ = assert_correct bir_exp_tm rw_thm ;
    in
      rw_thm
    end
  else if is_exp_bin_pred bir_exp_tm then
    let
      val (t1,t2,t3) = dest_exp_bin_pred bir_exp_tm ;
      val t2_thm = bir_exp_conv t2 ;
      val t2_tm = rand (rhs (concl t2_thm)) ;
      val t3_thm = bir_exp_conv t3 ;
      val t3_tm = rand (rhs (concl t3_thm)) ;
      val rw_thm = GSYM $ REWRITE_CONV [from_cv_exp_def, GSYM t2_thm, GSYM t3_thm] ``from_cv_exp ^(mk_cv_exp_bin_pred (t1,t2_tm,t3_tm))``
      val _ = assert_correct bir_exp_tm rw_thm ;
    in
      rw_thm
    end
  else if is_exp_if_then_else bir_exp_tm then
    let
      val (t1,t2,t3) = dest_exp_if_then_else bir_exp_tm ;
      val t1_thm = bir_exp_conv t1 ;
      val t1_tm = rand (rhs (concl t1_thm)) ;
      val t2_thm = bir_exp_conv t2 ;
      val t2_tm = rand (rhs (concl t2_thm)) ;
      val t3_thm = bir_exp_conv t3 ;
      val t3_tm = rand (rhs (concl t3_thm)) ;
      val rw_thm = GSYM $ REWRITE_CONV [from_cv_exp_def, GSYM t1_thm, GSYM t2_thm, GSYM t3_thm] ``from_cv_exp ^(mk_cv_exp_if_then_else (t1_tm,t2_tm,t3_tm))``
      val _ = assert_correct bir_exp_tm rw_thm ;
    in
      rw_thm
    end
  else if is_exp_load bir_exp_tm then
    let
      val (t1,t2,t3,t4) = dest_exp_load bir_exp_tm ;
      val t1_thm = bir_exp_conv t1 ;
      val t1_tm = rand (rhs (concl t1_thm)) ;
      val t2_thm = bir_exp_conv t2 ;
      val t2_tm = rand (rhs (concl t2_thm)) ;
      val rw_thm = GSYM $ REWRITE_CONV [from_cv_exp_def, GSYM t1_thm, GSYM t2_thm] ``from_cv_exp ^(mk_cv_exp_load (t1_tm,t2_tm,t3,t4))``
      val _ = assert_correct bir_exp_tm rw_thm ;
    in
      rw_thm
    end
  else if is_exp_store bir_exp_tm then
    let
      val (t1,t2,t3,t4) = dest_exp_store bir_exp_tm ;
      val t1_thm = bir_exp_conv t1 ;
      val t1_tm = rand (rhs (concl t1_thm)) ;
      val t2_thm = bir_exp_conv t2 ;
      val t2_tm = rand (rhs (concl t2_thm)) ;
      val t4_thm = bir_exp_conv t4 ;
      val t4_tm = rand (rhs (concl t4_thm)) ;
      val rw_thm = GSYM $ REWRITE_CONV [from_cv_exp_def, GSYM t1_thm, GSYM t2_thm, GSYM t4_thm] ``from_cv_exp ^(mk_cv_exp_store (t1_tm,t2_tm,t3,t4_tm))``
      val _ = assert_correct bir_exp_tm rw_thm ;
    in
      rw_thm
    end
  else raise ERR "bir_exp_conv" "not BExp"




end
