structure bir_cv_basicLib :> bir_cv_basicLib =
struct

open HolKernel Parse boolLib bossLib ;
open finite_mapSyntax ;
open bir_basicSyntax ;
open bir_cv_basicTheory ;
open optionSyntax ;


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
      val rw_thm = REWRITE_CONV [Once alistTheory.alist_to_fmap_thm, GSYM aux_fmap_thm] ``alist_to_fmap ^new_list_tm`` ;
  in GSYM rw_thm end

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
    val rw_thm = REWRITE_CONV [GSYM fmap_thm, from_cv_val_def] ``from_cv_val ^cv_val_mem_tm`` ;
  in GSYM rw_thm end


(* Given a BVal_Imm, outputs a theorem of the form :
*  bir_val_imm = from_cv_val v *)
fun bir_val_imm_conv (bir_val_imm_tm : term) : thm =
  let 
    (* Get the underlying fmap of the value *)
    val imm_tm = dest_val_imm bir_val_imm_tm ;
    (* Create the BCVVal_Mem term *)
    val cv_val_mem_tm = ``BCVVal_Imm ^imm_tm`` ;
    val rw_thm = REWRITE_CONV [from_cv_val_def] ``from_cv_val ^cv_val_mem_tm`` ;
  in GSYM rw_thm end


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
    val rw_thm = REWRITE_CONV [Once from_cv_val_def, Once from_cv_val_option_def, GSYM bir_val_thm] 
      ``from_cv_val_option (SOME ^cv_val_tm)`` ;
    in GSYM rw_thm end
    


end
