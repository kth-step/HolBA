(* ------------------------------------------------------------------------- *)
(*  Alternate env representation for cv computation and conversions with it  *)
(* ------------------------------------------------------------------------- *)


structure bir_cv_envLib :> bir_cv_envLib =
struct

open HolKernel Parse boolLib bossLib ;
open bir_cv_basicTheory ;
open bir_cv_basicLib ;
open bir_cv_envTheory bir_envTheory ;
open combinSyntax ;
open optionSyntax ;


(* Converts a chain of update calls to cv_env *)
(* The argument here should already unpacked from BEnv constructor *)
fun update_conv (env_comb : term) : thm = 
  (* TODO : Cleanup the equality check to relate to bir_empty_env *)
  if Term.term_eq env_comb ``\(x:ident). (NONE:bir_val_t option)`` then
    (* We have to rewrite here so the recursive call is easy *)
    REWRITE_RULE [bir_empty_env_def, bir_cv_empty_env_def] from_cv_env_empty
  else 
    let 
      (* Destroy the update call *)
      val ((id, val_opt), aux_env_comb) = dest_update_comb env_comb ;
      (* Converts val_opt to cv_val_opt *)
      val from_val_opt_thm = bir_val_option_conv val_opt ;
      val cv_val_opt = rand (rhs (concl from_val_opt_thm)) ;
      (* Recursively conv *)
      val aux_thm = update_conv aux_env_comb ;
      (* SPEC the cons theorem *)
      val spec_cons_thm = SPECL [id, (dest_some cv_val_opt)] from_cv_env_cons ;
      (* Apply cons theorem *)
      val from_cv_env_thm = MATCH_MP spec_cons_thm aux_thm ;
      (* EVAL the from_cv_val from cons theorem *)
      val evaled_from_cv_val_thm = EVAL (lhs (concl from_cv_env_thm)) ;
    in 
      REWRITE_RULE [evaled_from_cv_val_thm] from_cv_env_thm
    end





fun env_to_cv_env_conv (env : term) : thm =
  update_conv (rand env)


















end
