(* ------------------------------------------------------------------------- *)
(*  Alternate env representation for cv computation and conversions with it  *)
(* ------------------------------------------------------------------------- *)


structure bir_cv_envLib :> bir_cv_envLib =
struct

open HolKernel Parse boolLib bossLib ;
open bir_cv_envTheory bir_envTheory ;
open combinSyntax ;
open optionSyntax ;

val test_env = rhs (concl (EVAL 
``bir_env_update 
    (bir_env_update bir_empty_env (BVar "r1") (BVal_Imm (Imm8 1w))) 
  (BVar "r2") (BVal_Imm (Imm8 2w))``)) ;

(* Converts a chain of update calls to cv_env *)
(* The argument here should already unpacked from BEnv constructor *)
fun update_conv (env_comb : term) : thm = 
  (* TODO : Cleanup the equality check to relate to bir_empty_env *)
  if Term.term_eq env_comb ``\(x:ident). (NONE:bir_val_t option)`` then
    (* We have to rewrite here so the recursive call is easy *)
    REWRITE_RULE [bir_empty_env_def, bir_cv_empty_env_def] to_env_empty
  else 
    let 
      (* Destroy the update call *)
      val ((id, val_opt), aux_env_comb) = dest_update_comb env_comb ;
      (* Recursively conv *)
      val aux_thm = update_conv aux_env_comb ;
      (* SPEC the cons theorem *)
      val spec_cons_thm = SPECL [id, (dest_some val_opt)] to_env_cons ;
    in 
      MATCH_MP spec_cons_thm aux_thm
    end





fun env_to_cv_env_conv (env : term) : thm =
  update_conv (rand env)


















end
