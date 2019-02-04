
open bir_envSyntax;

open bir_envTheory;
open finite_mapTheory;


structure bir_exec_envLib =
struct

(*
  val env = ``BEnv (FEMPTY |+ ("bit1", (BType_Bool,      SOME (BVal_Imm (Imm1  0w))))
                           |+ ("R1",   (BType_Imm Bit32, SOME (BVal_Imm (Imm32 3w))))
                           |+ ("R2",   (BType_Imm Bit32, SOME (BVal_Imm (Imm32 4w))))
                           |+ ("R3",   (BType_Imm Bit32, SOME (BVal_Imm (Imm32 5w))))
                   )``;

  val var = ``(BVar "R1" (BType_Imm Bit32))``;
  val b_val = ``(BVal_Imm (Imm32 9w))``;

  val t = ``bir_env_write ^var ^b_val ^env``;

  val var_eq_thm =
    let
      val vars = [``"bit1"``, ``"R1"``, ``"R2"``, ``"R3"``];
    in
      LIST_CONJ (List.map ((SIMP_RULE pure_ss [boolTheory.EQ_CLAUSES]) o EVAL) (List.foldl (fn (v,l) => (List.map (fn v2 => mk_eq(v,v2)) vars)@l) [] vars))
    end;
*)
(*
++stringSimps.STRING_ss
*)

  fun bir_exec_env_write_conv var_eq_thm t =
    if not (is_bir_env_write t) then
      raise UNCHANGED
    else
      let
        val thm1 = SIMP_CONV (list_ss++HolBACoreSimps.holBACore_ss) [
                FLOOKUP_EMPTY,
                FLOOKUP_UPDATE,
                bir_env_update_def,
                bir_env_lookup_def,
                bir_env_lookup_type_def,
                bir_env_check_type_def,
                bir_env_write_def,
                var_eq_thm] t;

(*
        val thm2 = REFL ((snd o dest_eq o concl) thm1);
        val thm3 = REFL ((snd o dest_eq o concl) thm2);
*)
        val thm2 = REWRITE_CONV [Once finite_mapTheory.FUPDATE_PURGE] ((snd o dest_eq o concl) thm1);

        val thm3 = SIMP_CONV (std_ss) [
                DOMSUB_FEMPTY, DOMSUB_FUPDATE, DOMSUB_FUPDATE_NEQ,
                var_eq_thm] ((snd o dest_eq o concl) thm2);

      in
        TRANS (TRANS thm1 thm2) thm3
      end;




end
