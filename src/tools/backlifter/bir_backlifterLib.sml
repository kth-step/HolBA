structure bir_backlifterLib :> bir_backlifterLib =
struct

open Abbrev;

(* For debugging add_reg example:
  val bir_ct = bir_add_reg_ct;
  val prog_bin = ``bir_add_reg_progbin``;
  val arm8_pre = ``arm8_add_reg_pre``;
  val arm8_post = ``arm8_add_reg_post``;
  val bir_prog_def = bir_add_reg_prog_def;
  val bir_pre_defs = [bir_add_reg_contract_1_pre_def, bir_add_reg_pre_def];
  val bir_pre1_def = bir_add_reg_contract_1_pre_def;
  val arm8_pre_imp_bir_pre_thm = arm8_pre_imp_bir_pre_thm;
  val bir_post_defs = [bir_add_reg_contract_4_post_def];
  val arm8_post_imp_bir_post_thm = arm8_post_imp_bir_post_thm;
  val bir_is_lifted_prog_thm = examplesBinaryTheory.bir_add_reg_arm8_lift_THM;
*)

  local

(* these dependencies probably need cleanup *)
(* ================================================ *)
open HolKernel boolLib liteLib simpLib Parse bossLib;
open bir_inst_liftingTheory
open bir_lifting_machinesTheory
open bir_lifting_machinesLib bir_lifting_machinesLib_instances;
open bir_interval_expTheory bir_update_blockTheory
open bir_exp_liftingLib bir_typing_expSyntax
open bir_typing_expTheory
open bir_extra_expsTheory
open bir_lifter_general_auxTheory
open bir_programSyntax bir_interval_expSyntax
open bir_program_labelsTheory
open bir_immTheory
open intel_hexLib
open bir_inst_liftingLibTypes
open PPBackEnd Parse

open bir_inst_liftingHelpersLib;
(* ================================================ *)

    open bir_arm8_backlifterTheory;
    open bir_riscv_backlifterTheory;
    open bir_compositionLib;
  in

fun get_arm8_contract bir_ct prog_bin arm8_pre arm8_post bir_prog_def bir_pre_defs bir_pre1_def arm8_pre_imp_bir_pre_thm bir_post_defs arm8_post_imp_bir_post_thm bir_is_lifted_prog_thm = 
  let
    val word_from_address = bir_immSyntax.dest_Imm64 o bir_programSyntax.dest_BL_Address

    val bir_prog = get_bir_cont_prog bir_ct
    val l =
      word_from_address (get_bir_cont_start_label bir_ct)
    val ls_set = get_bir_cont_ilist bir_ct
    val ls = pred_setSyntax.mk_set (map word_from_address (pred_setSyntax.strip_set ls_set))

    val add_lift_thm =
      ISPECL [bir_prog,
	      prog_bin,
	      l,
	      ls,
	      (((el 2) o snd o strip_comb o concl) bir_is_lifted_prog_thm),
	      arm8_pre, arm8_post,
	      get_bir_cont_pre bir_ct,
	      get_bir_cont_post bir_ct] arm8_lift_contract_thm;

    (* Prove the ARM triple by supplying the antecedents of lift_contract_thm *)
    val arm8_contract_thm = prove(
      ``arm8_cont ^prog_bin ^l ^ls ^arm8_pre
		^arm8_post``,

    irule add_lift_thm >>
    REPEAT STRIP_TAC >| [
      (* 1. Prove that the union of variables in the program and precondition are a well-founded variable
       *    set *)
      (* TODO: This subset computation is slooow... *)
      FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss++HolBASimps.VARS_OF_PROG_ss
			   ++pred_setLib.PRED_SET_ss)
	([bir_prog_def, arm8_wf_varset_def, arm8_vars_def]@bir_pre_defs),

      (* 2. Starting address exists in program *)
      FULL_SIMP_TAC std_ss
	[EVAL ``MEM (^(get_bir_cont_start_label bir_ct))
		    (bir_labels_of_program ^(bir_prog))``],

      (* 3. Provide translation of the ARM8 precondition to the BIR precondition *)
      FULL_SIMP_TAC std_ss [bir_pre1_def, arm8_pre_imp_bir_pre_thm],

      (* 4. Provide translation of the ARM8 postcondition to BIR postcondition *)
      FULL_SIMP_TAC std_ss bir_post_defs >>
      ASSUME_TAC (Q.SPEC `{BL_Address (Imm64 ml') | ml' IN ^ls}` arm8_post_imp_bir_post_thm) >>
      FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [bir_post_bir_to_arm8_def] >>
      FULL_SIMP_TAC std_ss [],

      (* 5. Provide the lifter theorem of the program *)
      FULL_SIMP_TAC std_ss [bir_is_lifted_prog_thm],

      (* 6. Provide the BIR triple in the requisite format *)
      ASSUME_TAC bir_ct >>
      `{BL_Address (Imm64 ml') | ml' IN ^ls} = ^ls_set` suffices_by (
              FULL_SIMP_TAC std_ss []
      ) >>
      FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [pred_setTheory.EXTENSION] >>
      METIS_TAC []
    ]
    );

  in
    arm8_contract_thm
  end;

  fun get_riscv_contract bir_ct prog_bin riscv_pre riscv_post bir_prog_def bir_pre_defs bir_pre1_def riscv_pre_imp_bir_pre_thm bir_post_defs riscv_post_imp_bir_post_thm bir_is_lifted_prog_thm =
  let
    val word_from_address = bir_immSyntax.dest_Imm64 o bir_programSyntax.dest_BL_Address

    val bir_prog = get_bir_cont_prog bir_ct
    val l =
      word_from_address (get_bir_cont_start_label bir_ct)
    val ls_set = get_bir_cont_ilist bir_ct
    val ls = pred_setSyntax.mk_set (map word_from_address (pred_setSyntax.strip_set ls_set))

    val add_lift_thm =
      ISPECL [bir_prog,
	      prog_bin,
	      l,
	      ls,
	      (((el 2) o snd o strip_comb o concl) bir_is_lifted_prog_thm),
	      riscv_pre, riscv_post,
	      get_bir_cont_pre bir_ct,
	      get_bir_cont_post bir_ct] riscv_lift_contract_thm;

    (* Prove the RISC-V triple by supplying the antecedents of lift_contract_thm *)
    val riscv_contract_thm = prove(
      ``riscv_cont ^prog_bin ^l ^ls ^riscv_pre ^riscv_post``,

    irule add_lift_thm >>
    REPEAT STRIP_TAC >| [
      (* 1. Prove that the union of variables in the program and precondition are a well-founded variable
       *    set *)
      (* TODO: This subset computation is slooow... *)
      FULL_SIMP_TAC (std_ss++HolBACoreSimps.holBACore_ss++HolBASimps.VARS_OF_PROG_ss
			   ++pred_setLib.PRED_SET_ss)
	([bir_prog_def, riscv_wf_varset_def, riscv_vars_def]@bir_pre_defs),

      (* 2. Starting address exists in program *)
      FULL_SIMP_TAC std_ss
	[EVAL ``MEM (^(get_bir_cont_start_label bir_ct))
		    (bir_labels_of_program ^(bir_prog))``],

      (* 3. Provide translation of the RISC-V precondition to the BIR precondition *)
      FULL_SIMP_TAC std_ss [bir_pre1_def, riscv_pre_imp_bir_pre_thm],

      (* 4. Provide translation of the RISC-V postcondition to BIR postcondition *)
      ASSUME_TAC (Q.ISPEC `{BL_Address (Imm64 ml') | ml' IN ^ls}` riscv_post_imp_bir_post_thm) >>
      FULL_SIMP_TAC std_ss bir_post_defs >>
      FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [bir_post_bir_to_riscv_def] >>
      FULL_SIMP_TAC std_ss [],

      (* 5. Provide the lifter theorem of the program *)
      FULL_SIMP_TAC std_ss [bir_is_lifted_prog_thm],

      (* 6. Provide the BIR triple in the requisite format *)
      ASSUME_TAC bir_ct >>
      `{BL_Address (Imm64 ml') | ml' IN ^ls} = ^ls_set` suffices_by (
              FULL_SIMP_TAC std_ss []
      ) >>
      FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [pred_setTheory.EXTENSION] >>
      METIS_TAC []
    ]
    );

  in
    riscv_contract_thm
  end;

  end
end
