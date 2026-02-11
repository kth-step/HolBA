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

  fun get_arch_contract arch_cont
   arch_lift_contract_thm arch_wf_varset_def arch_vars_def bir_post_bir_to_arch_def
   bir_ct prog_bin arch_pre arch_post bir_prog_def bir_pre_defs
   bir_pre1_def arch_pre_imp_bir_pre_thm bir_post_defs
   arch_post_imp_bir_post_thm bir_is_lifted_prog_thm =
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
	      arch_pre, arch_post,
	      get_bir_cont_pre bir_ct,
	      get_bir_cont_post bir_ct] arch_lift_contract_thm;

    (* Prove the arch triple by supplying the antecedents of lift_contract_thm *)
    val arch_contract_thm = prove(
      ``^arch_cont ^prog_bin ^l ^ls ^arch_pre ^arch_post``,

    irule add_lift_thm >>
    REPEAT STRIP_TAC >| [
      (* 1. Prove that the union of variables in the program and precondition are a well-founded variable
       *    set *)
      rewrite_tac [bir_prog_def] >>
      CONV_TAC (bir_convLib.bir_vars_of_program_CONV) >>
      rewrite_tac ([arch_wf_varset_def, arch_vars_def]@bir_pre_defs) >>
      CONV_TAC (bir_convLib.bir_vars_of_exp_CONV) >>
      CONV_TAC (
        LAND_CONV (pred_setLib.UNION_CONV bir_convLib.bir_var_EQ_CONV) THENC
        holba_convLib.SUBSET_CONV bir_convLib.bir_var_EQ_CONV
      ),
      (* 2. Starting address exists in program *)
      rewrite_tac [bir_prog_def] >>
      CONV_TAC (
        bir_convLib.bir_labels_of_program_CONV THENC
        RAND_CONV holba_convLib.LIST_TO_SET_CONV THENC
        pred_setLib.IN_CONV bir_convLib.bir_label_EQ_CONV
      ),

      (* 3. Provide translation of the arch precondition to the BIR precondition *)
      FULL_SIMP_TAC std_ss [bir_pre1_def, arch_pre_imp_bir_pre_thm],

      (* 4. Provide translation of the arch postcondition to BIR postcondition *)
      ASSUME_TAC (Q.ISPEC `{BL_Address (Imm64 ml') | ml' IN ^ls}` arch_post_imp_bir_post_thm) >>
      FULL_SIMP_TAC std_ss bir_post_defs >>
      FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [bir_post_bir_to_arch_def] >>
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
    arch_contract_thm
  end;

  fun get_arch_contract_thm arch_cont
   arch_lift_contract_thm arch_wf_varset_def arch_vars_def bir_post_bir_to_arch_def
   bir_ct init_addr_def end_addr_defs prog_bin_def arch_pre_def arch_post_def bir_prog_def bir_pre_defs
   bir_pre1_def arch_pre_imp_bir_pre_thm bir_post_defs
   arch_post_imp_bir_post_thm bir_is_lifted_prog_thm =
  let
    val prog_bin = (fst o dest_eq o concl) prog_bin_def;
    val arch_pre = (fst o dest_comb o lhs o snd o strip_forall o concl) arch_pre_def;
    val arch_post = (fst o dest_comb o lhs o snd o strip_forall o concl) arch_post_def;
    val init_addr = (fst o dest_eq o concl) init_addr_def;
    val end_addrs = pred_setSyntax.mk_set (map (fst o dest_eq o concl) end_addr_defs);
    val word_from_address = bir_immSyntax.dest_Imm64 o bir_programSyntax.dest_BL_Address;
    val bir_prog = get_bir_cont_prog bir_ct;
    val l = word_from_address (get_bir_cont_start_label bir_ct);
    val ls_set = get_bir_cont_ilist bir_ct;
    val ls = pred_setSyntax.mk_set (map word_from_address (pred_setSyntax.strip_set ls_set));
    val add_lift_thm =
      ISPECL [bir_prog,
	      prog_bin,
	      l,
	      ls,
	      (((el 2) o snd o strip_comb o concl) bir_is_lifted_prog_thm),
	      arch_pre, arch_post,
	      get_bir_cont_pre bir_ct,
	      get_bir_cont_post bir_ct] arch_lift_contract_thm;
    (* Prove the arch triple by supplying the antecedents of lift_contract_thm *)
    val arch_contract_thm = prove (
      ``^arch_cont ^prog_bin ^init_addr ^end_addrs ^arch_pre ^arch_post``,

    once_rewrite_tac (init_addr_def :: end_addr_defs) >>
    irule add_lift_thm >>
    REPEAT STRIP_TAC >| [
      (* 1. Prove that the union of variables in the program and precondition are a well-founded variable
       *    set *)
      rewrite_tac [bir_prog_def] >>
      CONV_TAC (bir_convLib.bir_vars_of_program_CONV) >>
      rewrite_tac ([arch_wf_varset_def, arch_vars_def]@bir_pre_defs) >>
      CONV_TAC (bir_convLib.bir_vars_of_exp_CONV) >>
      CONV_TAC (
        LAND_CONV (pred_setLib.UNION_CONV bir_convLib.bir_var_EQ_CONV) THENC
        holba_convLib.SUBSET_CONV bir_convLib.bir_var_EQ_CONV
      ),
      (* 2. Starting address exists in program *)
      rewrite_tac [bir_prog_def] >>
      CONV_TAC (
        bir_convLib.bir_labels_of_program_CONV THENC
        RAND_CONV holba_convLib.LIST_TO_SET_CONV THENC
        pred_setLib.IN_CONV bir_convLib.bir_label_EQ_CONV
      ),

      (* 3. Provide translation of the arch precondition to the BIR precondition *)
      FULL_SIMP_TAC std_ss [bir_pre1_def, arch_pre_imp_bir_pre_thm],

      (* 4. Provide translation of the arch postcondition to BIR postcondition *)
      ASSUME_TAC (Q.ISPEC `{BL_Address (Imm64 ml') | ml' IN ^ls}` arch_post_imp_bir_post_thm) >>
      FULL_SIMP_TAC std_ss bir_post_defs >>
      FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [bir_post_bir_to_arch_def] >>
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
    arch_contract_thm
  end;

  fun get_arm8_contract bir_ct prog_bin arm8_pre arm8_post bir_prog_def bir_pre_defs
    bir_pre1_def arm8_pre_imp_bir_pre_thm bir_post_defs
    arm8_post_imp_bir_post_thm bir_is_lifted_prog_thm =
   get_arch_contract ``arm8_cont`` arm8_lift_contract_thm
    arm8_wf_varset_def arm8_vars_def bir_post_bir_to_arm8_def
    bir_ct prog_bin arm8_pre arm8_post bir_prog_def
    bir_pre_defs bir_pre1_def arm8_pre_imp_bir_pre_thm bir_post_defs
    arm8_post_imp_bir_post_thm bir_is_lifted_prog_thm;

  fun get_arm8_contract_thm bir_ct init_addr_def end_addr_defs prog_bin_def
    arm8_pre_def arm8_post_def bir_prog_def bir_pre_defs
    bir_pre1_def arm8_pre_imp_bir_pre_thm bir_post_defs
    arm8_post_imp_bir_post_thm bir_is_lifted_prog_thm =
   get_arch_contract_thm ``arm8_cont`` arm8_lift_contract_thm
    arm8_wf_varset_def arm8_vars_def bir_post_bir_to_arm8_def
    bir_ct init_addr_def end_addr_defs prog_bin_def
    arm8_pre_def arm8_post_def bir_prog_def
    bir_pre_defs bir_pre1_def arm8_pre_imp_bir_pre_thm bir_post_defs
    arm8_post_imp_bir_post_thm bir_is_lifted_prog_thm;

  fun get_riscv_contract bir_ct prog_bin riscv_pre riscv_post bir_prog_def bir_pre_defs
    bir_pre1_def riscv_pre_imp_bir_pre_thm bir_post_defs
    riscv_post_imp_bir_post_thm bir_is_lifted_prog_thm =
   get_arch_contract ``riscv_cont`` riscv_lift_contract_thm
    riscv_wf_varset_def riscv_vars_def bir_post_bir_to_riscv_def
    bir_ct prog_bin riscv_pre riscv_post bir_prog_def
    bir_pre_defs bir_pre1_def riscv_pre_imp_bir_pre_thm bir_post_defs
    riscv_post_imp_bir_post_thm bir_is_lifted_prog_thm;

  fun get_riscv_contract_thm bir_ct init_addr_def end_addr_defs prog_bin_def
    riscv_pre_def riscv_post_def bir_prog_def bir_pre_defs
    bir_pre1_def riscv_pre_imp_bir_pre_thm bir_post_defs
    riscv_post_imp_bir_post_thm bir_is_lifted_prog_thm =
   get_arch_contract_thm ``riscv_cont`` riscv_lift_contract_thm
    riscv_wf_varset_def riscv_vars_def bir_post_bir_to_riscv_def
    bir_ct init_addr_def end_addr_defs prog_bin_def
    riscv_pre_def riscv_post_def bir_prog_def
    bir_pre_defs bir_pre1_def riscv_pre_imp_bir_pre_thm bir_post_defs
    riscv_post_imp_bir_post_thm bir_is_lifted_prog_thm;

  end
end
