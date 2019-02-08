open HolKernel boolLib liteLib simpLib Parse bossLib;

open bir_typing_progTheory;
open bir_typing_expTheory;

open bir_valuesTheory;
open bir_immTheory;

open pred_setSyntax;
open bir_valuesSyntax;


structure bir_exec_typingLib =
struct


(*
val prog = ``
       BirProgram [
         <|bb_label :=
             BL_Label "entry";
           bb_statements :=
             [BStmt_Assign (BVar "bit1" BType_Bool)
                           (BExp_MSB Bit32 (BExp_Den (BVar "R1" (BType_Imm Bit32))))];
           bb_last_statement :=
             BStmt_Jmp (BLE_Label (BL_Address (Imm32 0x102w)))|>;
         <|bb_label :=
             BL_Address_HC (Imm32 0x102w) "abc";
           bb_statements :=
             [BStmt_Assign (BVar "R3" (BType_Imm Bit32))
                (BExp_BinExp BIExp_Plus
                   (BExp_Den (BVar "R2" (BType_Imm Bit32)))
                   (BExp_Den (BVar "R3" (BType_Imm Bit32))))];
           bb_last_statement :=
             BStmt_Halt (BExp_Const (Imm32 1w)) |>
       ]``;


val t = ``type_of_bir_val (BVal_Imm (Imm32 x))``

val t = ``type_of_bir_val (BVal_Mem Bit32 Bit32 x)``

val t = ``type_of_bir_val (BVal_Mem Bit32 Bit32 (K 0))``

*)



  fun gen_vars_of_prog prog =
    let
      val rep_gen_set_and_eval_conv =
                   (REWRITE_CONV [bir_vars_of_program_def]) THENC
                   (REPEATC ((SIMP_CONV list_ss []) THENC
                             ((fn t => if op=((dest_eq o concl) t) then raise UNCHANGED else t) o EVAL)
                            ));
      val var_set = (snd o dest_eq o concl o rep_gen_set_and_eval_conv) ``bir_vars_of_program ^prog``;
    in
      strip_set var_set
    end;


  fun bir_exec_typing_exp_conv_help t =
    if not (is_type_of_bir_val t) then
      raise UNCHANGED
    else
      REWRITE_CONV [type_of_bir_val_def, type_of_bir_imm_def] t;





  fun GEN_bir_exec_typing_exp_conv conv tm =
    if is_type_of_bir_val tm then
      conv tm
    else if is_comb tm then
        ((RAND_CONV  (GEN_bir_exec_typing_exp_conv conv)) THENC
         (RATOR_CONV (GEN_bir_exec_typing_exp_conv conv))) tm
    else
      raise UNCHANGED
    ;


(* TODO: *)
(*
type_of_bir_exp
(bir_vars_of_exp)
(bir_var_set_is_well_typed vs)
((bir_exp_is_well_typed))
bir_is_well_typed_program
*)


  val bir_exec_typing_exp_conv = GEN_bir_exec_typing_exp_conv bir_exec_typing_exp_conv_help;

end
