open HolKernel boolLib liteLib simpLib Parse bossLib;

open bir_typing_progTheory;
open bir_typing_expTheory;

open bir_valuesTheory;
open bir_immTheory;

open pred_setSyntax;
open bir_valuesSyntax;

open bir_exec_auxLib;

open optionSyntax;


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



(* TODO: *)
(*
type_of_bir_exp
(bir_vars_of_exp)
(bir_var_set_is_well_typed vs)
((bir_exp_is_well_typed))
bir_is_well_typed_program
*)

(*
  val bir_exec_typing_exp_conv =
    let
      val is_tm_fun = is_type_of_bir_val;
      val check_tm_fun = (fn t => is_none t orelse
                                  (is_some t andalso
                                   let
                                     val bt = dest_some t;
                                   in
                                     (List.exists (fn f => f bt) [is_BType_Imm1,
                                                                  is_BType_Imm8,
                                                                  is_BType_Imm16,
                                                                  is_BType_Imm32,
                                                                  is_BType_Imm64]
                                     ) orelse is_BType_Mem bt
                                   end)
                         );
      val conv = (REWRITE_CONV [type_of_bir_val_def, type_of_bir_imm_def]);
    in
      GEN_selective_conv is_tm_fun check_tm_fun conv
    end;
*)

end
