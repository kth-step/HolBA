
open bir_typing_progTheory;
open bir_typing_expTheory;

open pred_setSyntax;


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

(*
type_of_bir_val
*)

end
