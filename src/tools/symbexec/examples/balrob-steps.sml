open HolKernel Parse

open binariesLib;
open binariesCfgLib;
open binariesMemLib;

open bir_symbexec_sumLib;
open bir_symbexec_driverLib;


(* motor_prep_input 0 *)
val sums        = [];
val usage       = (100, 100);
val entry_label = "motor_prep_input";
val lbl_tm      = find_func_lbl_tm entry_label;



(* motor_prep_input 1 *)
val end_lbl_tms = [``BL_Address (Imm32 0xB0Aw)``];

val sum_motor_prep_input =
      obtain_summary n_dict bl_dict_ sums usage lbl_tm end_lbl_tms;
val _ = print_summary_info sum_motor_prep_input "sum_motor_prep_input";



(* motor_prep_input 2 *)
val end_lbl_tms = [``BL_Address (Imm32 0xB10w)``];

val sum_motor_prep_input =
      obtain_summary n_dict bl_dict_ sums usage lbl_tm end_lbl_tms;
val _ = print_summary_info sum_motor_prep_input "sum_motor_prep_input";



(* motor_prep_input 3 *)
val end_lbl_tms = [``BL_Address (Imm32 0xB1Cw)``];

val sum_motor_prep_input =
      obtain_summary n_dict bl_dict_ sums usage lbl_tm end_lbl_tms;
val _ = print_summary_info sum_motor_prep_input "sum_motor_prep_input";



(* motor_prep_input 4 *)
val end_lbl_tms = [``BL_Address (Imm32 0xB2Aw)``];

val sum_motor_prep_input =
      obtain_summary n_dict bl_dict_ sums usage lbl_tm end_lbl_tms;
val _ = print_summary_info sum_motor_prep_input "sum_motor_prep_input";



(* motor_prep_input x *)
val lbl_tm      =  ``BL_Address (Imm32 0xB08w)``;
val end_lbl_tms = [``BL_Address (Imm32 0xB0Aw)``];

val sum_motor_prep_input =
      obtain_summary n_dict bl_dict_ sums usage lbl_tm end_lbl_tms;
val _ = print_summary_info sum_motor_prep_input "sum_motor_prep_input";



