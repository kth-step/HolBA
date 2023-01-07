structure mymodexp_Lib =
struct

local
  open HolKernel Parse

  open bir_miscLib;

  open binariesLib;
  open binariesCfgLib;
  open binariesMemLib;

  open bir_symbexec_driverLib;

(*
  open aeabi_uidivmod_Lib;
*)

fun int_to_numterm i = numSyntax.mk_numeral(Arbnum.fromInt i);




(* _mymodexp_uidivmod_assmpt *)
val sum__mymodexp_uidivmod_assmpt =
  let
      open bir_symbexec_stateLib;

      val prog_vars = binariesLib.prog_vars;
      val envlist_progvars = List.map (fn bv => (bv, get_bvar_init bv)) prog_vars;

      val lbl_start_tm = “BL_Address (Imm32 0x1000010cw)”;
      val lbl_tm = “BL_Address (Imm32 0x10000112w)”;

      val preds = [];
      val env  = (Redblackmap.fromList Term.compare envlist_progvars);
      val vals = (Redblackmap.fromList Term.compare []):(term, symb_value) Redblackmap.dict;

      (* SYST_mk pc env status obss pred vals *)
      val systarget_new =
        SYST_mk lbl_tm
              env
              BST_Running_tm
              []
              preds
              vals;

      val bv = bir_countw_simplificationLib.bv_countw;
      val bv_pre = “BVar "sy_countw" (BType_Imm Bit64)”;
      val bv_fr = (get_bvar_fresh) bv;

      val exp_l   = ``
        BExp_BinExp BIExp_Plus
          ^(bir_expSyntax.mk_BExp_Den bv_pre)
          (BExp_Const (Imm64 0w))``;
      val exp_u   = ``
        BExp_BinExp BIExp_Plus
          ^(bir_expSyntax.mk_BExp_Den bv_pre)
          (BExp_Const (Imm64 242w))``;

      val deps  = Redblackset.add (symbvalbe_dep_empty, bv_pre);
      val symbv = SymbValInterval ((exp_l, exp_u), deps);

      val systarget_countw =
        (update_envvar bv bv_fr o insert_symbval bv_fr symbv) systarget_new;

      open bir_countw_simplificationLib;
      open commonBalrobScriptLib;
      open bir_symbexec_coreLib;
      val systarget =
        state_make_mem bv_mem
             (Arbnum.fromInt mem_sz_const, Arbnum.fromInt mem_sz_globl, Arbnum.fromInt mem_sz_stack)
                 (mem_read_byte binary_mem)
                 bv_sp
                 systarget_countw;
  in
    (lbl_start_tm, "path predicate goes here",
        [systarget])
  end;

val _ = print_summary_info sum__mymodexp_uidivmod_assmpt "sum__mymodexp_uidivmod_assmpt";


      val timer_meas = timer_start 1;

(* _mymodexp *)

(*
val aeabi_uidivmod_end_lbl_tms =
  [``BL_Address (Imm32 (n2w ^(int_to_numterm (0x100000fc))))``,
   ``BL_Address (Imm32 (n2w ^(int_to_numterm (0x10000108))))``];


val aeabi_uidivmod_exit_end_lbl_tms =
  [``BL_Address (Imm32 (n2w ^(int_to_numterm (0x1000009e))))``,
   ``BL_Address (Imm32 (n2w ^(int_to_numterm (0x100000ce))))``,
   ``BL_Address (Imm32 (n2w ^(int_to_numterm (0x100000f2))))``,
   ``BL_Address (Imm32 (n2w ^(int_to_numterm (0x100000fe))))``];


(* __aeabi_uidivmod_entry *)
val sums        = [];
val lbl_tm      =  ``BL_Address (Imm32 (n2w ^(int_to_numterm (0x10000000))))``;
val end_lbl_tms = [``BL_Address (Imm32 (n2w ^(int_to_numterm (0x1000003c))))``,
                   ``BL_Address (Imm32 (n2w ^(int_to_numterm (0x1000006c))))``,
                   ``BL_Address (Imm32 (n2w ^(int_to_numterm (0x10000020))))``]
                  @aeabi_uidivmod_end_lbl_tms
                  @aeabi_uidivmod_exit_end_lbl_tms;
val usage = (0, 18);

val sum___aeabi_uidivmod_entry =
      obtain_summary n_dict bl_dict_ sums usage lbl_tm end_lbl_tms;
val _ = print_summary_info sum___aeabi_uidivmod_entry "sum___aeabi_uidivmod_entry";


(* __aeabi_uidivmod_lp1 *)
val sums        = [];
val lbl_tm      =  ``BL_Address (Imm32 (n2w ^(int_to_numterm (0x1000003c))))``;
val end_lbl_tms = [``BL_Address (Imm32 (n2w ^(int_to_numterm (0x1000006c))))``];
val usage = (0, 24);

val sum___aeabi_uidivmod_lp1 =
      obtain_summary n_dict bl_dict_ sums usage lbl_tm end_lbl_tms;
val _ = print_summary_info sum___aeabi_uidivmod_lp1 "sum___aeabi_uidivmod_lp1";
*)


(*
(* _mymodexp_loop *)
val sums        = [sum__mymodexp_uidivmod_assmpt];
val lbl_tm      =  ``BL_Address (Imm32 (n2w ^(int_to_numterm (0x1000150a))))``;
val end_lbl_tms = [``BL_Address (Imm32 (n2w ^(int_to_numterm (0x10001504))))``];
val usage = (100, 500);

val sum__mymodexp_loop =
      obtain_summary n_dict bl_dict_ sums usage lbl_tm end_lbl_tms;
val _ = print_summary_info sum__mymodexp_loop "sum__mymodexp_loop";
*)

val sums        = [sum__mymodexp_uidivmod_assmpt];
val entry_label = "sum__mymodexp_loop_1";
(*
val sum__mymodexp =
      create_func_summary n_dict bl_dict_ sums entry_label;
*)
val lbl_tm      =  ``BL_Address (Imm32 (n2w ^(int_to_numterm (0x100014f0))))``;
val end_lbl_tms = [``BL_Address (Imm32 (n2w ^(int_to_numterm (0x1000155a))))``,
                   ``BL_Address (Imm32 (n2w ^(int_to_numterm (0x1000156c))))``];
val usage = (100, 500);

val sum__mymodexp_loop_1 =
      obtain_summary n_dict bl_dict_ sums usage lbl_tm end_lbl_tms;
val _ = print_summary_info sum__mymodexp_loop_1 "sum__mymodexp_loop_1";



(*
val idx = 2;
val summary = sum__mymodexp_loop_1;
*)
fun execute_an_iteration idx summary =
  let

val sums        = [summary];
(*
val sum__mymodexp =
      create_func_summary n_dict bl_dict_ sums entry_label;
*)
val lbl_tm      =  ``BL_Address (Imm32 (n2w ^(int_to_numterm (0x100014f0))))``;
val end_lbl_tms = [``BL_Address (Imm32 (n2w ^(int_to_numterm (0x10001504))))``];
val usage = (100, 500);

val sum__mymodexp_loop_idx1 =
      obtain_summary n_dict bl_dict_ sums usage lbl_tm end_lbl_tms;

val _ = print_summary_info sum__mymodexp_loop_idx1 ("sum__mymodexp_loop_p1_" ^ (Int.toString idx));

val sums        = [sum__mymodexp_loop_idx1, sum__mymodexp_uidivmod_assmpt];
val end_lbl_tms = [``BL_Address (Imm32 (n2w ^(int_to_numterm (0x1000155a))))``,
                   ``BL_Address (Imm32 (n2w ^(int_to_numterm (0x1000156c))))``];
val sum__mymodexp_loop_idx2 =
      obtain_summary n_dict bl_dict_ sums usage lbl_tm end_lbl_tms;

val _ = print_summary_info sum__mymodexp_loop_idx2 ("sum__mymodexp_loop_" ^ (Int.toString idx));

  in
    sum__mymodexp_loop_idx2
  end;


val sum__mymodexp_loop_2 = execute_an_iteration 2 sum__mymodexp_loop_1;
val sum__mymodexp_loop_3 = execute_an_iteration 3 sum__mymodexp_loop_2;
val sum__mymodexp_loop_4 = execute_an_iteration 4 sum__mymodexp_loop_3;
val sum__mymodexp_loop_5 = execute_an_iteration 5 sum__mymodexp_loop_4;
val sum__mymodexp_loop_6 = execute_an_iteration 6 sum__mymodexp_loop_5;
val sum__mymodexp_loop_7 = execute_an_iteration 7 sum__mymodexp_loop_6;
val sum__mymodexp_loop_8 = execute_an_iteration 8 sum__mymodexp_loop_7;


val sums        = [sum__mymodexp_loop_8];
val entry_label = "_mymodexp";
val lbl_tm      =  ``BL_Address (Imm32 (n2w ^(int_to_numterm (0x100014f0))))``;
val end_lbl_tms = [``BL_Address (Imm32 (n2w ^(int_to_numterm (0x1000156c))))``,
                   ``BL_Address (Imm32 (n2w ^(int_to_numterm (0x1000010c))))``];

val sum__mymodexp =
      obtain_summary n_dict bl_dict_ sums usage lbl_tm end_lbl_tms;

val _ = print_summary_info sum__mymodexp "sum__mymodexp";


      val _ = timer_stop (fn s => print("time for " ^ entry_label ^ ": " ^ s ^ "\n")) timer_meas;


in (* outermost local *)

(*
  val sum___aeabi_uidivmod      = sum___aeabi_uidivmod;
*)

end (* outermost local *)

end (* struct *)
