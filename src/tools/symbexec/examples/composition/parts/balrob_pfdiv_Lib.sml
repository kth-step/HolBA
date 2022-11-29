structure balrob_pfdiv_Lib =
struct

local
  open HolKernel Parse

  open bir_miscLib;

  open binariesLib;
  open binariesCfgLib;
  open binariesMemLib;

  open bir_symbexec_driverLib;

open balrob_pends_Lib;

      val timer_meas = timer_start 1;

val ffun_offset = 0x10000734 - 0x293C (* fadd: 0xFFFDD94 *);
fun int_to_numterm i = numSyntax.mk_numeral(Arbnum.fromInt i);
val _ = print "fdiv offset is: 0x";
val _ = print (Arbnum.toHexString (Arbnum.fromInt ffun_offset));
val _ = print "\n";

(*
(n2w ^(int_to_numterm (ffun_offset + 
)))
*)



(*
    
    2930:	d224      	bcs.n	297c <__aeabi_fdiv+0x1d0>

    2932:	211b      	movs	r1, #27
    
    2934:	2500      	movs	r5, #0
    2936:	3e01      	subs	r6, #1
    2938:	2701      	movs	r7, #1

    293a:	0010      	movs	r0, r2
    293c:	006d      	lsls	r5, r5, #1
    293e:	0052      	lsls	r2, r2, #1
    2940:	2800      	cmp	r0, #0
    2942:	db01      	blt.n	2948 <__aeabi_fdiv+0x19c>
    2944:	4294      	cmp	r4, r2
    2946:	d801      	bhi.n	294c <__aeabi_fdiv+0x1a0>
    2948:	1b12      	subs	r2, r2, r4
    294a:	433d      	orrs	r5, r7
    294c:	3901      	subs	r1, #1
    294e:	2900      	cmp	r1, #0
    2950:	d1f3      	bne.n	293a <__aeabi_fdiv+0x18e>

    297c:	1b12      	subs	r2, r2, r4
    297e:	211a      	movs	r1, #26
    2980:	2501      	movs	r5, #1
    2982:	e7d9      	b.n	2938 <__aeabi_fdiv+0x18c>

*)

(* sum___aeabi_fdiv_loop_body *)
val sums        = [];
val lbl_tm      =  ``BL_Address (Imm32 (n2w ^(int_to_numterm (ffun_offset + 0x293C))))``;
val end_lbl_tms = [``BL_Address (Imm32 (n2w ^(int_to_numterm (ffun_offset + 0x294E))))``];
val usage = (0, 9);

val sum___aeabi_fdiv_loop_body =
      obtain_summary n_dict bl_dict_ sums usage lbl_tm end_lbl_tms;
val _ = print_summary_info sum___aeabi_fdiv_loop_body "sum___aeabi_fdiv_loop_body";


(* sum___aeabi_fdiv_loop *)
val sums        = [sum___aeabi_fdiv_loop_body];
val lbl_tm      =  ``BL_Address (Imm32 (n2w ^(int_to_numterm (ffun_offset + 0x2930))))``;
val end_lbl_tms = [``BL_Address (Imm32 (n2w ^(int_to_numterm (ffun_offset + 0x2952))))``];
val usage = (0, 381);

val sum___aeabi_fdiv_loop =
      obtain_summary n_dict bl_dict_ sums usage lbl_tm end_lbl_tms;
val _ = print_summary_info sum___aeabi_fdiv_loop "sum___aeabi_fdiv_loop";


(* ====================================================================== *)


(* sum___aeabi_fdiv_c1 *)
val sums        = [];
val lbl_tm      =  ``BL_Address (Imm32 (n2w ^(int_to_numterm (ffun_offset + 0x27CA))))``;
val end_lbl_tms = [``BL_Address (Imm32 (n2w ^(int_to_numterm (ffun_offset + 0x27DC))))``];
val usage = (0, 15);

val sum___aeabi_fdiv_c1 =
      obtain_summary n_dict bl_dict_ sums usage lbl_tm end_lbl_tms;
val _ = print_summary_info sum___aeabi_fdiv_c1 "sum___aeabi_fdiv_c1";


(*
(* sum___aeabi_fdiv_c2 *)
val sums        = [];
val lbl_tm      =  ``BL_Address (Imm32 0x2930w)``;
val end_lbl_tms = [``BL_Address (Imm32 0x2938w)``];
val usage = (0, 20);

val sum___aeabi_fdiv_c2 =
      obtain_summary n_dict bl_dict_ sums usage lbl_tm end_lbl_tms;
val _ = print_summary_info sum___aeabi_fdiv_c2 "sum___aeabi_fdiv_c2";
*)

(* sum___aeabi_fdiv_c3 *)
val sums        = [];
val lbl_tm      =  ``BL_Address (Imm32 (n2w ^(int_to_numterm (ffun_offset + 0x2842))))``;
val end_lbl_tms = [``BL_Address (Imm32 (n2w ^(int_to_numterm (ffun_offset + 0x284E))))``];
val usage = (0, 7);

val sum___aeabi_fdiv_c3 =
      obtain_summary n_dict bl_dict_ sums usage lbl_tm end_lbl_tms;
val _ = print_summary_info sum___aeabi_fdiv_c3 "sum___aeabi_fdiv_c3";


(* sum___aeabi_fdiv_c4 *)
val sums        = [];
val lbl_tm      =  ``BL_Address (Imm32 (n2w ^(int_to_numterm (ffun_offset + 0x2850))))``;
val end_lbl_tms = [``BL_Address (Imm32 (n2w ^(int_to_numterm (ffun_offset + 0x285A))))``];
val usage = (0, 6);

val sum___aeabi_fdiv_c4 =
      obtain_summary n_dict bl_dict_ sums usage lbl_tm end_lbl_tms;
val _ = print_summary_info sum___aeabi_fdiv_c4 "sum___aeabi_fdiv_c4";


(* sum___aeabi_fdiv_c5 *)
val sums        = [];
val lbl_tm      =  ``BL_Address (Imm32 (n2w ^(int_to_numterm (ffun_offset + 0x2996))))``;
val end_lbl_tms = [``BL_Address (Imm32 (n2w ^(int_to_numterm (ffun_offset + 0x29A2))))``];
val usage = (0, 7);

val sum___aeabi_fdiv_c5 =
      obtain_summary n_dict bl_dict_ sums usage lbl_tm end_lbl_tms;
val _ = print_summary_info sum___aeabi_fdiv_c5 "sum___aeabi_fdiv_c5";


(* sum___aeabi_fdiv_c6 *)
val sums        = [];
val lbl_tm      =  ``BL_Address (Imm32 (n2w ^(int_to_numterm (ffun_offset + 0x29A4))))``;
val end_lbl_tms = [``BL_Address (Imm32 (n2w ^(int_to_numterm (ffun_offset + 0x286A))))``];
val usage = (0, 8);

val sum___aeabi_fdiv_c6 =
      obtain_summary n_dict bl_dict_ sums usage lbl_tm end_lbl_tms;
val _ = print_summary_info sum___aeabi_fdiv_c6 "sum___aeabi_fdiv_c6";


(* sum___aeabi_fdiv_c7 *)
val sums        = [];
val lbl_tm      =  ``BL_Address (Imm32 (n2w ^(int_to_numterm (ffun_offset + 0x2918))))``;
val end_lbl_tms = [``BL_Address (Imm32 (n2w ^(int_to_numterm (ffun_offset + 0x286A))))``];
val usage = (0, 15);

val sum___aeabi_fdiv_c7 =
      obtain_summary n_dict bl_dict_ sums usage lbl_tm end_lbl_tms;
val _ = print_summary_info sum___aeabi_fdiv_c7 "sum___aeabi_fdiv_c7";


(* __aeabi_fdiv *)
val sums        = [sum___clzsi2,
                   sum___aeabi_fdiv_loop,
                   sum___aeabi_fdiv_c1,
                   (*sum___aeabi_fdiv_c2,*)
                   sum___aeabi_fdiv_c3,
                   sum___aeabi_fdiv_c4,
                   sum___aeabi_fdiv_c5,
                   sum___aeabi_fdiv_c6,
                   sum___aeabi_fdiv_c7];
val entry_label = "__aeabi_fdiv";

val sum___aeabi_fdiv =
      create_func_summary n_dict bl_dict_ sums entry_label;

      val _ = timer_stop (fn s => print("time for fdiv: " ^ s ^ "\n")) timer_meas;

(*
2mins including building supporting summaries
time to drive symbolic execution: 95.967s

min = 77w
max = 581w
*)


in (* outermost local *)

val sum___aeabi_fdiv = sum___aeabi_fdiv;

end (* outermost local *)

end (* struct *)
