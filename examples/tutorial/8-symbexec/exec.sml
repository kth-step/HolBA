
(* ============================================================= *)
open HolKernel Parse;

open examplesBinaryTheory;

open bslSyntax;

open bir_symb2_masterLib;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;

val _ = print "loading...\n";

val name = "add_reg";
val prog = (snd o dest_eq o concl) bir_add_reg_prog_def;
(* ============================================================= *)

(* define binary inputs *)
val get_x = bconst ``R0:word64``;
val get_sp = bconst ``SP_EL0:word64``;

(* ============================================================= *)
(* ============================================================= *)

(* predefined preconditions *)
val precond_0 = btrue;
val precond_1 = beq(bconst64 5, bconst64 7);
val precond_2 = beq(bconst64 5, bconst64 5);
val precond_3 = bslt(get_x, bconst64 2);
val precond_4 = bandl [precond_3, beq(get_sp,bconst64 0x80000000)];
val precond_5 = bandl [bnot (bslt(get_x, bconst64 0)), precond_3, beq(get_sp,bconst64 0x80000000)];
val precond_6 = bandl [beq(get_x, bconst64 0), beq(get_sp,bconst64 0x80000000)];
val precond_7 = bandl [beq(get_x, bconst64 1), beq(get_sp,bconst64 0x80000000)];


(* select precondition *)
val precond = precond_7;

(* max birblock depth *)
val maxdepth_0 = 10;
val maxdepth_1 = 11;
val maxdepth_2 = 3;
val maxdepth_3 = ~1;
val maxdepth_10 = 11+8;
val maxdepth_11 = 11+9;
val maxdepth_12 = 11+9+2;
val maxdepth_13 = 11+9+3;
val maxdepth_14 = 11+9+3+1;
val maxdepth_15 = 11+3+1;
val maxdepth_16 = 11+3+1+88;

val maxdepth = maxdepth_16;




(* ============================================================= *)
(* ============================================================= *)

(* run the symbolic execution *)
val leafs = symb_exec2_process_to_leafs maxdepth precond prog;


(* ============================================================= *)

(* check leafs *)
val _ = print "^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n"
val _ = print "^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n"
val _ = print ("number of leafs: " ^ (Int.toString (length leafs)) ^ "\n\n");


(* ============================================================= *)

(* compute concrete states from path conditions using SMT-solver *)
val wtms = List.map symb_exec2_get_predword leafs;
val states = List.map symb_exec2_get_init_vals wtms;


(* print states *)
val _ = print "^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n"
val _ = print "^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n"
val _ = PolyML.print_depth 10;
val _ = List.foldl (fn (st,_) => (PolyML.print st; print "\n")) () states;

