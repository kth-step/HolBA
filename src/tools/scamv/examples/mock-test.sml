open HolKernel Parse boolLib bossLib;
open bir_exp_to_wordsLib;
open bir_rel_synthLib;
open bslSyntax;
open wordsSyntax;
open bir_embexp_driverLib;
open bir_symb_execLib;

(* Load the dependencies in interactive sessions *)
val _ = if !Globals.interactive then (
  load "../Z3_SAT_modelLib"; (* ../ *)
  load "../bir_exp_to_wordsLib"; (* ../ *)
  ()) else ();

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = Globals.show_tags := true;

(*
val _ = Globals.linewidth := 100;
val _ = wordsLib.add_word_cast_printer ();
val _ = Feedback.set_trace "HolSmtLib" 4;
val _ = Globals.show_assums := true;
val _ = Globals.show_types := true;
*)



val cond1 = bandl [ble (bconst64 (0x30000 + 0x80000000),
                       bden (bvarimm64 "R1")),
                  ble (bden (bvarimm64 "R1"), bconst64 (0x42ff8 + 0x80000000))
                 ];


val prog_w_obs = ``BirProgram
      [<|bb_label := BL_Address_HC (Imm64 0w) "F9400023 (ldr x3, [x1])";
         bb_statements :=
         [BStmt_Assert
              (^cond1);
	   BStmt_Assert
              (BExp_Aligned Bit64 3 (BExp_Den (BVar "R1" (BType_Imm Bit64))));
            BStmt_Assign (BVar "R3" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_Den (BVar "R1" (BType_Imm Bit64))) BEnd_LittleEndian
                 Bit64);
            BStmt_Observe (BExp_Const (Imm1 1w))
                          ([BExp_BinExp BIExp_And
                                        (BExp_Const (Imm64 0x1FC0w))
                                        (BExp_Den (BVar "R1" (BType_Imm Bit64)))])
                          (\x. x)];
         bb_last_statement := BStmt_Halt (BExp_Const (Imm64 4w))|>]``;


(* execute symbolically and determine paths *)
val tree = symb_exec_program prog_w_obs;

(* TODO: proper leaf collecting *)
val Symb_Node n = tree;
val (s1,_,_) = n;

fun extract_cond_obs s =
  let
    val (_,_,cond,_,obs) = dest_bir_symb_state s;
  in
    (cond, obs)
  end;
(*
extract_cond_obs s1
*)

val leafs = [s1];
val leaf_cond_obss = List.map extract_cond_obs leafs;

(* TODO: generalize this *)
val [(cond,obs_l)] = leaf_cond_obss;
val obs_cond_exp = (snd o dest_eq o concl o EVAL) (``(HD ^obs_l).obs_cond``);
val obs_exp = (snd o dest_eq o concl o EVAL) (``(HD ^obs_l).obs``);


val prog_obss_paths =
    [
      (bnot cond, NONE),
      (cond,
       SOME [
           (obs_cond_exp, obs_exp)
      ])
    ];

(*
val cond = bandl [ble (bconst64 (0x30000 + 0x80000000),
                       bden (bvarimm64 "R1")),
                  ble (bden (bvarimm64 "R1"), bconst64 (0x42ff8 + 0x80000000)),
                  (*``BExp_Aligned Bit64 3 (BExp_Den (BVar "R1" (BType_Imm Bit64)))``*)
                  beq (
                    band ((bden o bvarimm64) "R1", bconst64 0xF),
                    bconst64 0
                  )
                 ];

val bir_true = ``BExp_Const (Imm1 1w)``;
*)
(*
val prog_obss_paths =
    [
      (bnot cond, NONE),
      (cond,
       SOME [
           (bir_true, ``BExp_BinExp BIExp_And
                        (BExp_Const (Imm64 0x1FC0w))
                        (BExp_Den (BVar "R1" (BType_Imm Bit64)))``)
      ])
    ];
*)

(* TODO: handle HOL4 variables in BIR consts *)
val relation = mkRel prog_obss_paths;

(* Prints a model, one variable per line. *)
fun print_model model = List.foldl
  (fn ((name, tm), _) => (print (" - " ^ name ^ ": "); Hol_pp.print_term tm))
  () (rev model);

fun to_sml_ints model = List.map (fn (name, tm) => (name, uint_of_word tm)) model;

(*val word_relation = bir2bool relation;*)
val word_relation = ``^(bir2bool relation) /\ (R1 <> R1')``;
val model = Z3_SAT_modelLib.Z3_GET_SAT_MODEL word_relation;
val _ = (print "SAT model:\n"; print_model model(*; print "\n"*));

val sml_model = to_sml_ints model;
fun isPrimedRun s = String.isSuffix "_" s;
val (s2,s1) = List.partition (isPrimedRun o fst) sml_model;

val test_result =  bir_embexp_run_cache_distinguishability "ldr x2, [x1]" s1 s2;

val _ = print ("result = " ^ (if test_result then "ok!" else "failed") ^ "\n\n");
