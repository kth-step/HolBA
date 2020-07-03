
open HolKernel Parse boolLib bossLib;

open bslSyntax;

val _ = new_theory "peterson";

fun bloadvar var n =
    bload64_le (bden (bvarmem64_8 "MEM"))
               (bplus (bden (bvarimm64 var),
                       bconst8 n));

fun bstorevar var n v =
    bassign (bvarmem64_8 "MEM",
             bstore_le (bden (bvarmem64_8 "MEM"))
                       (bplus (bden (bvarimm64 var),
                               bconst8 n)) v);

exception WrongCore;
fun other_core n =
    case n of
        0 => 1
      | 1 => 0
      | _ => raise WrongCore;

fun critical_section core =
    bassign (bvarmem64_8 "MEM",
             bstore_le (bden (bvarmem64_8 "MEM"))
                       (bden (bvarimm64 "shared")) (bconst8 1));

fun petersons core =
    bdefprog_list (Type`:'a`) ("p_"^PolyML.makestring core)
                  [(blabel_str ("P"^PolyML.makestring core),

                 [bstorevar "flag" core btrue
                 ,bstorevar "turn" 0 (bconst1 (other_core core))
                 ],

                 (bjmp o belabel_str) "loop")

                  ,(blabel_str "loop",
                    (* TODO each stmt should be atomic *)
                    [bassign (bvarimm 1 "cond",
                              band (beq
                                        (bloadvar "flag" (other_core core),
                                         (bconst64 1))
                                   ,beq
                                        (bloadvar "turn" 0,
                                         bconst1 (other_core core))))
                    ],

                    bcjmp (bden (bvarimm1 "cond"),
                           belabel_str "loop",
                           belabel_str "critical"))

                  ,(blabel_str "critical",
                    [critical_section core],
                    (bjmp o belabel_str) "end")

                  ,(blabel_str "end",
                    [bstorevar "flag" core bfalse],
                    (bhalt o bconst32) 0)];

fun mk_initial prog = bir_state_init prog;

val peterson_init = Define`
  Peterson_init = Par ^(mk_initial (peterson 0)) ^(mk_initial (peterson 1))
`;

Theorem peterson_mutual_exclusion:
!t. is_trace t Peterson_init ==>
    !n. (pc1,pc2) = program_counters n t ==>
          (pc1,pc2) /= (blabel_str "critical", blabel_str "critical")
Proof.
cheat
QED




val _ = export_theory();
