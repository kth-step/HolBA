structure generationLib =
struct

open HolKernel Parse boolLib bossLib;

open listSyntax pairSyntax stringSyntax;
open bir_execLib bslSyntax bir_immSyntax wordsSyntax;

val observe_type = Type `: 'a`
val bdefprog_list = bdefprog_list observe_type

fun entry_block1(middle_blocks_n, exit_addr): term * term list * term =
  (blabel_str "entry1",
   [],
   bcjmp (blt((bden o bvarimm64) "x", (bconst64 middle_blocks_n)),
          belabel_str "entry2",
          belabel_addr64 exit_addr))

val entry_block2: term * term list * term =
  (blabel_str "entry2",
   [],
   (bjmp o belabel_expr o bden o bvarimm64) "x")

fun middle_block(addr, exit_addr): term * term list * term =
  (blabel_addr64 addr,
   [bassign (bvarimm64 "y", bconst64 exit_addr)],
   (bjmp o belabel_expr o bden o bvarimm64) "y")

fun middle_blocks(addrs, exit_addr) = 
  List.map (fn addr => middle_block(addr, exit_addr)) addrs

fun exit_block(addr): term * term list * term =
  (blabel_addr64 addr,
   [],
   (bhalt o bconst64) 0)

fun gen_program(name, middle_blocks_n) = 
  let
    val exit_addr = middle_blocks_n*10;
    val addrs = List.tabulate(middle_blocks_n, fn i => i);
    val blocks = [entry_block1(middle_blocks_n, exit_addr), entry_block2] @
                 middle_blocks(addrs, exit_addr) @
                 [exit_block(exit_addr)]
  in
    bdefprog_list name blocks
  end

fun gen_label_strings(prefix, n) = 
  List.tabulate(n, (fn i => prefix ^ "-" ^ Int.toString(i + 1)))

fun gen_arg2(ns, ss) =
  let
    val fsts = List.map (mk_Imm_of_int 64) ns;
    val snds = List.map (fromMLstring) ss;
    val list = List.map mk_pair (ListPair.zip(fsts, snds))
  in
    mk_list(list, “:(bir_imm_t#string)”)
  end

fun gen_arg(label, ns, ss) =
  mk_pair(label, gen_arg2(ns, ss))

fun gen_args(xs) =
  let
    val ty = “:(bir_label_t  # (bir_imm_t#string) list)”
  in
    mk_list(List.map gen_arg xs, ty)
  end

fun gen_args_entry_block2(middle_blocks_n) = 
  let
    val targets = List.tabulate(middle_blocks_n, fn i => i);
    val fresh_labels = gen_label_strings("entry2", middle_blocks_n);
  in
    [(blabel_str "entry2", targets, fresh_labels)]
  end

fun gen_args_middle_block(addr, exit_addr, m) =
  let
    val targets = List.tabulate(m, fn _ => exit_addr);
    val fresh_labels = gen_label_strings(Int.toString(addr)^"w", m);
  in
    [(blabel_addr64 addr, targets, fresh_labels)]
  end

fun gen_args_middle_blocks(addrs, exit_addr, m) =
  List.concat (List.map (fn addr => gen_args_middle_block(addr, exit_addr, m)) addrs)

fun gen_args_program(middle_blocks_n, m) =
  let
    val addrs = List.tabulate(middle_blocks_n, fn i => i)
    val exit_address = middle_blocks_n*10
  in
    gen_args (gen_args_entry_block2(middle_blocks_n) @
              gen_args_middle_blocks(addrs, exit_address, m))
 end

fun gen_partial_args_program(middle_blocks_n, m) =
  let
    val addrs = List.rev (List.tabulate(m, fn i => middle_blocks_n - 1 - i))
    val exit_address = middle_blocks_n*10
  in
    gen_args (gen_args_middle_blocks(addrs, exit_address, 1))
 end

end
