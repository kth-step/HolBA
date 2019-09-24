structure bir_lifter_simple_interfaceLib =
struct

local

open bir_expSyntax bir_immSyntax bir_envSyntax bir_exp_immSyntax bir_exp_memSyntax;
open bir_bool_expSyntax;

open bir_inst_liftingLib;
open gcc_supportLib;

open listSyntax;
open bir_expLib;

in (* local *)

val log_filename = "benchmark.log";
val log = TextIO.openOut log_filename;

fun print_log_with_style sty f s = let
  val _ = if f then TextIO.output (!log, s) else ();
  val _ = print_with_style_ sty s;
in () end;

val print_log = print_log_with_style [];
val print_l = print_log true;


(* error printing function *)
fun err_to_str disassemble_fun ((err_pc, err_inst, err_inst_desc,
                                 err_descr):bir_inst_error) =
  let
    fun asm_of_hex_code_fun code =
      hd (disassemble_fun [QUOTE code]);
    val err_str = (
             case err_descr of
                 SOME x => bir_inst_liftingExn_data_to_string x
               | NONE => "??? no error description ???"
      );
  in
    (err_inst ^ (" (" ^ err_inst ^ "; " ^ err_inst_desc ^ ")  @ 0x" ^ (Arbnum.toHexString err_pc)) ^ "\r\n\t" ^ err_str)
  end;



(* bir exp size, from wp/examples/aes-test.sml *)
  fun bir_exp_nonstandards exp =
    let
      val ef = bir_exp_nonstandards;
    in
      if is_BExp_Const exp then []
      else if is_BExp_MemConst exp then []
      else if is_BExp_Den exp then []
      else if is_BExp_Cast exp then
        let
          val (castt, exp, sz) = (dest_BExp_Cast) exp;
          val casttstr = castt_to_string castt;
          val szstr = (Int.toString o size_of_bir_immtype_t) sz;
        in
          ef exp
        end

      else if is_BExp_UnaryExp exp then
        let
          val (uop, exp) = (dest_BExp_UnaryExp) exp;
          val uopstr = uop_to_string uop;
        in
          ef exp
        end

      else if is_BExp_BinExp exp then
        let
          val (bop, exp1, exp2) = (dest_BExp_BinExp) exp;
          val bopstr = bop_to_string bop;
        in
          (ef exp1)@(ef exp2)
        end

      else if is_BExp_BinPred exp then
        let
          val (bpredop, exp1, exp2) = (dest_BExp_BinPred) exp;
          val bpredopstr = bpredop_to_string bpredop;
        in
          (ef exp1)@(ef exp2)
        end

      else if is_BExp_MemEq exp then
        let
          val (exp1, exp2) = (dest_BExp_MemEq) exp;
        in
          (ef exp1)@(ef exp2)
        end

      else if is_BExp_IfThenElse exp then
        let
          val (expc, expt, expf) = (dest_BExp_IfThenElse) exp;
        in
          (ef expc)@(ef expt)@(ef expf)
        end

      else if is_BExp_Load exp then
        let
          val (expm, expad, endi, sz) = (dest_BExp_Load) exp;
          val endistr = endi_to_string endi;
          val szstr = (Int.toString o size_of_bir_immtype_t) sz;
        in
          (ef expm)@(ef expad)
        end

      else if is_BExp_Store exp then
        let
          val (expm, expad, endi, expv) = (dest_BExp_Store) exp;
          val endistr = endi_to_string endi;
        in
          (ef expm)@(ef expad)@(ef expv)
        end

      else
        [exp]

    end;
    fun bir_exp_count_bir_nodes_mod exp =
    let
      val ef = bir_exp_count_bir_nodes_mod;
    in
      if is_BExp_Const exp then 1
      else if is_BExp_MemConst exp then 1
      else if is_BExp_Den exp then 1
      else if is_BExp_Cast exp then
        let
          val (castt, exp, sz) = (dest_BExp_Cast) exp;
          val casttstr = castt_to_string castt;
          val szstr = (Int.toString o size_of_bir_immtype_t) sz;
        in
          1+(ef exp)
        end

      else if is_BExp_UnaryExp exp then
        let
          val (uop, exp) = (dest_BExp_UnaryExp) exp;
          val uopstr = uop_to_string uop;
        in
          1+(ef exp)
        end

      else if is_BExp_BinExp exp then
        let
          val (bop, exp1, exp2) = (dest_BExp_BinExp) exp;
          val bopstr = bop_to_string bop;
        in
          1+(ef exp1)+(ef exp2)
        end

      else if is_BExp_BinPred exp then
        let
          val (bpredop, exp1, exp2) = (dest_BExp_BinPred) exp;
          val bpredopstr = bpredop_to_string bpredop;
        in
          1+(ef exp1)+(ef exp2)
        end

      else if is_BExp_MemEq exp then
        let
          val (exp1, exp2) = (dest_BExp_MemEq) exp;
        in
          1+(ef exp1)+(ef exp2)
        end

      else if is_BExp_IfThenElse exp then
        let
          val (expc, expt, expf) = (dest_BExp_IfThenElse) exp;
        in
          1+(ef expc)+(ef expt)+(ef expf)
        end

      else if is_BExp_Load exp then
        let
          val (expm, expad, endi, sz) = (dest_BExp_Load) exp;
          val endistr = endi_to_string endi;
          val szstr = (Int.toString o size_of_bir_immtype_t) sz;
        in
          1+(ef expm)+(ef expad)
        end

      else if is_BExp_Store exp then
        let
          val (expm, expad, endi, expv) = (dest_BExp_Store) exp;
          val endistr = endi_to_string endi;
        in
          1+(ef expm)+(ef expad)+(ef expv)
        end

      else
        raise (ERR "bir_exp_count_bir_nodes" "not an allowed structure")
    end;


(* generic lifting call *)
fun disassembly_section_to_minmax section =
  case section of
      BILMR(addr_start, entries) =>
        let
          val data_strs = List.map fst entries;
	  (* val _ = List.map (fn x => print (x ^ "\r\n")) data_strs; *)
          val lengths_st = List.map String.size data_strs;
          val _ = List.map (fn x => ()) lengths_st;
          val lengths = List.map (fn x => Arbnum.fromInt (x div 2)) lengths_st;
          val length = List.foldr (Arbnum.+) Arbnum.zero lengths;
        in
          (addr_start, Arbnum.+(addr_start, length))
        end;

fun minmax_fromlist ls = List.foldl (fn ((min_1,max_1),(min_2,max_2)) =>
  ((if Arbnum.<(min_1, min_2) then min_1 else min_2),
   (if Arbnum.>(max_1, max_2) then max_1 else max_2))
  ) (hd ls) (tl ls);

fun da_sections_minmax sections =
  minmax_fromlist (List.map disassembly_section_to_minmax sections);



fun split_to_non_overlapping_sections sections =
  let
    val aug_sections = List.map (fn sec => (sec, disassembly_section_to_minmax sec)) (List.rev sections);

    fun sections_overlapping secs (_,(min1,max1)) =
           List.exists (fn (_,(min2,max2)) => not (
               ((Arbnum.< (min1, min2)) andalso (Arbnum.< (max1, max2))) orelse 
               ((Arbnum.< (min2, min1)) andalso (Arbnum.< (max2, max1)))
             )) secs;

    fun update_sections (sec,[])                 = [[sec]]
      | update_sections (sec,(secs::sections_l)) =
            if sections_overlapping secs sec then
              (secs::(update_sections (sec,sections_l)))
            else
              ((sec::secs)::sections_l);

    val sections_l = List.foldr update_sections [] (aug_sections);
  in
    List.map (List.rev o (List.map fst)) sections_l
  end;




fun arch_str_to_funs arch_str = case arch_str of
            "arm8" => (bmil_arm8.bir_lift_prog_gen,
                       arm8AssemblerLib.arm8_disassemble)
          | "m0"   => (bmil_m0_LittleEnd_Process.bir_lift_prog_gen,
                       m0AssemblerLib.m0_disassemble)
     (*     | "riscv"=> (bmil_riscv.bir_lift_prog_gen,
                       riscvAssemblerLib.riscv_disassemble) *)
          | _      => raise (ERR "arch_str_to_funs"
                                 ("architecture \""^arch_str^
                                  "\" unknown"
                                 )
                            )
        ;

fun disassembly_section_to_n_instrs section =
  case section of
      BILMR(addr_start, entries) =>
        List.foldl (fn ((_,entry),(n_code, n_data, n_unknown)) =>
             case entry of
                 BILME_code(_) => (n_code+1, n_data  , n_unknown  )
               | BILME_data    => (n_code  , n_data+1, n_unknown  )
               | BILME_unknown => (n_code  , n_data  , n_unknown+1)
           ) (0,0,0) entries;

(*
val BILMR(addr_start, entries) = (hd sections);
hd entries
*)

fun da_sections_n_instrs sections = List.foldl
  (fn ((n_code_i, n_data_i, n_unknown_i),(n_code, n_data, n_unknown)) =>
     (n_code+n_code_i, n_data+n_data_i, n_unknown+n_unknown_i)
  )
  (0,0,0)
  (List.map disassembly_section_to_n_instrs sections);

(*
val arch_str = "arm8";
val da_file  = "binaries/android/taimen-ppr2.181005.003_bins/system/init.da";
val da_file  = "binaries/android/taimen-ppr2.181005.003_bins/system/system/bin/toybox.da";
*)
fun lift_sections arch_str sections idx =
  let
    val (bmil_bir_lift_prog_gen, disassemble_fun) = arch_str_to_funs arch_str;


    (*
    (* predefined program range *)
    val prog_range = ((Arbnum.fromInt 0), (Arbnum.fromInt 0x1000000));
    (* max for arm8 *)
    val prog_range = ((Arbnum.fromInt 0), (Arbnum.fromInt 0xFFFFFFFFFFFFFFFF));
    (* max for m0 *)
    val prog_range = ((Arbnum.fromInt 0), (Arbnum.fromInt 0xFFFFFFFF));
    (* max for prog *)
    *)
    val prog_range = da_sections_minmax sections;

    val timer = (Time.now());

    val (thm_prog, errors) = bmil_bir_lift_prog_gen prog_range sections;

    val d_time = Time.- (Time.now(), timer);
    val d_s = (Time.toString d_time);
    val _ = print_l ("time_to_lift = " ^ d_s ^ " s\n\n\n");


    (* sum up bir blocks and bir statements in thm_prog *)
    (* calculate block number, also block number by label type, sum and max of block sizes, end statements *)
    (* sum and max of expression sizes? *)
    val _ =
      let
        val prog = ((snd o dest_comb o concl) thm_prog);
        val blocks = (fst o dest_list o dest_BirProgram) prog;
        val n_blocks = length blocks;
        val (n_blocks_a, n_blocks_l) = List.foldl (fn (b,(n_blocks_a, n_blocks_l)) =>
(* val b = (hd blocks); *)
                   let val l = ((snd o dest_eq o concl o EVAL o (fn (l,_,_) => l) o dest_bir_block) b); in
                     if is_BL_Address l then      (n_blocks_a+1, n_blocks_l  )
                     else if is_BL_Address l then (n_blocks_a  , n_blocks_l+1)
                     else raise ERR "lift_file" "unknown label type"
                   end
                 ) (0,0) blocks;

        val (sum_stmts, max_stmts) = List.foldl (fn (b,(sum_stmts, max_stmts)) =>
                   let val n_stmts = 1 + ((length o fst o dest_list o (fn (_,stmts,_) => stmts) o dest_bir_block) b); in
                     (sum_stmts + n_stmts,
                      Int.max(max_stmts, n_stmts))
                   end
                 ) (0,0) blocks;

        val (n_jmp, n_cjmp, n_halt) = List.foldl (fn (b,(n_jmp, n_cjmp, n_halt)) =>
                   let val es = ((fn (_,_,es) => es) o dest_bir_block) b; in
                     if is_BStmt_Jmp es then
                       (n_jmp+1, n_cjmp  , n_halt  )
                     else if is_BStmt_CJmp es then
                       (n_jmp  , n_cjmp+1, n_halt  )
                     else if is_BStmt_Halt es then
                       (n_jmp  , n_cjmp  , n_halt+1)
                     else raise ERR "lift_file" "unknown end statement type"
                   end
                 ) (0,0,0) blocks;

        val _ = print_l ("output BIR statistics:\n");
        val _ = print_l ("  ------- \n");
        val _ = print_l ("  n_blocks = " ^ (Int.toString n_blocks) ^ "\n");
        val _ = print_l ("    - n_blocks_label   = " ^ (Int.toString n_blocks_l) ^ "\n");
        val _ = print_l ("    - n_blocks_address = " ^ (Int.toString n_blocks_a) ^ "\n");
        val _ = print_l ("    ------- \n");
        val _ = print_l ("    - n_jmp    = " ^ (Int.toString n_jmp)  ^ "\n");
        val _ = print_l ("    - n_cjmp   = " ^ (Int.toString n_cjmp) ^ "\n");
        val _ = print_l ("    - n_halt   = " ^ (Int.toString n_halt) ^ "\n");
        val _ = print_l ("  ------- \n");
        val _ = print_l ("  sum_stmts = " ^ (Int.toString sum_stmts) ^ "\n");
        val _ = print_l ("  max_stmts = " ^ (Int.toString max_stmts) ^ "\n");
        val _ = print_l ("  ------- \n");

        val _ =
          let
            val (sum_exp_size, max_exp_size) = List.foldl (fn (b,(sum_exp_size, max_exp_size)) =>
                   let
                     val stmts = (fst o dest_list o (fn (_,stmts,_) => stmts) o dest_bir_block) b;
                     val es = ((fn (_,_,es) => es) o dest_bir_block) b;

(* val s = hd stmts; *)
                     val s_exps = List.map (fn s =>
                            if is_BStmt_Assign s then
                               [(snd o dest_BStmt_Assign) s]
                            else if is_BStmt_Assert s then
                               [(dest_BStmt_Assert) s]
                            else if is_BStmt_Assume s then
                               [(dest_BStmt_Assume) s]
                            else if is_BStmt_Observe s then
                               let val (_,oe,oes,_) = (dest_BStmt_Observe) s; in
                                 (oe::((fst o dest_list) oes))
                               end
                            else raise ERR "lift_file" "unknown statement type"
                          ) stmts;
                     val e_exps = if is_BStmt_Jmp es then
				    let val le = dest_BStmt_Jmp es; in
                                      if is_BLE_Label le then []
                                      else if is_BLE_Exp le then [dest_BLE_Exp le]
                                      else raise ERR "lift_file" "unknown end statement label type"
                                    end
				  else if is_BStmt_CJmp es then
				    let
                                      val (ce, le1, le2) = dest_BStmt_CJmp es;
                                      val le1_ =
                                        if is_BLE_Label le1 then []
                                        else if is_BLE_Exp le1 then [dest_BLE_Exp le1]
                                        else raise ERR "lift_file" "unknown end statement label type";
                                      val le2_ =
                                        if is_BLE_Label le2 then []
                                        else if is_BLE_Exp le2 then [dest_BLE_Exp le2]
                                        else raise ERR "lift_file" "unknown end statement label type";
                                    in
                                      (ce::(le1_@le2_))
                                    end
				  else if is_BStmt_Halt es then []
				  else raise ERR "lift_file" "unknown end statement type";

                     val exps = List.concat (e_exps::s_exps);

                     val rewrs = [bir_extra_expsTheory.BExp_Aligned_def,
                                  BExp_unchanged_mem_interval_distinct_def,
                                  BExp_MSB_def, bir_bool_expTheory.bir_exp_true_def, bir_bool_expTheory.bir_exp_false_def];
                     val norm_conv = if true then EVAL else (REWRITE_CONV rewrs);


                     val exps = List.map (fn exp =>
                           (snd o dest_eq o concl o norm_conv) exp
                           handle UNCHANGED => exp
                         ) exps;

                     val _ =
                       let
                         val nonstd_exp = List.concat (List.map bir_exp_nonstandards exps);
                       in
                         if nonstd_exp = [] then ()
                         else (
                           print_l "something is fishy! non standard expressions found\n";
                           List.map ((K (print_l "\n")) o print_l o term_to_string) nonstd_exp;
                           raise ERR "lift_file" "contains expressions which cannot be handled"
                         )
                       end;

                     val exp_size = List.foldl (fn (exp,n) => n + (bir_exp_count_bir_nodes_mod exp)) 0 exps;
                   in
                     (sum_exp_size + exp_size,
                      Int.max(max_exp_size, exp_size))
                   end
                 ) (0,0) blocks;

            val _ = print_l ("  sum_exp_size = " ^ (Int.toString sum_exp_size) ^ "\n");
            val _ = print_l ("  max_exp_size = " ^ (Int.toString max_exp_size) ^ "\n");
          in
            ()
          end
          handle HOL_ERR x => print_l ("  error while processing the expressions" ^ ((!ERR_to_string) x) ^ "\n");

        val _ = print_l ("  ------- \n");
        val _ = print_l ("\n");
      in
        ()
      end;
  in
    (thm_prog, errors)
  end;

(* DESCRIPTION: Function transcompiling an entire program stored in a
 * disassembled file to BIR, yielding theorems stating the
 * correctness of the transcompilation.
 * 
 * ARGUMENTS: arch_str is the ISA of the instruction in string format,
 * e.g. "arm8", "m0" or "riscv".
 *
 * da_file is the file containing the disassembled executable,
 * possibly including a pathway, e.g. "binaries/aes-aarch64.da".
 *
 * USAGE: This is the main function for transcompilation of code.
 *
 * EXAMPLES OF USAGE:

   val arch_str = "arm8";
   val da_file = "binaries/bzip2-1.0.6/aarch64-libbz2-emptymain.da";
   val thms = lift_file arch_str da_file;

   val arch_str = "arm8";
   val da_file = "binaries/aes-aarch64.da";
   val thms = lift_file arch_str da_file;

   val arch_str = "arm8";
   val da_file = "binaries/bignum/aarch64-bignum-emptymain.da";
   val thms = lift_file arch_str da_file;

   val arch_str = "m0";
   val da_file = "binaries/bzip2-1.0.6/m0-libbz2-emptymain.da";
   val thms = lift_file arch_str da_file;

   val arch_str = "m0";
   val da_file = "binaries/bignum/m0-bignum-emptymain.da";
   val thms = lift_file arch_str da_file;

 * *)
fun lift_file arch_str da_file =
  let
    val (bmil_bir_lift_prog_gen, disassemble_fun) =
      arch_str_to_funs arch_str;

    val _ = print_log_with_style [Bold, Underline] true ("Lifting \""^da_file^"\" ("^arch_str^")\n");

    val (region_map, sections) = read_disassembly_file_regions da_file;

    (* Calculate the number of instructions of different categories *)
    val _ =
      let
        val (n_code, n_data, n_unknown) = da_sections_n_instrs sections;

        val _ = print_l ("input binary contents (number of instructions):\n");
        val _ = print_l ("  code    = " ^ (Int.toString n_code) ^ "\n");
        val _ = print_l ("  data    = " ^ (Int.toString n_data) ^ "\n");
        val _ = print_l ("  unknown = " ^ (Int.toString n_unknown) ^ "\n\n");
      in
        ()
      end;


    val sections_l = split_to_non_overlapping_sections sections;
(*    List.map (List.map disassembly_section_to_minmax) sections_l  *)
    val sections_to_lift = List.tabulate (length sections_l, fn x => x);

    val _ = print_l ("had to split the sections of the file into " ^ (Int.toString (length sections_l)) ^ " subsets.");

    val (thms, errors) = List.foldr (fn (idx,(thms, errors)) =>
      let
        val (lift_thm, lift_errors) = lift_sections arch_str (List.nth(sections_l,idx)) idx;
      in
        (lift_thm::thms, lift_errors@errors)
      end) ([],[]) sections_to_lift;

    (* Print only the failing instructions, for debug purposes *)
    val _ = if errors <> [] then
      let
        val _ = print_l "\n\n";
        val _ = print_log_with_style [Bold, Underline] true ("There are " ^ (Int.toString (length errors)) ^ " failing instruction(s)\n");
        val _ = print_with_style_ [Bold, Underline] "Failing instructions\n";
        val _ = List.foldl (fn (x, ()) => print ((err_to_str disassemble_fun x) ^ "\n")) () errors;
      in
        ()
      end else ();
  in
    thms
  end;

(* gen_sections is an auxiliary function to list_inst. *)
fun gen_sections disassemble_fun (pc:Arbnum.num) (inst:string) =
  let
    fun asm_of_hex_code_fun code =
      hd (disassemble_fun [QUOTE code]);
  in
    [BILMR (pc,
            [(inst, BILME_code (SOME (asm_of_hex_code_fun inst)))]
           )
    ]
  end;

(* DESCRIPTION: Function transcompiling a single instruction to BIR,
 * yielding a theorem stating the correctness of the
 * transcompilation.
 * 
 * ARGUMENTS: arch_str is the ISA of the instruction in string format,
 * e.g. "arm8", "m0" or "riscv".
 *
 * pc is a program counter in the form of a number. This should
 * correspond with the position in the disassembled code. To make
 * it easier to see you use the correct position, convert from
 * hexadecimal when giving the argument, e.g.: Arbnum.fromInt 0xCFEE
 *
 * inst is the instruction in string format, e.g.: "78206A61"
 *
 * USAGE: When debugging. Note that no arguments point to any program -
 * the programs are hard-coded inside arch_str_to_funs.
 *
 * EXAMPLES OF USAGE:

     val arch_str = "arm8";
     val pc = (Arbnum.fromInt 0x40C2A4);
     val inst = "78206A61";
     val thm_prog = lift_inst arch_str pc inst;

     val arch_str = "m0";
     val pc = (Arbnum.fromInt 0xCFEE);
     val inst = "4770";
     val thm_prog = lift_inst arch_str pc inst;

 * *)
fun lift_inst arch_str (pc:Arbnum.num) (inst:string) =
  let
    val (bmil_bir_lift_prog_gen, disassemble_fun) =
      arch_str_to_funs arch_str
    val sections = gen_sections disassemble_fun pc inst;
    val prog_range = da_sections_minmax sections;
    val (thm_prog, errors) =
      bmil_bir_lift_prog_gen prog_range sections;
  in
    thm_prog
  end;


(*
val arch_str = "arm8";
val thm_prog = lift_inst arch_str (Arbnum.fromInt 0x40C2A4) ("78206A61");

val arch_str = "m0";
val thm_prog = lift_inst arch_str (Arbnum.fromInt 0xCFEE) ("4770");
*)

end (* local *)
