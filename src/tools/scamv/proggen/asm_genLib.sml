structure asm_genLib : asm_genLib =
struct

open HolKernel boolLib liteLib simpLib Parse bossLib;

open qc_genLib;
infix 5 <$>;
infix 5 >>=;

datatype BranchCond = EQ | NE | LT | GT | HS
datatype Operand =
           Imm of int
         | Ld  of int option * string
         | Ld2 of string * string
         | Reg of string
datatype ArmInstruction =
           Load    of Operand * Operand
         | Store   of Operand * Operand
         | Branch  of BranchCond option * Operand
         | Compare of Operand * Operand
         | Nop
         | Add     of Operand * Operand * Operand
	 | Lsl     of Operand * Operand * Operand

(* pp *)
local
fun pp_operand (Imm n) = "#0x" ^ Int.fmt StringCvt.HEX n
  | pp_operand (Ld (NONE, src)) = "[" ^ src ^ "]"
  | pp_operand (Ld (SOME offset, src)) =
    "[" ^ src ^ ", #" ^ Int.toString offset ^ "]"
  | pp_operand (Ld2(src2, src)) =
    "[" ^ src ^ ", " ^ src2 ^ "]"
  | pp_operand (Reg str) = str

fun pp_opcode (Load _)    = "ldr"
  | pp_opcode (Store _)  = "str"
  | pp_opcode (Branch _)  = "b"
  | pp_opcode (Compare _) = "cmp"
  | pp_opcode (Nop)       = "nop"
  | pp_opcode (Add _)     = "add"
  | pp_opcode (Lsl _)     = "lsl"

fun pp_cond bc =
    case bc of
        EQ => "eq"
      | NE => "ne"
      | LT => "lt"
      | GT => "gt"
      | HS => "hs"

fun pp_instr instr =
    case instr of
        Load (target,source) =>
        pp_opcode instr ^ " " ^ pp_operand target ^ ", "
        ^ pp_operand source
     | Store (source, target) =>
        pp_opcode instr ^ " " ^ pp_operand source ^ ", "
        ^ pp_operand target
     |  Branch (NONE, target) =>
        "b " ^ pp_operand target
     | Branch (SOME cond, target) =>
       "b." ^ pp_cond cond ^ " " ^ pp_operand target
     | Compare (a, b) =>
       "cmp " ^ pp_operand a ^ ", " ^ pp_operand b
     | Nop =>
       "nop"
     | Add (target, a, b) =>
       "add " ^ pp_operand target ^ ", " ^ pp_operand a ^ ", " ^ pp_operand b
     | Lsl (target,source ,b) =>
       "lsl " ^ pp_operand target ^ ", " ^ pp_operand source ^ ", " ^ pp_operand b
in
fun pp_program is = List.map pp_instr is;
end

(* arb instances *)
local
  val min_addr = 0x1000;
  val max_addr = 0x2000;
in
  val arb_addr = choose (min_addr, max_addr);
end

val arb_armv8_regname =
    let
        fun regs n = List.tabulate (n, fn x => "x" ^ (Int.toString x))
    in
        elements (regs 30)
    end;

val arb_imm = Imm <$> arb_addr;
val arb_reg = Reg <$> arb_armv8_regname;
val arb_operand =
    frequency
        [(1, arb_imm)
        ,(5, arb_reg)]

local
  val arb_cond = elements [EQ, NE, LT, GT, HS];
in
  val arb_branchcond = arb_option arb_cond;
  val arb_branchcond_cond = (SOME) <$> arb_cond;
end;

val arb_ld = Ld <$> two (arb_option (elements [4,8,16])) arb_armv8_regname;

val arb_load_indir = Load <$> (two arb_reg arb_ld);
val arb_load_pcimm = Load <$> (two arb_reg arb_imm);
val arb_load = oneof [arb_load_indir, arb_load_pcimm];

val arb_store_indir = Store <$> (two arb_reg arb_ld);
val arb_store_pcimm = Store <$> (two arb_reg arb_imm);
val arb_store = oneof [arb_store_indir, arb_store_pcimm];

val arb_branch = Branch <$> (two arb_branchcond arb_imm);
val arb_compare = Compare <$> (two arb_reg arb_reg);
val arb_nop = return Nop;
val arb_add = (fn (t, (a, b)) => Add (t,a,b)) <$> (two arb_reg (two arb_reg arb_reg));

val arb_instruction_noload_nobranch =
    frequency
        [(1, arb_compare)
        ,(1, arb_nop)
        ,(1, arb_add)]

val arb_program_noload_nobranch = arb_list_of arb_instruction_noload_nobranch;

val arb_program_load = arb_list_of arb_load_indir;

fun arb_program_cond bc_o cmpops arb_prog_left arb_prog_right =
  let
    fun rel_jmp_after bl = Imm (((length bl) + 1) * 4);

    val arb_prog      = arb_prog_left  >>= (fn blockl =>
                        arb_prog_right >>= (fn blockr =>
                           let val blockl_wexit = blockl@[Branch (NONE, rel_jmp_after blockr)] in
                             return ([Compare cmpops,
                                      Branch (bc_o, rel_jmp_after blockl_wexit)]
                                    @blockl_wexit
                                    @blockr)
                           end
                        ));
  in
    arb_prog
  end;

fun arb_program_cond_arb_cmp bc_o arb_prog_left arb_prog_right =
  (two arb_reg arb_reg) >>= (fn cmpops =>
  arb_program_cond bc_o cmpops arb_prog_left arb_prog_right);

fun arb_program_cond_skip bc_o arb_prog =
  let
    fun rel_jmp_after bl = Imm (((length bl) + 1) * 4);
  in
    arb_compare >>= (fn cmp =>
    arb_prog    >>= (fn block =>
      return ([cmp, Branch (bc_o, rel_jmp_after block)]@block)
    ))
  end;


(* ================ Previction generator ================== *)
val arb_program_previct1 =
  let
    val arb_pad = sized (fn n => choose (0, n)) >>=
                  (fn n => resize n arb_program_noload_nobranch);

    val arb_load_instr = arb_load_indir;

    val arb_block_3ld = (List.foldr (op@) []) <$> (
                        sequence [arb_pad, (fn x => [x]) <$> arb_load_instr
                                 ,arb_pad, (fn x => [x]) <$> arb_load_instr
                                 ,arb_pad, (fn x => [x]) <$> arb_load_instr
                                 ,arb_pad]);
  in
    arb_program_cond_arb_cmp (SOME EQ) arb_block_3ld arb_block_3ld
  end;

val arb_program_previct2 =
  let
    val arb_pad = sized (fn n => choose (0, n)) >>=
                  (fn n => resize n arb_program_noload_nobranch);

    val arb_load_instr = arb_load_indir;

    val arb_block_3ld = (List.foldr (op@) []) <$> (
                        sequence [(fn x => [x]) <$> arb_load_instr
                                 ,arb_pad
                                 ,(fn x => [x]) <$> arb_load_instr
                                 ,(fn x => [x]) <$> arb_load_instr
                                 ]);
  in
    arb_program_cond_arb_cmp (SOME EQ) arb_block_3ld arb_block_3ld
  end;

val arb_program_previct3 =
  let
    val arb_pad = sized (fn n => choose (0, n)) >>=
                  (fn n => resize n arb_program_noload_nobranch);

    val arb_load_instr = arb_load_indir;

    val arb_leftright =
      arb_load_instr >>= (fn ld1 =>
      arb_load_instr >>= (fn ld2 =>
      arb_load_instr >>= (fn ld3 =>
        let val arb_block_3ld =
                        (List.foldr (op@) []) <$> (
                        sequence [return [ld1]
                                 ,arb_pad
                                 ,return [ld2]
                                 ,return [ld3]
                                 ]) in
          two arb_block_3ld arb_block_3ld
        end
      )));
  in
    arb_leftright >>= (fn (l,r) => arb_program_cond_arb_cmp (SOME EQ) (return l) (return r))
  end;

val arb_program_previct4 =
  let
    val arb_pad = sized (fn n => choose (0, n)) >>=
                  (fn n => resize n arb_program_noload_nobranch);

    val arb_load_instr = arb_load_indir;

    val arb_leftright =
      arb_load_instr >>= (fn ld1 =>
      arb_load_instr >>= (fn ld2 =>
      arb_load_instr >>= (fn ld3 =>
        let val arb_block_3ld =
                        (List.foldr (op@) []) <$> (
                        sequence [return [ld1]
                                 ,arb_pad
                                 ,return [ld2]
                                 ,return [ld3]
                                 ]) in
          two (return [ld1, ld2, ld3]) arb_block_3ld
        end
      )));
  in
    arb_leftright >>= (fn (l,r) => arb_program_cond_arb_cmp (SOME EQ) (return l) (return r))
  end;

val arb_program_previct5 =
  let
    val arb_pad = sized (fn n => choose (0, n)) >>=
                  (fn n => resize n (arb_list_of arb_nop));

    val arb_load_instr = arb_load_indir;

    val arb_leftright =
      arb_load_instr >>= (fn ld1 =>
      arb_load_instr >>= (fn ld2 =>
      arb_load_instr >>= (fn ld3 =>
        let val arb_block_3ld =
                        (List.foldr (op@) []) <$> (
                        sequence [return [ld1]
                                 ,arb_pad
                                 ,return [ld2]
                                 ,return [ld3]
                                 ]);
        in
          two (return [ld1, ld2, ld3]) arb_block_3ld
        end
      )));
  in
    arb_leftright >>= (fn (l,r) => arb_program_cond_arb_cmp (SOME EQ) (return l) (return r))
  end;


(* =============== xld_br_yld ================= *)
local
    val arb_load_instr = arb_load_indir;
    fun arb_upto_n_lds i =
      sized (fn n => choose (i, n)) >>= (fn n =>
      resize n (arb_list_of arb_load_instr));
in
  val arb_program_xld_br_yld =
    (arb_upto_n_lds 0) >>= (fn block1 =>
    arb_branchcond_cond >>= (fn bc_o =>
    arb_program_cond_skip bc_o (arb_upto_n_lds 1) >>= (fn block2 =>
      return (block1 @ block2)
    )));
  val arb_program_xld_br_yld_mod1 =
    (arb_upto_n_lds 0) >>= (fn block1 =>
    arb_branchcond_cond >>= (fn bc_o =>
    arb_program_cond_arb_cmp bc_o (arb_upto_n_lds 1) (return [Nop]) >>= (fn block2 =>
      return (block1 @ block2)
    )));
end;


(* =============== spectre v1 ================= *)
(*
if (x < len(array1))
  { y = array2[array1[x] * 4096]; }

CMP x, la1
B.HS #end
LDR y, [a1, x]
MUL y, y, 4k
LDR z, [a2, y]
*)
local
  val reg_x   = "x1";
  val reg_la1 = "x2";
  val reg_a1  = "x3";
  val reg_y   = "x4";
  val reg_a2  = "x5";
  val reg_z   = "x6";

  fun to_spe_v1_lsl i =
    Lsl (Reg reg_y, Reg reg_y, Imm i);

  val muls_ref =
    ref (List.map (Option.map (to_spe_v1_lsl)) [
      SOME 6,  (* 64   *)
      SOME 7,  (* 128  *)
      SOME 9,  (* 512  *)
      SOME 12, (* 4096 *)
      SOME 13, (* 8192 *)
      NONE,    (* no mul *)
      SOME 0,  (* 1    *)
      SOME 1   (* 2    *)
    ]);

  fun get_next_spectre_v1_mul () =
    case !muls_ref of
       [] => raise Fail "asm_genLib::get_next_spectre_v1_mul::no more options"
     | (x::xs) => (muls_ref := xs; x);

  fun skip_instrs bc_o bl = Branch (bc_o, Imm ((length(bl) + 1) * 4));
  fun gen_arr_bnds_chck_acc arr_acc_gen =
    arr_acc_gen >>= (fn arr_acc => return (
    [
      Compare (Reg reg_x, Reg reg_la1),
      skip_instrs (SOME HS) arr_acc
    ]@
    arr_acc
    ));
  fun gen_arr_bnds_chck_acc_mod arr_acc_gen other_gen =
    other_gen >>= (fn other =>
    arr_acc_gen >>= (fn arr_acc => return (
    let val arr_acc_wexit = arr_acc@[skip_instrs NONE other]; in
    [
      Compare (Reg reg_x, Reg reg_la1),
      skip_instrs (SOME HS) arr_acc_wexit
    ]@
    arr_acc_wexit@
    other
    end)));

  val gen_arr_acc = arb_nop >>= (fn _ => return (
    [Load (Reg reg_y, Ld2 (reg_x, reg_a1))]@
    (Portable.the_list (get_next_spectre_v1_mul ()))@
    [Load (Reg reg_z, Ld2 (reg_y, reg_a2))]));

  val reg_t1  = "x10";
  val reg_t2  = "x11";
  fun gen_preload with_dep =
    let
      val (reg_t, reg_s) =
        if with_dep then
          (reg_la1, reg_t1)
        else
          (reg_t1, reg_t2);
    in
      return (Load (Reg reg_t, Ld (NONE, reg_s)))
    end;
in
  val arb_program_spectre_v1 =
    gen_arr_bnds_chck_acc gen_arr_acc;
  val arb_program_spectre_v1_mod1 =
    gen_arr_bnds_chck_acc_mod gen_arr_acc (return [Nop]);

  fun arb_program_spectre_v1_mod2_gen w_dep =
    gen_preload w_dep >>= (fn preload_instr =>
    arb_program_spectre_v1_mod1 >>= (fn gadget_instrs =>
      return (preload_instr::gadget_instrs)
    ));
  val arb_program_spectre_v1_mod2     = arb_program_spectre_v1_mod2_gen false;
  val arb_program_spectre_v1_mod2_dep = arb_program_spectre_v1_mod2_gen true;
end;

(* =============== straightline speculation ================= *)
val arb_instruction_nobranch_nocmp =
    frequency
        [(1, arb_load_indir)
       ,(1, arb_nop)
       ,(1, arb_add)]

val arb_program_nobranch_nocmp = arb_list_of arb_instruction_nobranch_nocmp;
      
fun arb_program_straightline_cond arb_prog_left arb_prog_right =
    let
	fun rel_jmp_after bl = Imm (((length bl) + 1) * 4);
	      
	val arb_prog      = arb_prog_left  >>= (fn blockl =>
                              arb_prog_right >>= (fn blockr =>
                              let val blockl_wexit = blockl@[Branch (NONE, rel_jmp_after blockr)] in
                               return (
                                    blockl_wexit
                                    @blockr)
                              end
                        ));
    in
	arb_prog
    end;
    
val arb_program_straightline_branch =
  let
    val arb_pad = sized (fn n => choose (1, n)) >>=
                  (fn n => resize n arb_program_nobranch_nocmp);	
	

    val arb_load_instr = arb_load_indir;

    val arb_leftright =
      arb_load_instr >>= (fn ld1 =>

        let val arb_block_3ld =
                        (List.foldr (op@) []) <$> (
                        sequence [return [ld1]
                                ,arb_pad
                                ,arb_pad
                                 ]) in
          two (arb_pad) arb_block_3ld
        end
      );
  in
    arb_leftright >>= (fn (l,r) => arb_program_straightline_cond (return l) (return r))
  end;

(* ================================ *)
fun prog_gen_a_la_qc_gen do_resize gen n =
    let
      val g = bir_randLib.rand_gen_get ();
      val (p, _) = run_step n g (if do_resize then (resize n gen) else gen);
    in
        pp_program p
    end;

val prog_gen_a_la_qc =
    prog_gen_a_la_qc_gen true;

val prog_gen_a_la_qc_noresize =
    prog_gen_a_la_qc_gen false;


(*=========== Spectre Gen ========+=*)
local
  fun arb_regname_except xs =
    such_that (fn r => not (exists (fn x => x = r) xs)) arb_armv8_regname;

  fun arb_ld_offset reg offset =
    arb_regname_except [reg] >>= (fn source =>
    return (Load (Reg reg, Ld (SOME offset, source))));

  fun arb_ld_offset_src reg offset =
    arb_regname_except [reg] >>= (fn source => 
    return (source, Load (Reg reg, Ld (SOME offset, source))))

  fun arb_ld_reg_src reg =
    arb_regname_except [reg] >>= (fn source => 
    arb_regname_except [reg] >>= (fn reg'   =>
      return (source, Load (Reg reg, Ld (NONE, source^","^reg')))));

  fun arb_ld_offset_selected_source reg  offset =
    arb_regname_except [reg] >>= (fn target =>
    return (target, Load (Reg target, Ld (SOME offset, reg))));

  fun arb_cmp_g reg1 reg2 =
    return (Compare (Reg reg1, Reg reg2));

  fun preamble2 () =
    let
	val offsets = choose(0, 255)
	val regs    = arb_regname_except ["x1", "x0"]
	val zipped  = regs >>= (fn reg1 => offsets 
			   >>= (fn off1 => arb_regname_except [reg1]
                           >>= (fn reg2 => offsets
		           >>= (fn off2 => return ([(reg1, off1), (reg2, off2)], [reg1,reg2])))))


	val ext_src = zipped >>= (fn (p1::p2::_ , [reg1, reg2]) =>
                                         sequence ([arb_ld_reg_src (fst p1), arb_ld_offset_src (fst p2) (snd p2)])
			     >>= (fn h::t::_ => (return ([fst h, fst t], [snd h, snd t], [reg1, reg2]))))
    in
	ext_src >>= (fn (srcs, lds, [reg1, reg2]) =>  (arb_cmp_g (hd srcs) reg2)
                >>= (fn cmpi => return (lds@[cmpi], [reg1, reg2])))
    end;

  fun left_gen reg offset =
      (arb_ld_offset_selected_source reg  offset)
              >>= (fn (_, mop) => return [mop])
      
  val arb_block_l3 = 
      let 
	  val offsets = choose(0, 255)
      in
    preamble2() >>= (fn (prmbl,  [reg1, reg2]) => offsets 
               >>= (fn offset => ((List.foldr (op@) []) <$> 
   	             (sequence [(left_gen reg1 offset)]))
               >>= (fn left => return (prmbl, left))))
      end;

in

  fun arb_program_glue_spectre arb_prog_preamble_left arb_prog_right =
      let
  	  fun rel_jmp_after bl = Imm (((length bl) + 1) * 4);

  	  val arb_prog =arb_prog_preamble_left >>= (fn (prmbl, blockl) =>
                        arb_prog_right >>= (fn blockr =>
            
                           let val blockl_wexit = blockl@[Branch (NONE, rel_jmp_after blockr)] in
                             return (prmbl
  			            @[Branch (SOME EQ, rel_jmp_after blockl_wexit)]
                                    @blockl_wexit
                                    @blockr)
                           end
                        ));
      in
  	  arb_prog
      end;
    
  val arb_program_spectre =
      let
  	  val offsets = choose(0, 255);
  	  val arb_load_instr  =  arb_load_indir;
  	  val arb_store_instr = arb_store_indir;


  	  val arb_block_r = (List.foldr (op@) []) <$> (
              sequence [(fn x => [x]) <$> oneof[arb_load_indir]]);
      in
  	  arb_program_glue_spectre arb_block_l3 arb_block_r
      end
      
end

end
