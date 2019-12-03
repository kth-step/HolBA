structure asm_genLib : asm_genLib =
struct

open qc_genLib;
infix 5 <$>;
infix 5 >>=;

datatype BranchCond = EQ | NE | LT | GT
datatype Operand =
         Imm of int
         | Ld of int option * string
         | Reg of string
datatype ArmInstruction =
         Load of Operand * Operand
         | Branch of BranchCond option * Operand
         | Compare of Operand * Operand
         | Nop
         | Add of Operand * Operand * Operand

(* pp *)
local
fun pp_operand (Imm n) = "#0x" ^ Int.fmt StringCvt.HEX n
  | pp_operand (Ld (NONE, src)) = "[" ^ src ^ "]"
  | pp_operand (Ld (SOME offset, src)) =
    "[" ^ src ^ ", #" ^ Int.toString offset ^ "]"
  | pp_operand (Reg str) = str

fun pp_opcode (Load _)    = "ldr"
  | pp_opcode (Branch _)  = "b"
  | pp_opcode (Compare _) = "cmp"
  | pp_opcode (Nop)       = "nop"
  | pp_opcode (Add _)     = "add"

fun pp_cond bc =
    case bc of
        EQ => "eq"
      | NE => "ne"
      | LT => "lt"
      | GT => "gt"

fun pp_instr instr =
    case instr of
        Load (target,source) =>
        pp_opcode instr ^ " " ^ pp_operand target ^ ", "
        ^ pp_operand source
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
in
fun pp_program is = List.map pp_instr is;
end

(* arb instances *)
local
    val min_addr = 0x1000;
    val max_addr = 0x2000;
in
val arb_addr = choose (min_addr, max_addr);

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

val arb_branchcond =
    let val arb_cond = elements [EQ, NE, LT, GT];
    in
        arb_option arb_cond
    end;

val arb_ld = Ld <$> two (arb_option (elements [4,8,16])) arb_armv8_regname;

val arb_load_indir = Load <$> (two arb_reg arb_ld);
val arb_load_pcimm = Load <$> (two arb_reg arb_imm);
val arb_load = oneof [arb_load_indir, arb_load_pcimm];

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

fun arb_program_cond arb_prog_left arb_prog_right =
  let
    fun rel_jmp_after bl = Imm (((length bl) + 1) * 4);

    val arb_prog      = arb_prog_left  >>= (fn blockl =>
                        arb_prog_right >>= (fn blockr =>
                        arb_compare    >>= (fn cmp    =>
                           let val blockl_wexit = blockl@[Branch (NONE, rel_jmp_after blockr)] in
                             return ([cmp, Branch (SOME EQ, rel_jmp_after blockl_wexit)]
                                    @blockl_wexit
                                    @blockr)
                           end
                        )));
  in
    arb_prog
  end;

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
    arb_program_cond arb_block_3ld arb_block_3ld
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
    arb_program_cond arb_block_3ld arb_block_3ld
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
    arb_leftright >>= (fn (l,r) => arb_program_cond (return l) (return r))
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
    arb_leftright >>= (fn (l,r) => arb_program_cond (return l) (return r))
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
                                 ]) in
          two (return [ld1, ld2, ld3]) arb_block_3ld
        end
      )));
  in
    arb_leftright >>= (fn (l,r) => arb_program_cond (return l) (return r))
  end;
end


(* ================================ *)
fun prog_gen_a_la_qc gen n =
    let
      val g = bir_scamv_helpersLib.rand_gen_get ();
      val (p, _) = run_step n g (resize n gen);
    in
        pp_program p
    end



end
