(* ========================================================================= *)
(* FILE          : bilScript.sml                                             *)
(* DESCRIPTION   : A model of BAP Intermediate Language.                     *)
(*                 Based on Antony's Fox binary words treatment.             *)
(* AUTHOR        : (c) Roberto Metere, KTH - Royal Institute of Technology   *)
(* DATE          : 2015                                                      *)
(* ========================================================================= *)

open HolKernel bossLib Parse;
open wordsTheory;

val _ = new_theory "bil";
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(*  Syntax of BIL, embedding as deep as makes sense                          *)
(* ------------------------------------------------------------------------- *)
Datatype `bil_regtype_t =
  | Bit1
  | Bit8
  | Bit16
  | Bit32
  | Bit64
`;

Datatype `bil_type_t =
    NoType
  | Reg      bil_regtype_t
  | MemByte  bil_regtype_t (* address type *)
  | MemArray bil_regtype_t bil_regtype_t
`;

(* Shallow embedding for bil_int_t, here it's ok, because they are actually bit strings *)
Datatype `bil_int_t =
    Reg1  bool[1]
  | Reg8  bool[8]
  | Reg16 bool[16]
  | Reg32 bool[32]
  | Reg64 bool[64]
`;

Datatype `bil_label_t =
    Label string
  | Address bil_int_t
`;

(* Declaration of variable *)
Datatype `bil_var_t =
    Var string bil_type_t
`;

Datatype `bil_val_t =
    Unknown
  | Int   bil_int_t
  | Mem   bil_regtype_t (bil_int_t -> bil_int_t) (* address type *)
  | Array bil_regtype_t bil_regtype_t (bil_int_t -> bil_int_t)
`;


Datatype `bil_exp_t =
    Const             bil_int_t
  | Den               string (* this is a variable name *)
                      
  | Cast              bil_exp_t bil_regtype_t
  | SignedCast        bil_exp_t bil_regtype_t
  | HighCast          bil_exp_t bil_regtype_t
  | LowCast           bil_exp_t bil_regtype_t
                      
  | ChangeSign        bil_exp_t
  | Not               bil_exp_t
                      
  | Equal             bil_exp_t bil_exp_t
  | NotEqual          bil_exp_t bil_exp_t
  | LessThan          bil_exp_t bil_exp_t
  | SignedLessThan    bil_exp_t bil_exp_t
  | LessOrEqual       bil_exp_t bil_exp_t
  | SignedLessOrEqual bil_exp_t bil_exp_t
                      
  | And               bil_exp_t bil_exp_t
  | Or                bil_exp_t bil_exp_t
  | Xor               bil_exp_t bil_exp_t
                      
  | Plus              bil_exp_t bil_exp_t
  | Minus             bil_exp_t bil_exp_t
  | Mult              bil_exp_t bil_exp_t
  | Div               bil_exp_t bil_exp_t
  | SignedDiv         bil_exp_t bil_exp_t
  | Mod               bil_exp_t bil_exp_t
  | SignedMod         bil_exp_t bil_exp_t
  | LeftShift         bil_exp_t bil_exp_t
  | RightShift        bil_exp_t bil_exp_t
  | SignedRightShift  bil_exp_t bil_exp_t
                      
    (* For some reason if-then-else officially misses in BAP documentation *)
  | IfThenElse        bil_exp_t bil_exp_t bil_exp_t
                      
  | Load              bil_exp_t bil_exp_t bil_exp_t bil_regtype_t
  | Store             bil_exp_t bil_exp_t bil_exp_t bil_exp_t bil_regtype_t
`;

Datatype `bil_stmt_t =
  | Declare bil_var_t
  | Assign  string bil_exp_t
  | Jmp     bil_exp_t
  | CJmp    bil_exp_t bil_exp_t bil_exp_t
  | Halt    bil_exp_t
  | Assert  bil_exp_t
`;

(* As records *)
Datatype `bil_block_t = <| label:bil_label_t ; statements:bil_stmt_t list |>`;

val _ = type_abbrev("program", ``:bil_block_t list``);

(* ------------------------------------------------------------------------- *)
(*  Domain transforming maps : definitions                                   *)
(* ------------------------------------------------------------------------- *)
val b2n_def = Define `b2n t = case t of
  | Reg1  w => w2n w
  | Reg8  w => w2n w
  | Reg16 w => w2n w
  | Reg32 w => w2n w
  | Reg64 w => w2n w
`;

val b2w_def = Define `b2w t = case t of
  | Reg1  w => w2w w
  | Reg8  w => w2w w
  | Reg16 w => w2w w
  | Reg32 w => w2w w
  | Reg64 w => w2w w
`;

val b2n_def = Define `b2n t = case t of
  | Reg1  w => w2n w
  | Reg8  w => w2n w
  | Reg16 w => w2n w
  | Reg32 w => w2n w
  | Reg64 w => w2n w
`;

val b2bool_def = Define `b2bool t = case t of
  | Reg1  w => w ≠ 0w
  | Reg8  w => w ≠ 0w
  | Reg16 w => w ≠ 0w
  | Reg32 w => w ≠ 0w
  | Reg64 w => w ≠ 0w
`;

val w2bs_def = Define `w2bs w (s:num) =
        if (s = 1 ) then Reg1  (w2w w)
  else  if (s = 8 ) then Reg8  (w2w w)
  else  if (s = 16) then Reg16 (w2w w)
  else  if (s = 32) then Reg32 (w2w w)
  else  if (s = 64) then Reg64 (w2w w)
  else  Reg1 (w2w (word_mod w 2w))
`;

val w2b_def = Define `w2b w =
        if (word_len w  = 1 ) then w2bs w 1
  else  if (word_len w <= 8 ) then w2bs w 8
  else  if (word_len w <= 16) then w2bs w 16
  else  if (word_len w <= 32) then w2bs w 32
  else  if (word_len w <= 64) then w2bs w 64
  else  w2bs w 0
`;

val n2bs_def = Define `n2bs n (s:num) =
        if (s = 1 ) ∧ (n < 2**s) then Reg1  (n2w n)
  else  if (s = 8 ) ∧ (n < 2**s) then Reg8  (n2w n)
  else  if (s = 16) ∧ (n < 2**s) then Reg16 (n2w n)
  else  if (s = 32) ∧ (n < 2**s) then Reg32 (n2w n)
  else  if (s = 64) ∧ (n < 2**s) then Reg64 (n2w n)
  else  Reg1 (n2w (n MOD 2))
`;

val n2b_def = Define `n2b n =
        if (n < 2**1 ) then n2bs n 1
  else  if (n < 2**8 ) then n2bs n 8
  else  if (n < 2**16) then n2bs n 16
  else  if (n < 2**32) then n2bs n 32
  else  if (n < 2**64) then n2bs n 64
  else  n2bs n 0
`;

val bool2b_def = Define `bool2b b = if b then Reg1 1w else Reg1 0w`;

val n2b_1_def  = Define `n2b_1  n = n2bs n 1`;
val n2b_8_def  = Define `n2b_8  n = n2bs n 8`;
val n2b_16_def = Define `n2b_16 n = n2bs n 16`;
val n2b_32_def = Define `n2b_32 n = n2bs n 32`;
val n2b_64_def = Define `n2b_64 n = n2bs n 64`;

(* This definition is oriented to give an RX name to registers *)
val r2s_def = Define `r2s = λ(w:bool[5]).STRCAT ("R") (w2s (10:num) HEX w)`;

val _ = add_bare_numeral_form (#"x", SOME "n2b_64");
val _ = add_bare_numeral_form (#"e", SOME "n2b_32");
val _ = add_bare_numeral_form (#"d", SOME "n2b_16");
val _ = add_bare_numeral_form (#"c", SOME "n2b_8");
val _ = add_bare_numeral_form (#"b", SOME "n2b_1");

(* ------------------------------------------------------------------------- *)
(*  Environment (aka variable context)                                       *)
(* ------------------------------------------------------------------------- *)
(* Environment definition *)
val _ = type_abbrev("environment", ``:string -> (bil_type_t # bil_val_t)``);

(* Empty environment *)
val env0_def = Define `env0 = (λx.(NoType, Unknown)):environment`;

(* Error environment. env epsilon != (NoType,Unknown) *)
val is_env_regular_def = Define `is_env_regular env = ((env "") = (NoType, Unknown))`;
val set_env_irregular_def = Define `set_env_irregular env = ("" =+ (NoType, Int 0b)) env`;

(* Get the type of a variable from environment *)
val bil_env_read_type_def = Define `bil_env_read_type var (env:environment) = FST (env var)`;

(* Get value of a variable from environment *)
val bil_env_read_def = Define `bil_env_read var (env:environment) = SND (env var)`;

(* ------------------------------------------------------------------------- *)
(*  Type inference and sizes                                                 *)
(* ------------------------------------------------------------------------- *)

val bil_type_int_inf_def = Define `bil_type_int_inf n = case n of
  | Reg1  _ => Reg Bit1
  | Reg8  _ => Reg Bit8
  | Reg16 _ => Reg Bit16
  | Reg32 _ => Reg Bit32
  | Reg64 _ => Reg Bit64
`;

val bil_type_val_int_inf_def = Define `bil_type_val_int_inf n = case n of
  | Int (Reg1  _) => Reg Bit1
  | Int (Reg8  _) => Reg Bit8
  | Int (Reg16 _) => Reg Bit16
  | Int (Reg32 _) => Reg Bit32
  | Int (Reg64 _) => Reg Bit64
`;

val bil_regtype_int_inf_def = Define `bil_regtype_int_inf n = case n of
  | Reg1  _ => Bit1
  | Reg8  _ => Bit8
  | Reg16 _ => Bit16
  | Reg32 _ => Bit32
  | Reg64 _ => Bit64
`;

(* Number of bytes of a t_reg *)
val bil_sizeof_reg_def = Define `bil_sizeof_reg t = case t of
  | Bit1  => Int 1c (* 1 bit has got size 8 - is it right? *)
  | Bit8  => Int 1c
  | Bit16 => Int 2c
  | Bit32 => Int 4c
  | Bit64 => Int 8c
`;

(* Number of bytes of a tau *)
val bil_sizeof_def = Define `bil_sizeof t = case t of
  | Reg n => bil_sizeof_reg n
  | _     => Int 0c
`;

(* ------------------------------------------------------------------------- *)
(*  Unary operations                                                         *)
(* ------------------------------------------------------------------------- *)
val bil_not_def = Define `bil_not reg = case reg of
  | Reg64 w => Reg64 (word_1comp w)
  | Reg32 w => Reg32 (word_1comp w)
  | Reg16 w => Reg16 (word_1comp w)
  | Reg8  w => Reg8  (word_1comp w)
  | Reg1  w => Reg1  (word_1comp w)
`;

val bil_neg_def = Define `bil_neg reg = case reg of
  | Reg64 w => Reg64 (word_2comp w)
  | Reg32 w => Reg32 (word_2comp w)
  | Reg16 w => Reg16 (word_2comp w)
  | Reg8  w => Reg8  (word_2comp w)
  | Reg1  w => Reg1  (word_2comp w)
`;

val _ = overload_on ("~",               Term`$bil_not`);
val _ = overload_on ("numeric_negate",  Term`$bil_neg`);
val _ = overload_on ("¬",               Term`$bil_neg`);

(* ------------------------------------------------------------------------- *)
(*  Binary operations                                                        *)
(* ------------------------------------------------------------------------- *)
val bil_add_def = Define `bil_add a b = case (a, b) of
  | (Reg64 w1), (Reg64 w2) => Reg64 (w1 + w2)
  | (Reg32 w1), (Reg32 w2) => Reg32 (w1 + w2)
  | (Reg16 w1), (Reg16 w2) => Reg16 (w1 + w2)
  | (Reg8  w1), (Reg8  w2) => Reg8  (w1 + w2)
  | (Reg1  w1), (Reg1  w2) => Reg1  (w1 + w2)
`;

val bil_sub_def = Define `bil_sub a b = case (a, b) of
  | (Reg64 w1), (Reg64 w2) => Reg64 (w1 - w2)
  | (Reg32 w1), (Reg32 w2) => Reg32 (w1 - w2)
  | (Reg16 w1), (Reg16 w2) => Reg16 (w1 - w2)
  | (Reg8  w1), (Reg8  w2) => Reg8  (w1 - w2)
  | (Reg1  w1), (Reg1  w2) => Reg1  (w1 - w2)
`;

val bil_mul_def = Define `bil_mul a b = case (a, b) of
  | (Reg64 w1), (Reg64 w2) => Reg64 (w1 * w2)
  | (Reg32 w1), (Reg32 w2) => Reg32 (w1 * w2)
  | (Reg16 w1), (Reg16 w2) => Reg16 (w1 * w2)
  | (Reg8  w1), (Reg8  w2) => Reg8  (w1 * w2)
  | (Reg1  w1), (Reg1  w2) => Reg1  (w1 * w2)
`;

val bil_div_def = Define `bil_div a b = case (a, b) of
  | (Reg64 w1), (Reg64 w2) => Reg64 (w1 // w2)
  | (Reg32 w1), (Reg32 w2) => Reg32 (w1 // w2)
  | (Reg16 w1), (Reg16 w2) => Reg16 (w1 // w2)
  | (Reg8  w1), (Reg8  w2) => Reg8  (w1 // w2)
  | (Reg1  w1), (Reg1  w2) => Reg1  (w1 // w2)
`;

val bil_sdiv_def = Define `bil_sdiv a b = case (a, b) of
  | (Reg64 w1), (Reg64 w2) => Reg64 (w1 / w2)
  | (Reg32 w1), (Reg32 w2) => Reg32 (w1 / w2)
  | (Reg16 w1), (Reg16 w2) => Reg16 (w1 / w2)
  | (Reg8  w1), (Reg8  w2) => Reg8  (w1 / w2)
  | (Reg1  w1), (Reg1  w2) => Reg1  (w1 / w2)
`;

val bil_mod_def = Define `bil_mod a b = case (a, b) of
  | (Reg64 w1), (Reg64 w2) => Reg64 (word_mod w1 w2)
  | (Reg32 w1), (Reg32 w2) => Reg32 (word_mod w1 w2)
  | (Reg16 w1), (Reg16 w2) => Reg16 (word_mod w1 w2)
  | (Reg8  w1), (Reg8  w2) => Reg8  (word_mod w1 w2)
  | (Reg1  w1), (Reg1  w2) => Reg1  (word_mod w1 w2)
`;

val bil_smod_def = Define `bil_smod a b = case (a, b) of
  | (Reg64 w1), (Reg64 w2) => Reg64 (word_smod w1 w2)
  | (Reg32 w1), (Reg32 w2) => Reg32 (word_smod w1 w2)
  | (Reg16 w1), (Reg16 w2) => Reg16 (word_smod w1 w2)
  | (Reg8  w1), (Reg8  w2) => Reg8  (word_smod w1 w2)
  | (Reg1  w1), (Reg1  w2) => Reg1  (word_smod w1 w2)
`;

val bil_lsl_def = Define `bil_lsl a b = case (a, b) of
  | (Reg64 w1), (Reg64 w2) => Reg64 (word_lsl_bv w1 w2)
  | (Reg32 w1), (Reg32 w2) => Reg32 (word_lsl_bv w1 w2)
  | (Reg16 w1), (Reg16 w2) => Reg16 (word_lsl_bv w1 w2)
  | (Reg8  w1), (Reg8  w2) => Reg8  (word_lsl_bv w1 w2)
  | (Reg1  w1), (Reg1  w2) => Reg1  (word_lsl_bv w1 w2)
`;

val bil_lsr_def = Define `bil_lsr a b = case (a, b) of
  | (Reg64 w1), (Reg64 w2) => Reg64 (word_lsr_bv w1 w2)
  | (Reg32 w1), (Reg32 w2) => Reg32 (word_lsr_bv w1 w2)
  | (Reg16 w1), (Reg16 w2) => Reg16 (word_lsr_bv w1 w2)
  | (Reg8  w1), (Reg8  w2) => Reg8  (word_lsr_bv w1 w2)
  | (Reg1  w1), (Reg1  w2) => Reg1  (word_lsr_bv w1 w2)
`;

val bil_asr_def = Define `bil_asr a b = case (a, b) of
  | (Reg64 w1), (Reg64 w2) => Reg64 (word_asr_bv w1 w2)
  | (Reg32 w1), (Reg32 w2) => Reg32 (word_asr_bv w1 w2)
  | (Reg16 w1), (Reg16 w2) => Reg16 (word_asr_bv w1 w2)
  | (Reg8  w1), (Reg8  w2) => Reg8  (word_asr_bv w1 w2)
  | (Reg1  w1), (Reg1  w2) => Reg1  (word_asr_bv w1 w2)
`;

val bil_and_def = Define `bil_and a b = case (a, b) of
  | (Reg64 w1), (Reg64 w2) => Reg64 (word_and w1 w2)
  | (Reg32 w1), (Reg32 w2) => Reg32 (word_and w1 w2)
  | (Reg16 w1), (Reg16 w2) => Reg16 (word_and w1 w2)
  | (Reg8  w1), (Reg8  w2) => Reg8  (word_and w1 w2)
  | (Reg1  w1), (Reg1  w2) => Reg1  (word_and w1 w2)
`;

val bil_or_def = Define `bil_or a b = case (a, b) of
  | (Reg64 w1), (Reg64 w2) => Reg64 (word_or w1 w2)
  | (Reg32 w1), (Reg32 w2) => Reg32 (word_or w1 w2)
  | (Reg16 w1), (Reg16 w2) => Reg16 (word_or w1 w2)
  | (Reg8  w1), (Reg8  w2) => Reg8  (word_or w1 w2)
  | (Reg1  w1), (Reg1  w2) => Reg1  (word_or w1 w2)
`;

val bil_xor_def = Define `bil_xor a b = case (a, b) of
  | (Reg64 w1), (Reg64 w2) => Reg64 (word_xor w1 w2)
  | (Reg32 w1), (Reg32 w2) => Reg32 (word_xor w1 w2)
  | (Reg16 w1), (Reg16 w2) => Reg16 (word_xor w1 w2)
  | (Reg8  w1), (Reg8  w2) => Reg8  (word_xor w1 w2)
  | (Reg1  w1), (Reg1  w2) => Reg1  (word_xor w1 w2)
`;

val bil_eq_def = Define `bil_eq a b = case (a, b) of
  | (Reg64 w1), (Reg64 w2) => if (w1 = w2) then 1b else 0b
  | (Reg32 w1), (Reg32 w2) => if (w1 = w2) then 1b else 0b
  | (Reg16 w1), (Reg16 w2) => if (w1 = w2) then 1b else 0b
  | (Reg8  w1), (Reg8  w2) => if (w1 = w2) then 1b else 0b
  | (Reg1  w1), (Reg1  w2) => if (w1 = w2) then 1b else 0b
  | _, _ => 0b
`;

val bil_neq_def = Define `bil_neq a b = case (a, b) of
  | (Reg64 w1), (Reg64 w2) => if (w1 = w2) then 0b else 1b
  | (Reg32 w1), (Reg32 w2) => if (w1 = w2) then 0b else 1b
  | (Reg16 w1), (Reg16 w2) => if (w1 = w2) then 0b else 1b
  | (Reg8  w1), (Reg8  w2) => if (w1 = w2) then 0b else 1b
  | (Reg1  w1), (Reg1  w2) => if (w1 = w2) then 0b else 1b
  | _, _ => 0b
`;

(* 

signed less than:

> val it = |- 127w < 0w ⇔ F: thm
> val it = |- 128w < 0w ⇔ T: thm

*)
val bil_lt_def = Define `bil_lt a b = case (a, b) of
  | (Reg64 w1), (Reg64 w2) => if (word_lt w1 w2) then 1b else 0b
  | (Reg32 w1), (Reg32 w2) => if (word_lt w1 w2) then 1b else 0b
  | (Reg16 w1), (Reg16 w2) => if (word_lt w1 w2) then 1b else 0b
  | (Reg8  w1), (Reg8  w2) => if (word_lt w1 w2) then 1b else 0b
  | (Reg1  w1), (Reg1  w2) => if (word_lt w1 w2) then 1b else 0b
  | _, _ => 0b
`;

val bil_le_def = Define `bil_le a b = case (a, b) of
  | (Reg64 w1), (Reg64 w2) => if (word_le w1 w2) then 1b else 0b
  | (Reg32 w1), (Reg32 w2) => if (word_le w1 w2) then 1b else 0b
  | (Reg16 w1), (Reg16 w2) => if (word_le w1 w2) then 1b else 0b
  | (Reg8  w1), (Reg8  w2) => if (word_le w1 w2) then 1b else 0b
  | (Reg1  w1), (Reg1  w2) => if (word_le w1 w2) then 1b else 0b
  | _, _ => 0b
`;

val bil_ult_def = Define `bil_ult a b = case (a, b) of
  | (Reg64 w1), (Reg64 w2) => if (word_lo w1 w2) then 1b else 0b
  | (Reg32 w1), (Reg32 w2) => if (word_lo w1 w2) then 1b else 0b
  | (Reg16 w1), (Reg16 w2) => if (word_lo w1 w2) then 1b else 0b
  | (Reg8  w1), (Reg8  w2) => if (word_lo w1 w2) then 1b else 0b
  | (Reg1  w1), (Reg1  w2) => if (word_lo w1 w2) then 1b else 0b
  | _, _ => 0b
`;

val bil_ule_def = Define `bil_ule a b = case (a, b) of
  | (Reg64 w1), (Reg64 w2) => if (word_ls w1 w2) then 1b else 0b
  | (Reg32 w1), (Reg32 w2) => if (word_ls w1 w2) then 1b else 0b
  | (Reg16 w1), (Reg16 w2) => if (word_ls w1 w2) then 1b else 0b
  | (Reg8  w1), (Reg8  w2) => if (word_ls w1 w2) then 1b else 0b
  | (Reg1  w1), (Reg1  w2) => if (word_ls w1 w2) then 1b else 0b
  | _, _ => 0b
`;

val _ = add_infix("<<",  680, HOLgrammars.LEFT);
val _ = add_infix(">>",  680, HOLgrammars.LEFT);
val _ = add_infix(">>>", 680, HOLgrammars.LEFT);

val _ = overload_on ("+",              Term`$bil_add`);
val _ = overload_on ("-",              Term`$bil_sub`);
val _ = overload_on ("*",              Term`$bil_mul`);
val _ = overload_on ("//",             Term`$bil_div`);
val _ = overload_on ("/",              Term`$bil_sdiv`);
val _ = overload_on ("<<",             Term`$bil_lsl`);
val _ = overload_on (">>>",            Term`$bil_lsr`);
val _ = overload_on (">>",             Term`$bil_asr`);
val _ = overload_on ("<",              Term`$bil_lt`);
val _ = overload_on ("<=",             Term`$bil_le`);

val _ = set_fixity "//" (Infixl 600);
val _ = set_fixity "/"  (Infixl 600);

(* ------------------------------------------------------------------------- *)
(*  Casts                                                                    *)
(* ------------------------------------------------------------------------- *)
val bil_cast_def = Define `bil_cast a t = case (a, t) of
  (* Not very casts *)
  | (Reg1  w), Bit1  => Reg1  w
  | (Reg8  w), Bit8  => Reg8  w
  | (Reg16 w), Bit16 => Reg16 w
  | (Reg32 w), Bit32 => Reg32 w
  | (Reg64 w), Bit64 => Reg64 w
  
  (* Casts *)
  | (Reg1  w), Bit8  => Reg8  ((0w:bool[7])  @@ w)
  | (Reg1  w), Bit16 => Reg16 ((0w:bool[15]) @@ w)
  | (Reg1  w), Bit32 => Reg32 ((0w:bool[31]) @@ w)
  | (Reg1  w), Bit64 => Reg64 ((0w:bool[63]) @@ w)
  | (Reg8  w), Bit16 => Reg16 ((0w:bool[8])  @@ w)
  | (Reg8  w), Bit32 => Reg32 ((0w:bool[24]) @@ w)
  | (Reg8  w), Bit64 => Reg64 ((0w:bool[56]) @@ w)
  | (Reg16 w), Bit32 => Reg32 ((0w:bool[16]) @@ w)
  | (Reg16 w), Bit64 => Reg64 ((0w:bool[48]) @@ w)
  | (Reg32 w), Bit64 => Reg64 ((0w:bool[32]) @@ w)
`;

val bil_scast_def = Define `bil_scast a t = case (a, t) of
  (* Not very casts *)
  | (Reg1  w), Bit1  => Reg1  w
  | (Reg8  w), Bit8  => Reg8  w
  | (Reg16 w), Bit16 => Reg16 w
  | (Reg32 w), Bit32 => Reg32 w
  | (Reg64 w), Bit64 => Reg64 w
  
  (* Casts *)
  | (Reg1  w), Bit8  => Reg8  ((if (word_msb w) then (0x7Fw:bool[7]) else  (0w:bool[7]) ) @@ w)
  | (Reg1  w), Bit16 => Reg16 ((if (word_msb w) then (0x7FFFw:bool[15]) else  (0w:bool[15]) ) @@ w)
  | (Reg1  w), Bit32 => Reg32 ((if (word_msb w) then (0x7FFFFFFFw:bool[31]) else  (0w:bool[31]) ) @@ w)
  | (Reg1  w), Bit64 => Reg64 ((if (word_msb w) then (0x7FFFFFFFFFFFFFFFw:bool[63]) else  (0w:bool[63]) ) @@ w)
  | (Reg8  w), Bit16 => Reg16 ((if (word_msb w) then (0xFFw:bool[8]) else  (0w:bool[8]) ) @@ w)
  | (Reg8  w), Bit32 => Reg32 ((if (word_msb w) then (0xFFFFFFw:bool[24]) else (0w:bool[24])) @@ w)
  | (Reg8  w), Bit64 => Reg64 ((if (word_msb w) then (0xFFFFFFFFFFFFFFw:bool[56]) else (0w:bool[56])) @@ w)
  | (Reg16 w), Bit32 => Reg32 ((if (word_msb w) then (0xFFFFw:bool[16]) else (0w:bool[16])) @@ w)
  | (Reg16 w), Bit64 => Reg64 ((if (word_msb w) then (0xFFFFFFFFFFFFw:bool[48]) else (0w:bool[48])) @@ w)
  | (Reg32 w), Bit64 => Reg64 ((if (word_msb w) then (0xFFFFFFFFw:bool[32]) else (0w:bool[32])) @@ w)
`;

val bil_hcast_def = Define `bil_hcast a t = case (a, t) of
  (* Not very casts *)
  | (Reg1  w), Bit1  => Reg1  w
  | (Reg8  w), Bit8  => Reg8  w
  | (Reg16 w), Bit16 => Reg16 w
  | (Reg32 w), Bit32 => Reg32 w
  | (Reg64 w), Bit64 => Reg64 w
  
  (* Casts *)
  | (Reg64 w), Bit32 => Reg32 (word_extract 63 32 w)
  | (Reg64 w), Bit16 => Reg16 (word_extract 63 48 w)
  | (Reg64 w), Bit8  => Reg8  (word_extract 63 56 w)
  | (Reg64 w), Bit1  => Reg1  (word_extract 63 63 w)
  | (Reg32 w), Bit16 => Reg16 (word_extract 31 16 w)
  | (Reg32 w), Bit8  => Reg8  (word_extract 31 24 w)
  | (Reg32 w), Bit1  => Reg1  (word_extract 31 31 w)
  | (Reg16 w), Bit8  => Reg8  (word_extract 15 8  w)
  | (Reg16 w), Bit1  => Reg1  (word_extract 15 15 w)
  | (Reg8  w), Bit1  => Reg1  (word_extract 7  7  w)
`;

val bil_lcast_def = Define `bil_lcast a t = case (a, t) of
  (* Not very casts *)
  | (Reg1  w), Bit1  => Reg1  w
  | (Reg8  w), Bit8  => Reg8  w
  | (Reg16 w), Bit16 => Reg16 w
  | (Reg32 w), Bit32 => Reg32 w
  | (Reg64 w), Bit64 => Reg64 w
  
  (* Downcasts *)
  | (Reg64 w), Bit32 => Reg32 (word_extract 31 0 w)
  | (Reg64 w), Bit16 => Reg16 (word_extract 15 0 w)
  | (Reg64 w), Bit8  => Reg8  (word_extract 7  0 w)
  | (Reg64 w), Bit1  => Reg1  (word_extract 0  0 w)
  | (Reg32 w), Bit16 => Reg16 (word_extract 15 0 w)
  | (Reg32 w), Bit8  => Reg8  (word_extract 7  0 w)
  | (Reg32 w), Bit1  => Reg1  (word_extract 0  0 w)
  | (Reg16 w), Bit8  => Reg8  (word_extract 7  0 w)
  | (Reg16 w), Bit1  => Reg1  (word_extract 0  0 w)
  | (Reg8  w), Bit1  => Reg1  (word_extract 0  0 w)
`;

(* ------------------------------------------------------------------------- *)
(*  Semantics of expressions                                                 *)
(* ------------------------------------------------------------------------- *)
val bil_eval_exp_def = Define `bil_eval_exp exp (env:environment) = case exp of
  | Const n => Int n
  | Den v => bil_env_read v env
  
  | Cast e t => (
      case bil_eval_exp e env of
          Int v => Int (bil_cast v t)
        | _     => Unknown
      )
  | SignedCast e t => (
      case bil_eval_exp e env of
          Int v => Int (bil_scast v t)
        | _     => Unknown
      )
  | HighCast e t => (
      case bil_eval_exp e env of
          Int v => Int (bil_hcast v t)
        | _     => Unknown
      )
  | LowCast e t => (
      case bil_eval_exp e env of
          Int v => Int (bil_lcast v t)
        | _     => Unknown
      )
  
  | ChangeSign e => (
      case bil_eval_exp e env of
          Int v => Int (numeric_negate v)
        | _     => Unknown
      )
  | Not e => (
      case bil_eval_exp e env of
          Int v => Int (bil_not v)
        | _     => Unknown
      )
  
  | Equal e1 e2 => (
      case (bil_eval_exp e1 env, bil_eval_exp e2 env) of
          (Int v1, Int v2) => Int (bil_eq v1 v2)
        | _     => Unknown
      )
  | NotEqual e1 e2 => (
      case (bil_eval_exp e1 env, bil_eval_exp e2 env) of
          (Int v1, Int v2) => Int (bil_neq v1 v2)
        | _     => Unknown
      )
  | LessThan e1 e2 => (
      case (bil_eval_exp e1 env, bil_eval_exp e2 env) of
          (Int v1, Int v2) => Int (bil_ult v1 v2)
        | _     => Unknown
      )
  | SignedLessThan e1 e2 => (
      case (bil_eval_exp e1 env, bil_eval_exp e2 env) of
          (Int v1, Int v2) => Int (bil_lt v1 v2)
        | _     => Unknown
      )
  | LessOrEqual e1 e2 => (
      case (bil_eval_exp e1 env, bil_eval_exp e2 env) of
          (Int v1, Int v2) => Int (bil_ule v1 v2)
        | _     => Unknown
      )
  | SignedLessOrEqual e1 e2 => (
      case (bil_eval_exp e1 env, bil_eval_exp e2 env) of
          (Int v1, Int v2) => Int (bil_le v1 v2)
        | _     => Unknown
      )
  
  | And e1 e2 => (
      case (bil_eval_exp e1 env, bil_eval_exp e2 env) of
          (Int v1, Int v2) => Int (bil_and v1 v2)
        | _     => Unknown
      )
  | Or e1 e2 => (
      case (bil_eval_exp e1 env, bil_eval_exp e2 env) of
          (Int v1, Int v2) => Int (bil_or v1 v2)
        | _     => Unknown
      )
  | Xor e1 e2 => (
      case (bil_eval_exp e1 env, bil_eval_exp e2 env) of
          (Int v1, Int v2) => Int (bil_xor v1 v2)
        | _     => Unknown
      )
  
  | Plus e1 e2 => (
      case (bil_eval_exp e1 env, bil_eval_exp e2 env) of
          (Int v1, Int v2) => Int (bil_add v1 v2)
        | _     => Unknown
      )
  | Minus e1 e2 => (
      case (bil_eval_exp e1 env, bil_eval_exp e2 env) of
          (Int v1, Int v2) => Int (bil_sub v1 v2)
        | _     => Unknown
      )
  | Mult e1 e2 => (
      case (bil_eval_exp e1 env, bil_eval_exp e2 env) of
          (Int v1, Int v2) => Int (bil_mul v1 v2)
        | _     => Unknown
      )
  | Div e1 e2 => (
      case (bil_eval_exp e1 env, bil_eval_exp e2 env) of
          (Int v1, Int v2) => Int (bil_div v1 v2)
        | _     => Unknown
      )
  | SignedDiv e1 e2 => (
      case (bil_eval_exp e1 env, bil_eval_exp e2 env) of
          (Int v1, Int v2) => Int (bil_sdiv v1 v2)
        | _     => Unknown
      )
  | Mod e1 e2 => (
      case (bil_eval_exp e1 env, bil_eval_exp e2 env) of
          (Int v1, Int v2) => Int (bil_mod v1 v2)
        | _     => Unknown
      )
  | SignedMod e1 e2 => (
      case (bil_eval_exp e1 env, bil_eval_exp e2 env) of
          (Int v1, Int v2) => Int (bil_smod v1 v2)
        | _     => Unknown
      )
  | LeftShift e1 e2 => (
      case (bil_eval_exp e1 env, bil_eval_exp e2 env) of
          (Int v1, Int v2) => Int (bil_lsl v1 v2)
        | _     => Unknown
      )
  | RightShift e1 e2 => (
      case (bil_eval_exp e1 env, bil_eval_exp e2 env) of
          (Int v1, Int v2) => Int (bil_lsr v1 v2)
        | _     => Unknown
      )
  | SignedRightShift e1 e2 => (
      case (bil_eval_exp e1 env, bil_eval_exp e2 env) of
          (Int v1, Int v2) => Int (bil_asr v1 v2)
        | _     => Unknown
      )
      
  | IfThenElse c et ee => (
      case (bil_eval_exp c env) of
          Int b => if (b = 1b)
                      then bil_eval_exp et env
                      else bil_eval_exp ee env
        | _        => Unknown
      )
      
  (* Memory *)
  | Load  e1 e2 e3 t => (
      let n = bil_sizeof_reg t in
      if ~(n = Int 0c)
      then
        let mem = bil_eval_exp e1 env in
        let address = bil_eval_exp e2 env in
        let bigendian = bil_eval_exp e3 env in
        case (mem, address, bigendian) of
            (Mem ta mmap, Int a, Int be) => (
              if ((bil_regtype_int_inf a) = ta)
              then
                case t of
                    Bit1   => Int (if (mmap a) = 0c then 0b else 1b)
                  | Bit8   => Int (mmap a)
                  | Bit16  => if be = 0b
                              then Int (
                                bil_or
                                  ((bil_cast (mmap (a + (bil_cast 1c ta))) Bit16) << 8d)
                                  (bil_cast (mmap a) Bit16)
                                )
                              else Int (
                                bil_or
                                  ((bil_cast (mmap a) Bit16) << 8d)
                                  (bil_cast (mmap (a + (bil_cast 1c ta))) Bit16)
                                )
                  | Bit32  => if be = 0b
                              then Int (
                                bil_or
                                  (bil_or
                                    ((bil_cast (mmap (a + (bil_cast 3c ta))) Bit32) << 24e)
                                    ((bil_cast (mmap (a + (bil_cast 2c ta))) Bit32) << 16e)
                                  )
                                  (bil_or
                                    ((bil_cast (mmap (a + (bil_cast 1c ta))) Bit32) << 8e)
                                    (bil_cast (mmap a) Bit32)
                                  )
                                )
                              else Int (
                                bil_or
                                  (bil_or
                                    ((bil_cast (mmap a) Bit32) << 24e)
                                    ((bil_cast (mmap (a + (bil_cast 1c ta))) Bit32) << 16e)
                                  )
                                  (bil_or
                                    ((bil_cast (mmap (a + (bil_cast 2c ta))) Bit32) << 8e)
                                    (bil_cast (mmap (a + (bil_cast 3c ta))) Bit32)
                                  )
                                )
                  | Bit64  => if be = 0b
                              then Int (
                                bil_or
                                  (bil_or
                                    (bil_or
                                      ((bil_cast (mmap (a + (bil_cast 7c ta))) Bit64) << 56x)
                                      ((bil_cast (mmap (a + (bil_cast 6c ta))) Bit64) << 48x)
                                    )
                                    (bil_or
                                      ((bil_cast (mmap (a + (bil_cast 5c ta))) Bit64) << 40x)
                                      ((bil_cast (mmap (a + (bil_cast 4c ta))) Bit64) << 32x)
                                    )
                                  )
                                  (bil_or
                                    (bil_or
                                      ((bil_cast (mmap (a + (bil_cast 3c ta))) Bit64) << 24x)
                                      ((bil_cast (mmap (a + (bil_cast 2c ta))) Bit64) << 16x)
                                    )
                                    (bil_or
                                      ((bil_cast (mmap (a + (bil_cast 1c ta))) Bit64) << 8x)
                                      (bil_cast (mmap a) Bit64)
                                    )
                                  )
                                )
                              else Int (
                                bil_or
                                  (bil_or
                                    (bil_or
                                      ((bil_cast (mmap a) Bit64) << 56x)
                                      ((bil_cast (mmap (a + (bil_cast 1c ta))) Bit64) << 48x)
                                    )
                                    (bil_or
                                      ((bil_cast (mmap (a + (bil_cast 2c ta))) Bit64) << 40x)
                                      ((bil_cast (mmap (a + (bil_cast 3c ta))) Bit64) << 32x)
                                    )
                                  )
                                  (bil_or
                                    (bil_or
                                      ((bil_cast (mmap (a + (bil_cast 4c ta))) Bit64) << 24x)
                                      ((bil_cast (mmap (a + (bil_cast 5c ta))) Bit64) << 16x)
                                    )
                                    (bil_or
                                      ((bil_cast (mmap (a + (bil_cast 6c ta))) Bit64) << 8x)
                                      (bil_cast (mmap (a + (bil_cast 7c ta))) Bit64)
                                    )
                                  )
                                )
                
              (* Can't use addresses of different types *)
              else Unknown
              )
          | (Array ta tv mmap, Int a, _) => (
              if ((bil_regtype_int_inf a) = ta)
              then
                  Int (mmap a)
                
              (* Can't use addresses of different types *)
              else Unknown
              )
          | _                                 => Unknown
      else
        (* Can't read less than 1 byte from memory *)
        Unknown
      )
  | Store e1 e2 e3 e4 t => (
      let n = bil_sizeof_reg t in
      if ~(n = Int 0c)
      then
        let mem = bil_eval_exp e1 env in
        let address = bil_eval_exp e2 env in
        let newval = bil_eval_exp e3 env in
        let bigendian = bil_eval_exp e4 env in
        case (mem, address, newval, bigendian) of
            (Mem ta mmap, Int a, Int v, Int be) => (
              if ((bil_regtype_int_inf a) = ta) ∧ ((bil_regtype_int_inf v) = t)
              then
                case t of
                    Bit1   => Mem ta ((a =+ (if v = 0b then 0c else 1c)) mmap)
                  | Bit8   => Mem ta ((a =+ v) mmap)
                  | Bit16  => if be = 0b
                              then Mem ta ((a                     =+ (bil_lcast v Bit8)) (
                                          ((a + (bil_cast 1c ta)) =+ (bil_hcast v Bit8))
                                   mmap))
                              else Mem ta ((a                     =+ (bil_hcast v Bit8)) (
                                          ((a + (bil_cast 1c ta)) =+ (bil_lcast v Bit8))
                                   mmap))
                  | Bit32  => if be = 0b
                              then Mem ta ((a                     =+ (bil_lcast v Bit8)) (
                                          ((a + (bil_cast 1c ta)) =+ (bil_hcast (bil_lcast v Bit16) Bit8)) (
                                          ((a + (bil_cast 2c ta)) =+ (bil_lcast (bil_hcast v Bit16) Bit8)) (
                                          ((a + (bil_cast 3c ta)) =+ (bil_hcast v Bit8))
                                   mmap))))
                              else Mem ta ((a                     =+ (bil_hcast v Bit8)) (
                                          ((a + (bil_cast 1c ta)) =+ (bil_lcast (bil_hcast v Bit16) Bit8)) (
                                          ((a + (bil_cast 2c ta)) =+ (bil_hcast (bil_lcast v Bit16) Bit8)) (
                                          ((a + (bil_cast 3c ta)) =+ (bil_lcast v Bit8))
                                   mmap))))
                  | Bit64  => if be = 0b
                              then Mem ta ((a                     =+ (bil_lcast v Bit8)) (
                                          ((a + (bil_cast 1c ta)) =+ (bil_hcast (bil_lcast v Bit16) Bit8)) (
                                          ((a + (bil_cast 2c ta)) =+ (bil_lcast (bil_hcast (bil_lcast v Bit32) Bit16) Bit8)) (
                                          ((a + (bil_cast 3c ta)) =+ (bil_hcast (bil_lcast v Bit32) Bit8)) (
                                          ((a + (bil_cast 4c ta)) =+ (bil_lcast (bil_hcast v Bit32) Bit8)) (
                                          ((a + (bil_cast 5c ta)) =+ (bil_hcast (bil_lcast (bil_hcast v Bit32) Bit16) Bit8)) (
                                          ((a + (bil_cast 6c ta)) =+ (bil_lcast (bil_hcast v Bit16) Bit8)) (
                                          ((a + (bil_cast 7c ta)) =+ (bil_hcast v Bit8))
                                   mmap))))))))
                              else Mem ta ((a                     =+ (bil_hcast v Bit8)) (
                                          ((a + (bil_cast 1c ta)) =+ (bil_lcast (bil_hcast v Bit16) Bit8)) (
                                          ((a + (bil_cast 2c ta)) =+ (bil_hcast (bil_lcast (bil_hcast v Bit32) Bit16) Bit8)) (
                                          ((a + (bil_cast 3c ta)) =+ (bil_lcast (bil_hcast v Bit32) Bit8)) (
                                          ((a + (bil_cast 4c ta)) =+ (bil_hcast (bil_lcast v Bit32) Bit8)) (
                                          ((a + (bil_cast 5c ta)) =+ (bil_lcast (bil_hcast (bil_lcast v Bit32) Bit16) Bit8)) (
                                          ((a + (bil_cast 6c ta)) =+ (bil_hcast (bil_lcast v Bit16) Bit8)) (
                                          ((a + (bil_cast 7c ta)) =+ (bil_lcast v Bit8))
                                   mmap))))))))
                
              (* Can't use addresses of different types *)
              else Unknown
              )
          | (Array ta tv mmap, Int a, Int v, _) => (
              if ((bil_regtype_int_inf a) = ta) ∧ ((bil_regtype_int_inf v) = tv)
              then
                  Array ta tv ((a =+ v) mmap)
                
              (* Can't use addresses of different types *)
              else Unknown
              )
          | _                                 => Unknown
      else
        (* Can't store less than 1 byte from memory *)
        Unknown
      )
  
  (* out of BIL semantic *)
  | _ => Unknown
`;

(* ------------------------------------------------------------------------- *)
(*  Semantics of statements                                                  *)
(* ------------------------------------------------------------------------- *)

(* Execution of Jmp, CJmp, Halt, Assert doesn't change environment *)
val bil_exec_stmt_def = Define `bil_exec_stmt stmt env = case stmt of
  | Declare (Var s t) => (
      case env s, t of
          (NoType, Unknown), Reg _          => (s =+ (t, Unknown)) env
        | (NoType, Unknown), MemByte ta     => (s =+ (t, Mem ta ((λx.(Reg8 0w)):bil_int_t -> bil_int_t))) env
        | (NoType, Unknown), MemArray ta tv => (
            case tv of
                Bit1  => (s =+ (t, Array ta tv ((λx.(Reg1  0w)):bil_int_t -> bil_int_t))) env
              | Bit8  => (s =+ (t, Array ta tv ((λx.(Reg8  0w)):bil_int_t -> bil_int_t))) env
              | Bit16 => (s =+ (t, Array ta tv ((λx.(Reg16 0w)):bil_int_t -> bil_int_t))) env
              | Bit32 => (s =+ (t, Array ta tv ((λx.(Reg32 0w)):bil_int_t -> bil_int_t))) env
              | Bit64 => (s =+ (t, Array ta tv ((λx.(Reg64 0w)):bil_int_t -> bil_int_t))) env
            )
        | _ => env
      )
  | Assign v e => (
      case env v, bil_eval_exp e env of
          (t, _), Int nexp                        => let texp = bil_type_int_inf nexp in
                                                    if (t = texp)
                                                      then (v =+ (t, Int nexp)) env
                                                      else set_env_irregular env
        | (MemByte t, _), Mem ta mmap             => if (t = ta)
                                                      then (v =+ (MemByte t, Mem ta mmap)) env
                                                      else set_env_irregular env
        | (MemArray ta tv, _), Array tta ttv mmap => if (ta = tta) ∧ (tv = ttv)
                                                      then (v =+ (MemArray ta tv, Array tta ttv mmap)) env
                                                      else set_env_irregular env
        (* Kind of redeclarations... they seems to be out of BIL semantics *)
(*         | (t, _), Unknown                        => (v =+ (t, Unknown)) env *)
(*         | (MemByte t, _), Unknown                => (v =+ (MemByte t, Unknown)) env *)
(*         | (MemArray ta tv, _), Unknown           => (v =+ (MemArray ta tv, Unknown)) env *)
        
        (* Other things don't change the environment, but are wrong in some way *)
        | _, _                                   => set_env_irregular env
      )
  | _ => env
`;


val debug_concat_def = Define `debug_concat l = CONCAT l`;


(* Statement to string (useful for debugging purposes) *)
val bil_stmt_to_string_def = Define `bil_stmt_to_string stmt = case stmt of
  | Declare (Var s t) => debug_concat ["Declaration of "; s]
  | Assign v e => debug_concat ["Assignment of "; v]
  | Jmp _ => "Jump"
  | CJmp _ _ _ => "Conditional Jump"
  | Halt _ => "Halt"
  | Assert _ => "Assert"
  | _ => "-- unsupported statement"
`;

(* Define PC record *)
Datatype `programcounter = <| label:bil_label_t; index:num |>`;

val bil_get_program_block_info_by_label_def = Define `bil_get_program_block_info_by_label p l =
  INDEX_FIND 0 (\(x:bil_block_t). x.label = l) p
`;

val bil_nextblock_def = Define `bil_nextblock (p:program) (n, (bl:bil_block_t)) = if (n < LENGTH p - 1) 
  then SOME (n + 1, EL (n + 1) p)
  else NONE
`;

val bil_pcnext_def = Define `
  (bil_pcnext p NONE = NONE) ∧
  (bil_pcnext p (SOME pc) = case bil_get_program_block_info_by_label p (pc.label) of
        SOME (n, bl) => if (pc.index < LENGTH bl.statements - 1)
          then SOME <| label := pc.label ; index := (pc.index + 1) |>
          else (
            case bil_nextblock p (n, bl) of
              | NONE => NONE
              | SOME (_, nextblock) => if (LENGTH nextblock.statements = 0)
                  then SOME <| label := Label "" ; index := 0 |>
                  else SOME <| label := nextblock.label ; index := 0 |>
            )
      | _ => NONE
  )
`;

Datatype `stepstate = <|
  pco:programcounter option ;
  pi:program ;
  environ:environment ;
  termcode:bil_val_t ;
  debug:string list;
  execs:num
|>`;

val bil_exec_step_def = Define `bil_exec_step state = case state.pco of
  | NONE => state
  | SOME (pc) => if pc.label = (Label "")
      then state with <| pco := (bil_pcnext state.pi state.pco) ; debug := "Empty block not allowed"::state.debug ; execs := state.execs + 1 |>
      else case bil_get_program_block_info_by_label state.pi pc.label of
        | NONE => state with <| pco := NONE ; debug := "Wrong program counter"::state.debug ; execs := state.execs + 1 |>
        | SOME (n, bl) => if (pc.index >= LENGTH bl.statements) \/ ~(state.termcode = Unknown)
            then state with <| pco := NONE ; debug := "Program terminated"::state.debug ; execs := state.execs + 1 |>
            else
              let stmt = EL pc.index bl.statements in
              let newenviron = bil_exec_stmt stmt state.environ in
              if ~(is_env_regular newenviron)
              then
                state with <| pco := NONE ; debug := (debug_concat ["Irregular environment after "; bil_stmt_to_string stmt])::state.debug ; execs := state.execs + 1 |>
              else
                case stmt of
                  | Jmp e        => (case bil_eval_exp e newenviron of
                        (Int addr) =>
                         state with <| pco := SOME (<| label := (Address addr) ; index := 0 |>) ; execs := state.execs + 1 |>
                         | _ =>  state with <| pco := NONE ; debug := (debug_concat ["Wrong exp in jmp "; bil_stmt_to_string stmt])::state.debug ; execs := state.execs + 1 |>)
                  | CJmp e e1 e2 => if (bil_eval_exp e newenviron) = Int 1b
                         then (case bil_eval_exp e1 newenviron of
                            (Int addr) =>
                              state with <| pco := SOME (<| label := (Address addr) ; index := 0 |>) ; execs := state.execs + 1 |>
                             | _ =>  state with <| pco := NONE ; debug := (debug_concat ["Wrong exp in jmp "; bil_stmt_to_string stmt])::state.debug ; execs := state.execs + 1 |>)
                         else (case bil_eval_exp e2 newenviron of
                            (Int addr) =>
                              state with <| pco := SOME (<| label := (Address addr) ; index := 0 |>) ; execs := state.execs + 1 |>
                             | _ =>  state with <| pco := NONE ; debug := (debug_concat ["Wrong exp in jmp "; bil_stmt_to_string stmt])::state.debug ; execs := state.execs + 1 |>)
                  | Declare _    => state with <| pco := (bil_pcnext state.pi state.pco) ; environ := newenviron ; execs := state.execs + 1 |>
                  | Assign _ _   => state with <| pco := (bil_pcnext state.pi state.pco) ; environ := newenviron ; execs := state.execs + 1 |>
                  | Assert e     => if (bil_eval_exp e newenviron) = Int 1b
                                    then state with <| pco := (bil_pcnext state.pi state.pco) ; execs := state.execs + 1 |>
                                    else state with <| pco := NONE ; termcode := Unknown ; debug := "Assertion failed"::state.debug ; execs := state.execs + 1 |>
                  | Halt e       => state with <| pco := NONE ; termcode := (bil_eval_exp e newenviron) ; debug := "Program halted"::state.debug ; execs := state.execs + 1 |>
                  | _            => state with <| pco := NONE ; environ := newenviron ; termcode := Unknown ; debug := "Unknown statement"::state.debug ; execs := state.execs + 1 |>
`;

(* Multiple execution of step *)
val bil_exec_step_n_def = Define `bil_exec_step_n state (n:num) =
  if state.pco = NONE then state else
  if (n = 0)
    then state
    else bil_exec_step_n (bil_exec_step state) (n - 1)
`;

(* Statements' counting and irregular program *)
val bil_block_stmts_count_def = Define `bil_block_stmts_count bl = LENGTH bl.statements`;

val bil_program_lbl_unique_def = Define`bil_program_lbl_unique (p:program) = ALL_DISTINCT (MAP (λbl.(bl.label)) p)`;

val bil_program_no_empty_blocks_def = Define`bil_program_no_empty_blocks p = (FIND ($= 0) (FILTER (λl.l = 0) (MAP bil_block_stmts_count p)) = NONE)`;

val bil_program_irregular_def = Define `bil_program_irregular p = ~(bil_program_lbl_unique p ∧ bil_program_no_empty_blocks p)`;

val bil_pcinit_def = Define `bil_pcinit (p:program) = let bl = EL 0 p in <| label := bl.label ; index := 0 |>`;

val bil_state_init_def = Define `bil_state_init (p:program) = <|
    pco      := SOME (bil_pcinit p)
  ; pi       := p
  ; environ  := (λx.(NoType, Unknown)):environment
  ; termcode := Unknown
  ; debug    := if (bil_program_irregular p)
                then ["Irregular program detected (duplicate labels or empty statements)"]
                else []
  ; execs    := 0
|>`;


(* ------------------------------------------------------------------------- *)
(*  Misc Tools                                                               *)
(* ------------------------------------------------------------------------- *)
val bil_stepstate_pco_def = Define `bil_stepstate_pco s = s.pco`;

val bil_stepstate_termcode_def = Define `bil_stepstate_termcode s = s.termcode`;

val bil_program_stmts_count_def = Define`bil_program_stmts_count p = SUM (MAP bil_block_stmts_count p)`;

val bil_read_address_label_def = Define `bil_read_address_label l = case l of
  | Address n => n
  | _ => 0b
`;


(* ------------------------------------------------------------------------- *)
(*  Theorems - not yet completed                                             *)
(* ------------------------------------------------------------------------- *)


(* ------------------------------------------------------------------------- *)
val _ = export_theory();
