structure bir_ppLib :> bir_ppLib =
struct

  open HolKernel Parse PPBackEnd boolLib bossLib;
  open bslSyntax;
  open pretty_exnLib;

  val ERR = mk_HOL_ERR "bir_ppLib";
  val wrap_exn = Feedback.wrap_exn "bir_ppLib";

  val level_log = ref (logLib.INFO: int)
  val _ = register_trace ("bir_ppLib", level_log, logLib.MAX)

  val {error, warn, info, debug, trace, ...} = logLib.gen_fn_log_fns "bir_ppLib" level_log;

  fun term_to_ppstring term = (ppstring pp_term) term
  fun thm_to_ppstring thm = (ppstring pp_thm) thm
  fun pprint_term term = ((print o ppstring pp_term) term; print "\n")
  fun pprint_thm thm = ((print o ppstring pp_thm) thm; print "\n")

  (* End of prelude
   ****************************************************************************)

  (*****************************************************************************
   * Pretty printers
   *)

  fun paren ppfns consistency enabled depth user_printer =
    let
      open Portable term_pp_types smpp
      infix >>
      val {add_string,ublock,ustyle,...} = ppfns: term_pp_types.ppstream_funs
      val colors = [
        RedBrown,   Green,      BrownGreen, DarkBlue,
        Purple,     BlueGreen,  OrangeRed,  VividGreen,
        Yellow,     Blue,       PinkPurple, LightBlue
      ]
      val n_colors = List.length colors
      val idx = ((depth mod n_colors) + n_colors) mod n_colors
      val color = List.nth (colors, idx)
    in
      if enabled then ublock consistency 1
        (ustyle [FG color] (add_string "(")
         >> user_printer
         >> ustyle [FG color] (add_string ")"))
      else user_printer
    end

  fun hol_string_printer _ _ _ {add_string,ustyle,...} _ _ term =
    ustyle [FG Green] (add_string ("\"" ^ (stringSyntax.fromHOLstring term) ^ "\""))
      handle e => raise term_pp_types.UserPP_Failed

  fun bir_immtype_t_printer _ _ _ ppfns _ _ term =
    let
      val {add_string,ustyle,...} = ppfns
      val bit_str = if bir_immSyntax.is_Bit1 term then "Bit1"
        else if bir_immSyntax.is_Bit8 term then "Bit8"
        else if bir_immSyntax.is_Bit16 term then "Bit16"
        else if bir_immSyntax.is_Bit32 term then "Bit32"
        else if bir_immSyntax.is_Bit64 term then "Bit64"
        else if bir_immSyntax.is_Bit128 term then "Bit128"
        else raise ERR "bir_immtype_t_printer" "unknown bir_immtype_t"
    in
      ustyle [FG Blue] (add_string bit_str)
    end
      handle HOL_ERR _ => raise term_pp_types.UserPP_Failed

  fun bir_imm_printer grammars pp_backend sysprinter ppfns gravities depth term =
    let
      open Portable term_pp_types smpp
      infix >>
      val {add_string,ublock,ustyle,...} = ppfns: term_pp_types.ppstream_funs
      fun syspr gravs t = sysprinter {gravs = gravs, depth = depth - 1, binderp = false} t
      open bir_immSyntax
      val (bit_str, dest_fn) =
        if bir_immSyntax.is_Imm1 term then ("Imm1", dest_Imm1)
        else if is_Imm8 term then ("Imm8", dest_Imm8)
        else if is_Imm16 term then ("Imm16", dest_Imm16)
        else if is_Imm32 term then ("Imm32", dest_Imm32)
        else if is_Imm64 term then ("Imm64", dest_Imm64)
        else if is_Imm128 term then ("Imm128", dest_Imm128)
        else raise ERR "bir_imm_printer" "unknown bir_imm type"
      val word_tm = dest_fn term
    in
      paren ppfns PP.CONSISTENT true depth
        (ustyle [FG Blue] (add_string bit_str)
         >> add_string " "
         >> ustyle [FG Purple] (syspr (Top,Top,Top) word_tm))
    end
      handle HOL_ERR _ => raise term_pp_types.UserPP_Failed

  fun bir_exp_printer grammars pp_backend sysprinter ppfns gravities depth term =
    let
      val warn = warn "bir_exp_printer"

      open Portable term_pp_types smpp
      infix >>

      val (type_gm, term_gm) = grammars
      val (parent_g, left_g, right_g) = gravities

      val {add_string,add_break,ublock,ustyle,...} = ppfns: term_pp_types.ppstream_funs
      fun syspr gravs t = sysprinter {gravs = gravs, depth = depth - 1, binderp = false} t

      val paren_required =
               (case right_g of Prec(p, _) => p > 70 | _ => false)
        orelse (case left_g  of Prec(_, n) => n = GrammarSpecials.fnapp_special | _ => false)

      open bir_expSyntax bir_immSyntax bir_exp_immSyntax

      fun print_exp exp =
        if is_BExp_Const exp then
          let
            val prec = Prec (2000, "bir_exp_const")
            val is_false = (identical exp (mk_BExp_Const (mk_Imm_of_int 1 0)))
            val is_true = (identical exp (mk_BExp_Const (mk_Imm_of_int 1 1)))
          in
            if is_false then
              (paren_required, fn () => add_string "BExp_False")
            else if is_true then
              (paren_required, fn () => add_string "BExp_True")
            else
              (paren_required, fn () =>
               ublock PP.CONSISTENT 0
                (add_string "BExp_Const"
                 >> add_string " "
                 >> (syspr (prec,prec,prec) (dest_BExp_Const exp))))
          end
        else if is_BExp_Den exp then
          let val prec = Prec (2000, "bir_exp_den")
          in
            (paren_required, fn () =>
             ublock PP.CONSISTENT 0
              (add_string "BExp_Den"
               >> add_string " "
               >> (syspr (prec,prec,prec) (dest_BExp_Den exp))))
          end
        else if is_BExp_Cast exp then raise term_pp_types.UserPP_Failed
        else if is_BExp_UnaryExp exp then
          let
            val (uop_tm, arg_tm) = dest_BExp_UnaryExp exp
            val uop_str =
              if is_BIExp_ChangeSign uop_tm then "BExp_ChangeSign"
              else if is_BIExp_Not uop_tm then "BExp_Not"
              else if is_BIExp_CLZ uop_tm then "BExp_CLZ"
              else if is_BIExp_CLS uop_tm then "BExp_CLS"
              else raise (warn ("Unknown BIExp: " ^ (term_to_ppstring uop_tm));
                term_pp_types.UserPP_Failed)
            val prec = Prec (2000, uop_str)
          in
            (paren_required, fn () =>
             ublock PP.CONSISTENT 0
              (add_string uop_str
               >> add_break (1, 2)
               >> (syspr (prec,prec,prec) arg_tm)))
          end
        else if is_BExp_BinExp exp then
          let
            val (bop_tm, lhs_tm, rhs_tm) = dest_BExp_BinExp exp
            val bop_str =
              if is_BIExp_And bop_tm then "BExp_And"
              else if is_BIExp_Or bop_tm then "BExp_Or"
              else if is_BIExp_Xor bop_tm then "BExp_Xor"
              else if is_BIExp_Plus bop_tm then "BExp_Plus"
              else if is_BIExp_Minus bop_tm then "BExp_Minus"
              else if is_BIExp_Mult bop_tm then "BExp_Mult"
              else if is_BIExp_Div bop_tm then "BExp_Div"
              else if is_BIExp_SignedDiv bop_tm then "BExp_SignedDiv"
              else if is_BIExp_Mod bop_tm then "BExp_Mod"
              else if is_BIExp_SignedMod bop_tm then "BExp_SignedMod"
              else if is_BIExp_LeftShift bop_tm then "BExp_LeftShift"
              else if is_BIExp_RightShift bop_tm then "BExp_RightShift"
              else if is_BIExp_SignedRightShift bop_tm then "BExp_SignedRightShift"
              else raise (warn ("Unknown BIExp: " ^ (term_to_ppstring bop_tm));
                term_pp_types.UserPP_Failed)
            val prec = Prec (2000, bop_str)
            val delim_required =
              case parent_g of
                  Prec(_, parent_g_name) => not (parent_g_name = bop_str)
                | _ => true
            fun delim wrap body = if delim_required then wrap body else body
            val new_depth = if delim_required then depth - 1 else depth
            fun syspr gravs t = sysprinter {gravs = gravs, depth = new_depth, binderp = false} t
          in
            (delim_required, fn () =>
             delim (fn body =>
              ublock PP.CONSISTENT 0
                (add_string bop_str
                 >> add_break (1, 2)
                 >> ublock PP.CONSISTENT 0 body))
              ((syspr (prec,prec,prec) lhs_tm)
               >> add_break (1, 0)
               >> (syspr (prec,prec,prec) rhs_tm)))
          end
        else if is_BExp_BinPred exp then
          let
            val (bpred_tm, lhs_tm, rhs_tm) = dest_BExp_BinPred exp
            val bpred_str =
              if is_BIExp_Equal bpred_tm then "BExp_Equal"
              else if is_BIExp_NotEqual bpred_tm then "BExp_NotEqual"
              else if is_BIExp_LessThan bpred_tm then "BExp_LessThan"
              else if is_BIExp_SignedLessThan bpred_tm then "BExp_SignedLessThan"
              else if is_BIExp_LessOrEqual bpred_tm then "BExp_LessOrEqual"
              else if is_BIExp_SignedLessOrEqual bpred_tm then "BExp_SignedLessOrEqual"
              else raise (warn ("Unknown BIExp: " ^ (term_to_ppstring bpred_tm));
                term_pp_types.UserPP_Failed)
            val prec = Prec (2000, bpred_str)
          in
            (paren_required, fn () =>
             ublock PP.CONSISTENT 0
              (add_string bpred_str
               >> add_break (1, 2)
               >> ublock PP.CONSISTENT 0
                 ((syspr (prec,prec,prec) lhs_tm)
                  >> add_break (1, 0)
                  >> (syspr (prec,prec,prec) rhs_tm))))
          end
        else if is_BExp_MemEq exp then raise term_pp_types.UserPP_Failed
        else if is_BExp_IfThenElse exp then
          let
            val (cond_tm, then_tm, else_tm) = dest_BExp_IfThenElse exp
            val prec = Prec (2000, "bir_exp_cond")
          in
            (paren_required, fn () =>
             ublock PP.CONSISTENT 0
              ((ublock PP.CONSISTENT 0
                (add_string "BExp_If"
                 >> add_break (1, 2)
                 >> ublock PP.CONSISTENT 0 (syspr (prec,prec,prec) cond_tm)))
               >> add_break (1, 0)
               >> (ublock PP.CONSISTENT 0
                (add_string "BExp_Then"
                 >> add_break (1, 2)
                 >> ublock PP.CONSISTENT 0 (syspr (prec,prec,prec) then_tm)))
               >> add_break (1, 0)
               >> (ublock PP.CONSISTENT 0
                (add_string "BExp_Else"
                 >> add_break (1, 2)
                 >> ublock PP.CONSISTENT 0 (syspr (prec,prec,prec) else_tm)))))
          end
        else if is_BExp_Load exp then raise term_pp_types.UserPP_Failed
        else if is_BExp_Store exp then raise term_pp_types.UserPP_Failed
        else raise term_pp_types.UserPP_Failed

      val (paren_required, printer) = print_exp term
    in
      paren ppfns PP.CONSISTENT paren_required depth (printer ())
    end
      handle HOL_ERR _ => raise term_pp_types.UserPP_Failed

  (*****************************************************************************
   * List of all available pretty printers
   *)

  val pretty_printers = [
    ("HOL_string", ``str: string``, hol_string_printer),
    ("bir_immtype_t", ``bit: bir_immtype_t``, bir_immtype_t_printer),
    ("bir_imm_t", ``bir_imm: bir_imm_t``, bir_imm_printer),
    ("bir_exp_t", ``bir_exp_t: bir_exp_t``, bir_exp_printer)
  ]

  (*****************************************************************************
   * Public functions
   *)

  fun install_bir_pretty_printers () =
    let
      val _ = List.map Parse.temp_add_user_printer pretty_printers
    in () end
    handle e => raise wrap_exn "install_pretty_printer" e;

  fun remove_bir_pretty_printers () =
    let
      fun fst (a, b, c) = a
      val _ = List.map (Parse.temp_remove_user_printer o fst) pretty_printers
    in () end
    handle e => raise wrap_exn "remove_pretty_printer" e;

end (* bir_ppLib *)
