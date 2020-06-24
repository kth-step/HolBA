structure bir_passificationLib :> bir_passificationLib =
struct

open listSyntax;

(* Unverified translation of loop-free programs to SSA, passified
 * form. *)
(* From BIR core: *)
open bir_programSyntax bir_expSyntax bir_exp_immSyntax
     bir_valuesSyntax;
open bir_envSyntax;
(* From BIR lib: *)
open bir_extra_expsTheory bir_interval_expTheory;
open bir_extra_expsSyntax bir_interval_expSyntax;

(* Exception for use in this structure. *)
val ERR = mk_HOL_ERR "bir_translationLib";

(* Comparison function between two BIR variables.
 * Variables are sorted by type first, string name second. *)
fun bir_var_compare (var1, var2) =
  let
    val (str1, ty1) = dest_BVar_string var1
    val (str2, ty2) = dest_BVar_string var2
    val strcomp = String.compare (str1, str2)
    val tycomp = Term.compare (ty1, ty2)
  in
    if tycomp = EQUAL
    then strcomp
    else tycomp
  end
;

(* Writes a program to a file in .bir format. *)
fun bir_prog_wtf prog file =
  let
    val os = TextIO.openOut file
    val output_to_file = term_to_string prog
    val _ = TextIO.output (os, output_to_file) handle e =>
      (TextIO.closeOut os; raise e)
    val _ = TextIO.closeOut os
  in
    ()
  end
;

(* Reads a program stored in .bir format from a file. *)
fun bir_prog_rff file =
  let
    val is = TextIO.openIn file
    val file_content = TextIO.inputAll is handle e =>
      (TextIO.closeIn is; raise e)
    val prog = Term [QUOTE file_content]
    val _ = TextIO.closeIn is
  in
    prog
  end
;

(* Passification procedure *)
local
  (* TODO: Map with string instead of bir_var term? *)
  val vmap = ref (Redblackmap.mkDict bir_var_compare :
                   (term, int) Redblackmap.dict
                 )
  val underscore = "_"

  fun rename_var var version =
    let
      val (holvarname, varval) = dest_BVar var
      val varname = stringLib.fromHOLstring holvarname
      val new_varname = varname^underscore^(Int.toString version)
    in
      mk_BVar (stringLib.fromMLstring new_varname, varval)
    end

  fun rename_vars_in_exp exp =
    (* Leaves *)
    if is_BExp_Const exp
    then exp
    else if is_BExp_MemConst exp
    then exp
    else if is_BExp_Den exp
    then let
           val var = dest_BExp_Den exp
           val version = Redblackmap.peek (!vmap, var)
         in
           if (isSome version)
           then mk_BExp_Den (rename_var var (valOf version))
           else let
                  val _ = vmap := Redblackmap.insert (!vmap, var, 0)
                in
                  mk_BExp_Den (rename_var var 0)
                end
         end
    (* One branch *)
    else if is_BExp_Cast exp
    then let
           val (ct, subexp, it) = dest_BExp_Cast exp
         in
           mk_BExp_Cast (ct, rename_vars_in_exp subexp, it)
         end
  else if is_BExp_UnaryExp exp
  then let
         val (ue, subexp) = dest_BExp_UnaryExp exp
       in
         mk_BExp_UnaryExp (ue, rename_vars_in_exp subexp)
       end
  (* Two branches *)
  else if is_BExp_BinExp exp
  then let
         val (be, subexp1, subexp2) = dest_BExp_BinExp exp
       in
         mk_BExp_BinExp (be, rename_vars_in_exp subexp1,
                             rename_vars_in_exp subexp2)
       end
  else if is_BExp_BinPred exp
  then let
         val (bp, subexp1, subexp2) = dest_BExp_BinPred exp
       in
         mk_BExp_BinPred (bp, rename_vars_in_exp subexp1,
                              rename_vars_in_exp subexp2)
       end
  else if is_BExp_MemEq exp
  then let
         val (subexp1, subexp2) = dest_BExp_MemEq exp
       in
         mk_BExp_MemEq (rename_vars_in_exp subexp1,
                        rename_vars_in_exp subexp2)
       end
  else if is_BExp_IfThenElse exp
  then let
         val (subexp1, subexp2, subexp3) = dest_BExp_IfThenElse exp
       in
         mk_BExp_IfThenElse (rename_vars_in_exp subexp1,
                             rename_vars_in_exp subexp2,
                             rename_vars_in_exp subexp3)
       end
  else if is_BExp_Load exp
  then let
         val (subexp1, subexp2, en, it) = dest_BExp_Load exp
       in
         mk_BExp_Load (rename_vars_in_exp subexp1,
                       rename_vars_in_exp subexp2, en, it)
       end
  else if is_BExp_Store exp
  then let
         val (subexp1, subexp2, en, subexp3) = dest_BExp_Store exp
       in
         mk_BExp_Store (rename_vars_in_exp subexp1,
                        rename_vars_in_exp subexp2, en,
                        rename_vars_in_exp subexp3)
       end
  (* Additional supported abbreviations: *)
  else if is_BExp_Aligned exp
  then let
         val (sz, p, subexp) = dest_BExp_Aligned exp
       in
         mk_BExp_Aligned (sz, p, rename_vars_in_exp subexp)
       end
  else if is_BExp_unchanged_mem_interval_distinct exp
  then let
         val (sz, mb_n, me_n, subexp, isz) =
           dest_BExp_unchanged_mem_interval_distinct exp
       in
         mk_BExp_unchanged_mem_interval_distinct
           (sz, mb_n, me_n, rename_vars_in_exp subexp, isz)
       end
  (* Outside syntax, should not happen... *)
  else raise (ERR "passify_prog_ssa"
                  ("The expression "^(Parse.term_to_string exp)^
                   " was "^
                   "not found in supported BIR syntax.")
             )

  fun passify_assign stmt =
    let
      val (var, exp) = dest_BStmt_Assign stmt
      (* 1. Rename variables in assigned expression *)
      val renamed_exp = rename_vars_in_exp exp
      (* 2. Get version of variable assigned to *)
      val version = Redblackmap.peek (!vmap, var)
      (* 3. Get equality constructor for right type of variable *)
      val mk_exp_eq =
        if is_BType_Imm ((snd o dest_BVar) var)
        then (fn (e1, e2) =>
                mk_BExp_BinPred (BIExp_Equal_tm, e1, e2)
             )
        else mk_BExp_MemEq
    in
      if (isSome version)
      then let
             val new_version = (valOf version)+1
             val _ = vmap := Redblackmap.insert (!vmap, var,
                                                 new_version)
           in
             mk_BStmt_Assume (
               mk_exp_eq (mk_BExp_Den (rename_var var new_version),
                          renamed_exp)
             )
           end
      else let
             val _ = vmap := Redblackmap.insert (!vmap, var, 0)
           in
             mk_BStmt_Assume (
               mk_exp_eq (mk_BExp_Den (rename_var var 0),
                          renamed_exp)
             )
           end
    end

  fun rename_vars_assert stmt =
    let
      val exp = dest_BStmt_Assert stmt
      val renamed_exp = rename_vars_in_exp exp
    in
      mk_BStmt_Assert renamed_exp
    end

  fun rename_vars_assume stmt =
    let
      val exp = dest_BStmt_Assume stmt
      val renamed_exp = rename_vars_in_exp exp
    in
      mk_BStmt_Assume renamed_exp
    end

  fun rename_vars_observe stmt =
    let
      val (oid, exp, explist_tm, valmap) = dest_BStmt_Observe stmt
      val renamed_exp = rename_vars_in_exp exp
      val (explist, hty) = dest_list explist_tm
      val renamed_explist = map rename_vars_in_exp explist
    in
      mk_BStmt_Observe (oid, renamed_exp, mk_list (renamed_explist, hty),
                        valmap)
    end

  fun passify_bstmts_ssa []     = []
    | passify_bstmts_ssa (h::t) =
        (* Case: Assign. Rename and update version. *)
        if is_BStmt_Assign h
        then (passify_assign h::
              (passify_bstmts_ssa t)
             )
        (* Case: Other basic BIR statements. Just rename vars. *)
        else if is_BStmt_Assert h
        then (rename_vars_assert h::
              (passify_bstmts_ssa t)
             )
        else if is_BStmt_Assume h
        then (rename_vars_assume h::
              (passify_bstmts_ssa t)
             )
        else if is_BStmt_Observe h
        then (rename_vars_observe h::
              (passify_bstmts_ssa t)
             )
        else raise (ERR "passify_prog_ssa"
                        ("The statement "^(Parse.term_to_string h)^
                        " is "^
                        "not found in supported BIR syntax.")
                   )

  fun rename_vars_cjmp stmt =
    let
      val (exp, l1, l2) = dest_BStmt_CJmp stmt
      val renamed_exp = rename_vars_in_exp exp
    in
      mk_BStmt_CJmp (renamed_exp, l1, l2)
    end

  fun rename_vars_halt stmt =
    let
      val exp = dest_BStmt_Halt stmt
      val renamed_exp = rename_vars_in_exp exp
    in
      mk_BStmt_Halt renamed_exp
    end

  fun passify_estmt_ssa stmt =
    if is_BStmt_Jmp stmt
    then stmt
    else if is_BStmt_CJmp stmt
    then rename_vars_cjmp stmt
    else if is_BStmt_Halt stmt
    then rename_vars_halt stmt
    else raise (ERR "passify_estmt_ssa"
                    ("The statement "^(Parse.term_to_string
                                         stmt)^
                     " is not found in supported BIR syntax.")
               )

fun passify_block_list_ssa []     = []
  | passify_block_list_ssa (h::t) =
      let
        val (obs, label, bstmts, estmt) = dest_bir_block_list h
        val passified_bstmts =
          map (inst [(* TODO: make this "alpha" again *) (Type `:'a`) |-> obs]) (passify_bstmts_ssa bstmts)
        val passified_estmt = passify_estmt_ssa estmt
        val passified_block =
          mk_bir_block_list (obs, label, passified_bstmts,
                             passified_estmt)
      in
        (passified_block::passify_block_list_ssa t)
      end

in
fun bir_prog_pass_ssa prog =
  let
    val (hty, block_list) = dest_BirProgram_list prog
  in
    mk_BirProgram_list (hty, passify_block_list_ssa block_list)
  end
end;

end;
