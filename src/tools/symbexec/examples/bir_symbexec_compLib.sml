structure bir_symbexec_compLib =
struct

local
  open bir_symbexec_stateLib;

  open bir_constpropLib;
  open bir_exp_helperLib;
  open bir_expSyntax;
in (* outermost local *)

  (* TODO: make this available at some more central location (it is from src/tools/exec/auxLib *)
  fun find_subterm is_tm_fun tm =
    if is_tm_fun tm then
      SOME tm
    else if is_comb tm then
      let
        val (l,r) = dest_comb tm;
      in
        case find_subterm is_tm_fun l of
           SOME tm2 => SOME tm2
         | NONE => find_subterm is_tm_fun r
      end
    else
      NONE
    ;

  fun subterm_satisfies is_tm_fun tm =
    (isSome o find_subterm is_tm_fun) tm;

  fun compute_val_try_const_only vals (besubst, besubst_vars) deps_l2 =
    let
      val all_deps_const = List.all (fn bv =>
             (is_bvar_bound vals) bv andalso
             (case find_bv_val "compute_val_try_const_only" vals bv of
                 SymbValBE (exp,_) => is_BExp_Const exp
               | _ => false)
           ) besubst_vars;
    in
      if all_deps_const then
        if List.null besubst_vars then NONE else
        let
          val _ = if Redblackset.isEmpty deps_l2 then () else
                  raise ERR "compute_val_try_const_only" "deps_l2 is not empty. Unexpected here.";

          fun subst_fun_symbvalbe vals (bv_dep, e) =
            let
              val symbv_dep = find_bv_val "compute_val_try_const_only" vals bv_dep;
              val exp = case symbv_dep of
                           SymbValBE (exp,_) => exp
                         | _ => raise ERR "compute_val_try_const_only" "cannot happen";
            in
              subst_exp (bv_dep, exp, e)
            end;

          val becomp = List.foldr (subst_fun_symbvalbe vals) besubst besubst_vars;
        in
          SOME (SymbValBE (becomp, symbvalbe_dep_empty))
        end
      else
        NONE
    end;

  open bslSyntax;
  val var_add_const_match_tm = bplus (bden ``x:bir_var_t``, bconstimm ``y:bir_imm_t``);
  val const_add_var_match_tm = bplus (bconstimm ``y:bir_imm_t``, bden ``x:bir_var_t``);
  val var_sub_const_match_tm = bminus(bden ``x:bir_var_t``, bconstimm ``y:bir_imm_t``);

  fun add_imms imm_val imm_val_2 = 
        (snd o dest_eq o concl o EVAL) ``bir_bin_exp BIExp_Plus ^imm_val ^imm_val_2``;
  fun sub_imms imm_val imm_val_2 = 
        (snd o dest_eq o concl o EVAL) ``bir_bin_exp BIExp_Minus ^imm_val ^imm_val_2``;

  fun compute_val_try_single_interval vals (besubst, besubst_vars) =
    let
      val depends_on_single_interval =
             length besubst_vars = 1 andalso
             (is_bvar_bound vals) (hd besubst_vars) andalso
             (case find_bv_val "compute_val_try_single_interval" vals (hd besubst_vars) of
                 SymbValInterval _ => true
               | _ => false);
    in
      if depends_on_single_interval then
        let
          val (vs, _) = hol88Lib.match var_add_const_match_tm besubst;
          val bv      = fst (List.nth (vs, 0));
          val imm_val = fst (List.nth (vs, 1));

          val _ = if identical bv (hd besubst_vars) then () else
                  raise ERR "compute_val_try_single_interval" "something is not right 1...";

          val ((itv_exp1, itv_exp2), itv_deps) =
             (case find_bv_val "compute_val_try_single_interval" vals bv of
                 SymbValInterval x => x
               | _ => raise ERR "compute_val_try_single_interval" "something is not right 2...");

          fun add_const exp imm_val =
            if is_BExp_Den exp then bplus (exp, bconstimm imm_val) else
            let
              val (vs, _) = hol88Lib.match var_add_const_match_tm exp;
              val bv_       = fst (List.nth (vs, 0));
              val imm_val_2 = fst (List.nth (vs, 1));

              val res_tm = add_imms imm_val imm_val_2;
            in
              bplus (bden bv_, bconstimm res_tm)
            end;
        in
          SOME (SymbValInterval ((add_const itv_exp1 imm_val,
                                  add_const itv_exp2 imm_val),
                                 itv_deps))
        end
        handle HOL_ERR _ => NONE
      else
        NONE
    end;
(*
(print "(((((((((((((((((((((((())))))))))))))))))))))))\n\n\n"; 
*)
  fun get_var_plusminus_const exp =
    let
      val (vs, _) = hol88Lib.match var_add_const_match_tm exp;
      val bv      = fst (List.nth (vs, 0));
      val imm_val = fst (List.nth (vs, 1));
    in
      (bv, (imm_val, true))
    end
    handle HOL_ERR _ => (
    let
      val (vs, _) = hol88Lib.match const_add_var_match_tm exp;
      val bv      = fst (List.nth (vs, 1));
      val imm_val = fst (List.nth (vs, 0));
    in
      (bv, (imm_val, true))
    end
    handle HOL_ERR _ =>
    let
      val (vs, _) = hol88Lib.match var_sub_const_match_tm exp;
      val bv      = fst (List.nth (vs, 0));
      val imm_val = fst (List.nth (vs, 1));
    in
      (bv, (imm_val, false))
    end);

  fun add_imm_plusminus (imm_val1, true) (imm_val2, true) =
        (add_imms imm_val1 imm_val2, true)
    | add_imm_plusminus (imm_val1, false) (imm_val2, false) =
        (add_imms imm_val1 imm_val2, false)
    | add_imm_plusminus (imm_val1, true) (imm_val2, false) =
        add_imm_plusminus (imm_val2, false) (imm_val1, true)
    | add_imm_plusminus (imm_val1, false) (imm_val2, true) =
        if Arbnum.<= (
             (wordsSyntax.dest_word_literal o snd o bir_immSyntax.gen_dest_Imm) imm_val1,
             (wordsSyntax.dest_word_literal o snd o bir_immSyntax.gen_dest_Imm) imm_val2) then
          (sub_imms imm_val2 imm_val1, true)
        else
          (sub_imms imm_val1 imm_val2, false);

  fun exp_from_bv_plusminus_imm bv (imm_val, imm_plus) =
    (if imm_plus then bplus else bminus)
    (bden bv, bconstimm imm_val);

  fun compute_val_try_expplusminusconst vals (besubst, besubst_vars) =
    let
      val depends_on_single_exp =
             length besubst_vars = 1 andalso
             (is_bvar_bound vals) (hd besubst_vars) andalso
             (case find_bv_val "compute_val_try_expplusminusconst" vals (hd besubst_vars) of
                 SymbValBE _ => true
               | _ => false);
    in
      if depends_on_single_exp then
        let
          val (bv, imm_val_pm) = get_var_plusminus_const besubst;

          val (exp2, deps2) =
             (case find_bv_val "compute_val_try_expplusminusconst" vals bv of
                 SymbValBE x => x
               | _ => raise ERR "compute_val_try_expplusminusconst" "something is not right 2...");

          val (bv2, imm_val_pm2) = get_var_plusminus_const exp2;

          val imm_val_pm12 = add_imm_plusminus imm_val_pm imm_val_pm2;
        in
          SOME (SymbValBE (exp_from_bv_plusminus_imm bv2 imm_val_pm12, deps2))
        end
        handle HOL_ERR _ => NONE
      else
        NONE
    end;

  val debug_addrOn = false;

  fun process_addr str_op vals addr_tm =
    let
      val _ = if not debug_addrOn then () else
              print (str_op ^ "\n---------------\n");
      (*
      val _ = (print ("addr " ^ str_op ^ ": [[[\n"); print_term addr_tm; print "]]]\n\n");
      *)
      val addr_tm_vars = get_birexp_vars addr_tm;
      val addr_ =
          if is_BExp_Den addr_tm then
            SOME (find_bv_val "state_make_interval" vals (dest_BExp_Den addr_tm))
          else
            compute_val_try_expplusminusconst vals (addr_tm, addr_tm_vars);
      (*
      val _ = if isSome addr_ then print (symbv_to_string (valOf addr_)) else
              print "NONE";
      *)
      val (addr, addr_deps) =
          case addr_ of
             SOME (SymbValBE x) => x
           | NONE => (addr_tm, Redblackset.addList (symbvalbe_dep_empty, addr_tm_vars))
           | _ => raise ERR "process_addr" "NEEDS TO BE A SYMBOLIC EXPRESSION";

      val _ = if not debug_addrOn then () else
              (print ("addr proc: {{{\n"); print_term addr; print "}}}\n\n");
    in
      (addr, addr_deps)
    end;

(* ================================================================ *)

  val bexpden_match_tm = bden ``x:bir_var_t``;
  fun lookup_mem_symbv vals symbv =
    case symbv of
       SymbValBE (t, _) => (
         let
           val (vs, _) = hol88Lib.match bexpden_match_tm t;
           val bv      = fst (List.nth (vs, 0));
         in
           find_bv_val "lookup_mem_symbv" vals bv
         end
         handle _ => raise ERR "lookup_mem_symbv" "SymbValBE didn't match bexpden"
        )
     | SymbValMem _ => symbv
     | _ => raise ERR "lookup_mem_symbv" "needs to be SymbValBE or SymbValMem";

  fun bexp_to_bittype tm_v =
    let
      val bty_v_o = bir_exp_helperLib.get_type_of_bir_exp tm_v;
      val bty_v = if optionSyntax.is_some bty_v_o then
                    optionSyntax.dest_some bty_v_o
                  else
                    raise ERR "bexp_to_immsize" "couldn't resolve expression type";

      val sz_tm =
        if bir_valuesSyntax.is_BType_Imm bty_v then
          bir_valuesSyntax.dest_BType_Imm bty_v
        else
          raise ERR "bexp_to_immsize" "no bir imm";
    in
      sz_tm
    end;

  fun bittype_to_size sz_tm =
      if identical sz_tm ``Bit1``   then   1 else
      if identical sz_tm ``Bit8``   then   8 else
      if identical sz_tm ``Bit16``  then  16 else
      if identical sz_tm ``Bit32``  then  32 else
      if identical sz_tm ``Bit64``  then  64 else
      if identical sz_tm ``Bit128`` then 128 else
      raise ERR "bittype_to_size" "unknown bit size";

  fun mem_addr_sz_offset addrint szint =
    let
      val zerobits = (szint div 8) - 1;
      val zeromask =
           Word.- (Word.<< (Word.fromInt 1, Word.fromInt zerobits), Word.fromInt 1);
      val zeromasked =
           Word.andb (Word.fromInt addrint, zeromask);
      (*
      val _ = print ((Word.toString zeromask) ^ "\n");
      val _ = print ((Word.toString zeromasked) ^ "\n");
      *)
    in
      Word.toInt zeromasked
    end;

(* ================================================================ *)

  fun mem_store_stack mem bv_sp imm_offset val_tm =
    let
      val ((mem_const_size, mem_globl_size, mem_stack_size),
           (mem_const, mem_globl, (bv_sp_, mem_stack)),
           deps) = mem;

      val _ = if identical bv_sp bv_sp_ then () else
              raise ERR "mem_store_stack" "stackpointer doesn't match memory abstraction";

      (* TODO: add check that addr is well in stack memory (would require pred, and maybe smt solver for simplicity) *)
      (* TODO: add check that addr is aligned? is this needed? probably not *)

      val val_tm_deps = Redblackset.fromList Term.compare (get_birexp_vars val_tm);
      (* this is an overapproximation, because variables may get lost when overwriting *)
      val deps_new = Redblackset.union (deps, val_tm_deps);

      val val_tm_sz = (bittype_to_size o bexp_to_bittype) val_tm;
      (* TODO: fix for wordlengths other than 32 *)
      (* TODO: to allow 8 here is a bug at the moment! *)
      val _ = if val_tm_sz = 32 orelse val_tm_sz = 8 then () else
              raise ERR "mem_store_const" "cannot handle anything other than 32 currently";

      val offset = (wordsSyntax.dest_word_literal o bir_immSyntax.dest_Imm32) imm_offset;
      val mem_stack_new = Redblackmap.insert (mem_stack, offset, (val_tm, val_tm_deps));
    in
      SymbValMem ((mem_const_size, mem_globl_size, mem_stack_size),
                  (mem_const, mem_globl, (bv_sp, mem_stack_new)),
                  deps_new)
    end;

  fun mem_store_const mem caddr val_tm =
    let
      val ((mem_const_size, mem_globl_size, mem_stack_size),
           (mem_const, mem_globl, (bv_sp, mem_stack)),
           deps) = mem;

      val val_tm_deps = Redblackset.fromList Term.compare (get_birexp_vars val_tm);
      (* this is an overapproximation, because variables may get lost when overwriting *)
      val deps_new = Redblackset.union (deps, val_tm_deps);

      val val_tm_sz = (bittype_to_size o bexp_to_bittype) val_tm;

      val _ = if val_tm_sz = 32 orelse
                 val_tm_sz = 16 orelse
                 val_tm_sz =  8 then () else
              raise ERR "mem_store_const" "cannot handle anything other than 32/16/8 bit stores currently";

      val zeromasked = mem_addr_sz_offset (Arbnum.toInt caddr) val_tm_sz;
      (*val suboff = mem_addr_sz_offset (Arbnum.toInt caddr) 32;*)

      val _ = if zeromasked = 0 then () else
              raise ERR "mem_store_const" "store address is not aligned";

      (* TODO: fix for wordlengths other than 32 *)
      val _ = if val_tm_sz = 32 then () else
              raise ERR "mem_store_const" "cannot handle anything other than 32 currently";

      val mem_globl_new = Redblackmap.insert (mem_globl, caddr, (val_tm, val_tm_deps));
    in
      if Arbnum.<  (caddr, mem_const_size) orelse
         Arbnum.<= (Arbnum.+ (mem_const_size, mem_globl_size), caddr) then
        raise ERR "mem_store_const" "global store out of global memory range"
      else
      SymbValMem ((mem_const_size, mem_globl_size, mem_stack_size),
                  (mem_const, mem_globl_new, (bv_sp, mem_stack)),
                  deps_new)
    end;

  fun mem_store mem addr_tm end_tm val_tm =
    let
      (* NOTE: this only works for (BType_Mem Bit32 Bit8) and
                          little endian memory operations *)
      val _ = if identical end_tm ``BEnd_LittleEndian`` then () else
              raise ERR "mem_store" "needs to be little endian";
    in
      if is_BExp_Const addr_tm then
        let
          val caddr = (wordsSyntax.dest_word_literal o bir_immSyntax.dest_Imm32 o dest_BExp_Const) addr_tm;
        in
          SOME (mem_store_const mem caddr val_tm)
        end
      else
      let
        val (vs, _) = hol88Lib.match var_sub_const_match_tm addr_tm
                       handle _ => raise ERR "mem_store"
                                      ("couldn't resolve addr_tm: " ^ (term_to_string addr_tm));
        val bv      = fst (List.nth (vs, 0));
        val imm_val = fst (List.nth (vs, 1));
      in
        SOME (mem_store_stack mem bv imm_val val_tm)
      end
    end;


(* ================================================================ *)

(* TODO: add initial memory symbol and add it to memory abstractions for loads from "unpopulated" memory *)

  fun mem_load_exp_gen exp suboff sz =
    let
      val _ =
        if sz = 32 orelse
           sz = 16 orelse
           sz =  8 then ()
        else
          raise ERR "mem_load_exp_gen" "cannot handle word size";

      val bytes = sz div 8;

      val _ = if suboff >= 0 orelse suboff + bytes <= 4 then () else
              raise ERR "mem_load_exp_gen" "reading outside of word32";
    in
      if sz = 32 then
        exp
      else if sz = 16 andalso suboff = 0 then
        blowcast16 exp
      else if sz = 16 andalso suboff = 2 then
        bhighcast16 exp
      else if sz =  8 andalso suboff = 0 then
        blowcast8 exp
      else if sz =  8 andalso suboff = 1 then
        bhighcast8 (blowcast16 exp)
      else if sz =  8 andalso suboff = 2 then
        blowcast8 (bhighcast16 exp)
      else if sz =  8 andalso suboff = 3 then
        bhighcast8 exp
      else raise ERR "mem_load_exp_gen" "this should never happen"
    end;

  fun mem_load_stack mem bv_sp imm_offset sz_tm =
    let
      val ((mem_const_size, mem_globl_size, mem_stack_size),
           (mem_const, mem_globl, (bv_sp_, mem_stack)),
           deps) = mem;

      val _ = if identical bv_sp bv_sp_ then () else
              raise ERR "mem_store_stack" "stackpointer doesn't match memory abstraction";

      (* TODO: add check that addr is well in stack memory (would require pred, and maybe smt solver for simplicity) *)
      (* TODO: add check that addr is aligned? is this needed? YES *)

      val sz = (bittype_to_size) sz_tm;

      val sp_offset = (Arbnum.toInt o wordsSyntax.dest_word_literal o bir_immSyntax.dest_Imm32) imm_offset;

      val suboff = 4 - (mem_addr_sz_offset sp_offset 32);
      val offset = if suboff = 4
                   then sp_offset
                   else sp_offset + suboff;

      val (exp, deps) = Redblackmap.find (mem_stack, Arbnum.fromInt offset)
        handle _ => raise ERR "mem_load_stack" "address is not mapped in global memory";

      val exp' = mem_load_exp_gen exp suboff sz;
    in
      SymbValBE (exp', deps)
    end;

  fun mem_load_const_le_sz mem_const addr sz acc =
    if sz = 0 then
      acc
    else if sz <> 32 andalso
       sz <> 24 andalso
       sz <> 16 andalso
       sz <> 8 then
      raise ERR "mem_load_const_le_sz" "cannot handle word size"
    else (
      mem_load_const_le_sz
         mem_const
         addr
         (sz-8)
         (case (acc, mem_const (Arbnum.+ (addr, Arbnum.fromInt ((sz-8) div 8)))) of
             (SOME v1, SOME v0) =>
               SOME (Arbnum.+ (Arbnum.* (v1, Arbnum.fromInt 256), v0))
           | _ => NONE
          )
    );

  fun mem_load_const mem caddr sz_tm =
    let
      val ((mem_const_size, mem_globl_size, mem_stack_size),
           (mem_const, mem_globl, (bv_sp, mem_stack)),
           deps) = mem;

      val sz = (bittype_to_size) sz_tm;

      val _ = if sz = 32 orelse
                 sz = 16 orelse
                 sz =  8 then () else
              raise ERR "mem_load_const" "cannot handle anything other than 32/16/8 bit loads currently";

      val zeromasked = mem_addr_sz_offset (Arbnum.toInt caddr) sz;
      val suboff = mem_addr_sz_offset (Arbnum.toInt caddr) 32;

      val _ = if zeromasked = 0 then () else
              raise ERR "mem_load_const" "load address is not aligned";
    in
      if Arbnum.<= (Arbnum.+ (mem_const_size, mem_globl_size), caddr) then
        raise ERR "mem_load_const" "const/global load out of corresponding memory range"
      else if Arbnum.<= (mem_const_size, caddr) then
        (* global load *)
        (
          let
            val (exp, deps) = Redblackmap.find (mem_globl, caddr)
              handle _ => raise ERR "mem_load_const" "address is not mapped in global memory";
            val exp' = mem_load_exp_gen exp suboff sz;
          in
            SymbValBE (exp', deps)
          end
        )
      else (
        (* const load *)
        let
          val exp = (bconst32 o Arbnum.toInt o valOf)
                     (mem_load_const_le_sz mem_const caddr sz (SOME Arbnum.zero))
              handle _ => raise ERR "mem_load_const"
                             ("memory at addr " ^ (Arbnum.toHexString caddr) ^
                              " seems not available (" ^ (term_to_string sz_tm) ^ ")");
          val exp' = mem_load_exp_gen exp suboff sz;
        in
          SymbValBE (exp', symbvalbe_dep_empty)
        end
      )
    end;

  fun mem_load mem addr_tm end_tm sz_tm =
    let
      (* NOTE: this only works for (BType_Mem Bit32 Bit8) and
                          little endian memory operations *)
      val _ = if identical end_tm ``BEnd_LittleEndian`` then () else
              raise ERR "mem_load" "needs to be little endian";
    in
      if is_BExp_Const addr_tm then
        let
          val caddr = (wordsSyntax.dest_word_literal o bir_immSyntax.dest_Imm32 o dest_BExp_Const) addr_tm;
        in
          SOME (mem_load_const mem caddr sz_tm)
        end
      else
      let
        val (vs, _) = hol88Lib.match var_sub_const_match_tm addr_tm
                      handle _ => raise ERR "mem_load"
                                    ("couldn't resolve addr_tm: " ^ (term_to_string addr_tm));
        val bv      = fst (List.nth (vs, 0));
        val imm_val = fst (List.nth (vs, 1));
      in
        SOME (mem_load_stack mem bv imm_val sz_tm)
      end
    end;

(* ================================================================ *)

  val debug_memOn = false;

  fun compute_val_try_mem_load compute_val_and_resolve_deps vals (besubst, besubst_vars) =
    if is_BExp_Load besubst then
    let
      val (mem_tm, addr_tm, end_tm, sz_tm) = dest_BExp_Load besubst;
      val (addr, addr_deps) = process_addr "load" vals addr_tm;

      val mem_symbv_resolve = compute_val_and_resolve_deps vals (mem_tm, besubst_vars);
      val mem_symbv_o = SOME (lookup_mem_symbv vals mem_symbv_resolve)
                        handle _ => NONE;

      val mem_o = case mem_symbv_o of
                     SOME (SymbValMem m) => SOME m
                   | _ => NONE;
    in
      if is_none mem_o then NONE else
      let
        val mem_symbv = valOf mem_symbv_o;
        val mem       = valOf mem_o;

        val _ = if not debug_memOn then () else (
                  print "\n\n============ load\n";
                  print ((symbv_to_string mem_symbv) ^ "\n");
                  print_term addr;
                  print_term sz_tm
                );

        val res = mem_load mem addr end_tm sz_tm;

        val _ = if not debug_memOn then () else (
                  if is_none res then print "NONE\n" else
                  print ((symbv_to_string (valOf res)) ^ "\n")
                );
      in
        res
      end
    end
    else NONE;

  fun compute_val_try_mem_store compute_val_and_resolve_deps vals (besubst, besubst_vars) =
    if is_BExp_Store besubst then
    let
      val (mem_tm, addr_tm, end_tm, val_tm) = dest_BExp_Store besubst;
      val (addr, addr_deps) = process_addr "store" vals addr_tm;

      val mem_symbv_resolve = compute_val_and_resolve_deps vals (mem_tm, besubst_vars);
      val mem_symbv_o = SOME (lookup_mem_symbv vals mem_symbv_resolve)
                        handle _ => NONE;

      val mem_o = case mem_symbv_o of
                     SOME (SymbValMem m) => SOME m
                   | _ => NONE;
    in
      if is_none mem_o then NONE else
      let
        val mem_symbv = valOf mem_symbv_o;
        val mem       = valOf mem_o;

        val _ = if not debug_memOn then () else (
                  print "\n\n============ store\n";
                  print ((symbv_to_string mem_symbv) ^ "\n");
                  print_term addr;
                  print_term val_tm
                );

        val res = mem_store mem addr end_tm val_tm;

        val _ = if not debug_memOn then () else (
                  if is_none res then print "NONE\n" else
                  print ((symbv_to_string (valOf res)) ^ "\n")
                );
      in
        res
      end
    end
    else NONE;

  (* TODO: this should probably not be separate... *)
  fun compute_val_try_mem_subexp compute_val_and_resolve_deps vals (besubst, besubst_vars) =
    if subterm_satisfies is_BExp_Load besubst then
        (* TODO: need to carry out load and subsistute in expression *)
        NONE
    else if subterm_satisfies is_BExp_Store besubst then
        NONE (*
      raise ERR "compute_val_try_mem"
                ("found store as subexpression, unexpected: " ^
                 term_to_string besubst) *)
    else NONE;

  fun compute_val_try_mem compute_val_and_resolve_deps vals (besubst, besubst_vars) =
    case compute_val_try_mem_load   compute_val_and_resolve_deps vals (besubst, besubst_vars) of
        SOME x => SOME x
      | NONE => (
    case compute_val_try_mem_store  compute_val_and_resolve_deps vals (besubst, besubst_vars) of
        SOME x => SOME x
      | NONE => (
         compute_val_try_mem_subexp compute_val_and_resolve_deps vals (besubst, besubst_vars)
    ));

end (* outermost local *)

end (* struct *)
