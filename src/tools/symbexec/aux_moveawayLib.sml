structure aux_moveawayLib =
struct

local

  open HolKernel Parse boolLib bossLib;

  (* error handling *)
  val libname = "aux_moveawayLib"
  val ERR = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname

in (* local *)

  fun result_cache kcomp =
    let
      val d = ref (Redblackmap.mkDict kcomp);
      fun add (k, v) = d := Redblackmap.insert (!d, k, v);
      fun lookup k = 
        SOME (Redblackmap.find (!d, k))
        handle NotFound => NONE;
    in
      (add, lookup)
    end;

  fun wrap_cache_result kcomp f =
    let
      val (add, lookup) = result_cache kcomp;
      fun f_wrapped k =
        let
          val v_o = lookup k;
        in
          if isSome v_o then valOf v_o else
          let
            val v = f k;
          in
            add (k, v);
            v
          end
        end;
    in
      f_wrapped
    end;

  fun wrap_cache_result_EQ_BEQ kcomp f =
    let
      val (add, lookup) = result_cache kcomp;
      fun f_wrapped k =
        let
          val v_o = lookup k;
        in
          if isSome v_o then valOf v_o else
          let
            val v = f k;
          in
            add (k, v);
            add ((*(rhs o concl o SYM_CONV)*)(mk_eq o (fn (x,y) => (y,x)) o dest_eq) k, CONV_RULE (LHS_CONV SYM_CONV) v);
            v
          end
        end;
    in
      f_wrapped
    end;

  fun wrap_cache_CONV_inter_result funname k_tm_fun check_res_tm_fun f =
    let
      val (add:term * thm -> unit, lookup) = result_cache Term.compare;
      fun add_result thm =
        let
          val (term, result) = (dest_eq o concl) thm;
          val k_tm = k_tm_fun term;
          val _ =
            if check_res_tm_fun result then () else
              (print_thm thm; print "\n\n"; raise ERR funname "didn't reach a result");
        in (add (k_tm, thm); thm) end;

      fun f_wrapped tm =
        let
          val k_tm = k_tm_fun tm;
          val vars_thm_o = lookup k_tm;
        in
          if isSome vars_thm_o then ((*print "successss!!!!\n";*) valOf vars_thm_o) else
          add_result (f f_wrapped tm)
        end;
    in
      f_wrapped
    end;

end (* local *)

end (* struct *)
