structure aux_moveawayLib =
struct

local

open HolKernel Parse boolLib bossLib;

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

end (* local *)

end (* struct *)
