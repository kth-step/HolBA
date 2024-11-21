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

fun measure_fun s f v =
  let
    val timer = holba_miscLib.timer_start 0;
    val res = f v;
    val _ = holba_miscLib.timer_stop (fn delta_s => print (s ^ delta_s ^ "\n")) timer;
  in
    res
  end;

local
  open bir_programSyntax;
  open bir_program_labelsSyntax;
  open bir_immSyntax;
  open numSyntax;
  open stringSyntax;
in
  fun imm_to_hexstring immv =
    let
      val (bw, v) = gen_dest_Imm immv;
    in
      "imm(" ^
      Int.toString bw ^
      "; 0x" ^
      (Arbnum.toHexString o wordsSyntax.dest_word_literal) v ^
      ")"
    end;

  fun label_to_string label =
    if is_BL_Label label then
      "label(" ^
      ((fromHOLstring o dest_BL_Label) label) ^
      ")"
    else if is_BL_Address label then
      "address(" ^
      imm_to_hexstring (dest_BL_Address label) ^
      ")"
    else if is_BL_Address_HC label then
      let
        val (immv, comment) = dest_BL_Address_HC label;
      in
        "address(" ^
        imm_to_hexstring immv ^
        "; " ^
        fromHOLstring comment ^
        ")"
      end
    else
      raise ERR "label_to_string" "unexpected";

  fun pc_to_string pc =
    let
      val (label,index) = dest_bir_programcounter pc;
      val label_str = label_to_string label;
      val index_str = Arbnum.toString (dest_numeral index);
    in
      "pc(" ^
      label_str ^
      "; " ^
      index_str ^
      ")"
    end;
end

end (* local *)

end (* struct *)
