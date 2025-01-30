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

  val EQ_flip = mk_eq o (fn (x,y) => (y,x)) o dest_eq;
  fun wrap_cache_result_EQ_BEQ_gen to_intform to_k to_flip_k kcomp f =
    let
      val (add, lookup) = result_cache kcomp;
      fun f_wrapped x =
        let
          val (x1,x2) = dest_eq x;
          val intform = (to_intform x1, to_intform x2);
          val k = (to_k intform);
          val v_o = lookup k;
        in
          if isSome v_o then valOf v_o else
          let
            val v = f x;
          in
            add (k, v);
            add (to_flip_k intform, CONV_RULE (LHS_CONV SYM_CONV) v);
            v
          end
        end;
    in
      f_wrapped
    end;
  
  fun to_eq_string (s1, s2) =
    s1^"="^s2;
  fun to_flip_eq_string (s1, s2) =
    s2^"="^s1;
  fun wrap_cache_result_EQ_BEQ_string to_string = wrap_cache_result_EQ_BEQ_gen to_string to_eq_string to_flip_eq_string String.compare;

  (*val wrap_cache_result_EQ_BEQ = wrap_cache_result_EQ_BEQ_gen I EQ_flip; *)
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
            add ((*(rhs o concl o SYM_CONV)*)EQ_flip k, CONV_RULE (LHS_CONV SYM_CONV) v);
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
              (print "\nunfinished:\n"; print_thm thm; print "\n\n"; raise ERR funname "didn't reach a result");
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

  local
    datatype res_ex_t = Result of thm | Except of exn;
    fun capture_res_ex f x =
      Result(f x)
      handle e => Except e
    fun process_res_ex v =
      case v of
          Result x => x
        | Except e => raise e;
  in
    fun wrap_res_exn f =
      let
        val (add, lookup) = result_cache Term.compare;
        fun f_wrapped k =
          let
            val v_o = lookup k;
          in
            case v_o of
                SOME v => process_res_ex v
              | _ =>
                let
                  val v = capture_res_ex f k;
                in
                  add (k, v);
                  process_res_ex v
                end
          end;
      in
        f_wrapped
      end;
  end

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
