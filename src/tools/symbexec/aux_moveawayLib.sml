structure aux_moveawayLib =
struct

local

  open HolKernel Parse boolLib bossLib;

  (* error handling *)
  val libname = "aux_moveawayLib"
  val ERR = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname

in (* local *)

  fun mk_oracle_preserve_tags ls tagstr goal =
    let
      fun inject_tags (thm_tags, thm) =
        CONJUNCT2 (CONJ thm_tags thm);
    in
      List.foldr inject_tags (mk_oracle_thm tagstr ([], goal)) ls
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
