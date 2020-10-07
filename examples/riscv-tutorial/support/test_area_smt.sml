local
  open bir_env_oldTheory;
  open bir_envTheory;

  (* TODO: These should only be defined once in HolBA... *)
  val string_ss = rewrites (type_rws ``:string``);
  val char_ss = rewrites (type_rws ``:char``);

  val simp_conv_for_bir_var_set_is_well_typed =
      (
	(* first, convert the set to a list *)
	(RAND_CONV (REWRITE_CONV [pred_setTheory.INSERT_UNION_EQ, pred_setTheory.UNION_EMPTY]))
	THENC
	REPEATC (
	  (fn x => REWRITE_CONV [Once UNION_INSERT] x)
	  THENC (
	    (RATOR_CONV o LAND_CONV) (
	      (REWRITE_CONV [pred_setTheory.IN_INSERT])
	      THENC
	      (SIMP_CONV (std_ss++HolBACoreSimps.holBACore_ss++stringSimps.STRING_ss++string_ss++
                                  char_ss)
		[pred_setTheory.NOT_IN_EMPTY])
	    )
	  )
	) THENC
	REWRITE_CONV [pred_setTheory.UNION_EMPTY]
      ) THENC
      (REWRITE_CONV [GSYM listTheory.LIST_TO_SET])
      THENC
      (* normalize to bir_var_set_is_well_typed *)
      (REWRITE_CONV [GSYM bir_var_set_is_well_typed_EQ_bir_vs_consistent])
      THENC
      (* then, repeatedly check for inconsistency of the first list element with the rest *)
      REPEATC (
	(fn x => REWRITE_CONV [Once bir_var_set_is_well_typed_REWRS] x)
	THENC
	(LAND_CONV EVAL) THENC
	(REWRITE_CONV [])
      ) THENC
      (* and finish when the end of the list is reached *)
      (REWRITE_CONV [bir_var_set_is_well_typed_REWRS]
    );

  (*
    val s = ``{BVar "hello"  (BType_Imm Bit64);
               BVar "hello2" (BType_Imm Bit32);
               BVar "hello"  (BType_Imm Bit32);
               BVar "hello3" (BType_Imm Bit32)}``;

    val test = ``bir_var_set_is_well_typed {BVar "hello"  (BType_Imm Bit64);
               BVar "hello2" (BType_Imm Bit32);
               BVar "hello"  (BType_Imm Bit32);
               BVar "hello3" (BType_Imm Bit32)}``;
  *)
in
  fun bir_vs_consistent_prove s =
    let val t = ``bir_vs_consistent ^s`` in
      prove (t,
	REWRITE_TAC [simp_conv_for_bir_var_set_is_well_typed t]
      )
    end;
end (* local for bir_vs_consistent_prove *)

val bir_var_set_is_well_typed_ss =
  SSFRAG {ac = [],
          congs = [],
          convs = [{conv = K (K simp_conv_for_bir_var_set_is_well_typed),
                    key= SOME ([], ``bir_var_set_is_well_typed varset``),
                    name = "simp_conv_for_bir_var_set_is_well_typed",
                    trace = 2}],
          dprocs = [],
          filter = NONE,
          name = SOME "bir_var_set_is_well_typed_ss",
          rewrs = []};

SIMP_CONV (std_ss++bir_var_set_is_well_typed_ss) [] test;
