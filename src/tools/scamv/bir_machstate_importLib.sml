structure bir_machstate_importLib :> bir_machstate_importLib =
struct
open HolKernel Parse boolLib bossLib Abbrev;

local
  open wordsSyntax numSyntax pairSyntax;
  open experimentsLib;

  (* main memory name in BIR env *)
  val mem_string = “"MEM"”;

  (* defval ignored for now *)
  fun build_mem wsz defval memmap =
      let open bir_immSyntax bir_valuesSyntax finite_mapSyntax;
          val value_ty = bir_immtype_t_of_size wsz;
          val mf_empty = mk_fempty (num, num);
          fun mk_fupdate_pair (addr,v) = mk_pair(mk_numeral addr, mk_numeral v);
          val mf = 
              list_mk_fupdate (mf_empty, List.map mk_fupdate_pair memmap);
      in
        mk_BVal_Mem (Bit64_tm, value_ty, mf)
      end;

  fun build_env st regmap mem =
      let open stringSyntax bir_envSyntax bir_programSyntax;
          val (_,base_env,_) = dest_bir_state st;
          val base_envf = dest_BEnv base_env;
          fun go [] envf = envf
            | go ((regname,v)::rs) envf =
              go rs “\x. if x = ^(fromMLstring regname) then SOME (BVal_Imm (Imm64 ^(mk_wordi (v,64)))) else ^envf x”
          val regenvf = go regmap base_envf;
          val envf = “\x. if x = ^mem_string then SOME ^mem else ^regenvf x”;
      in
        mk_BEnv envf
      end;

in

fun merge_machstate_into_bir_state st machstate =
    let val (MACHSTATE (regmap, (wsz, defval, memmap))) = machstate;

        val mem = build_mem wsz defval (Redblackmap.listItems memmap);
        val env = build_env st (Redblackmap.listItems regmap) mem;
    in
      (rhs o concl) (EVAL “^st with <| bst_environ := ^env |>”)
    end;

fun merge_json_into_bir_state st =
    merge_machstate_into_bir_state st o Json_to_machstate;

(* first argument is the program (to initialise PC, etc.) *)
fun scamv_machstate_to_bir_state prog =
    merge_machstate_into_bir_state “bir_state_init ^prog”;

fun scamv_json_to_bir_state prog = scamv_machstate_to_bir_state prog o Json_to_machstate;

end
end
