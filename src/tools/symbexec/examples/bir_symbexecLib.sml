structure bir_symbexecLib =
struct

datatype symb_state =
  SymbState of {
      SYST_env  : ((string * term) * term) list,
      SYST_pred : term list,
      SYST_pc : term
    };

fun SYST_get_env (SymbState systr) =
  #SYST_env systr;
fun SYST_get_pred (SymbState systr) =
  #SYST_pred systr;
fun SYST_get_pc (SymbState systr) =
  #SYST_pc systr;

fun SYST_update_env env' (SymbState systr) =
  SymbState {SYST_env  = env',
             SYST_pred = #SYST_pred systr,
             SYST_pc   = #SYST_pc systr };
fun SYST_update_pred pred' (SymbState systr) =
  SymbState {SYST_env  = #SYST_env systr,
             SYST_pred = pred',
             SYST_pc   = #SYST_pc systr };
fun SYST_update_pc pc' (SymbState systr) =
  SymbState {SYST_env  = #SYST_env systr,
             SYST_pred = #SYST_pred systr,
             SYST_pc   = pc' };

fun SYST_mk env pred pc =
  SymbState {SYST_env  = env,
             SYST_pred = pred,
             SYST_pc   = pc };

local

  open bir_constpropLib;

in (* local *)

end (* local *)
end (* struct *)
