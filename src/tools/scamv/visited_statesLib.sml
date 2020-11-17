structure visited_statesLib :> visited_statesLib =
struct

local

open HolKernel Parse boolLib;
open Redblackmap;
open bir_utilLib;

fun order2bool ord =
    case ord of
        LESS => true
      | _ => false;

fun order2eq ord =
    case ord of
        EQUAL => true
      | _ => false;

in

open bir_rel_synthLib;
type visited_map = (path_spec, term) dict;

fun path_spec_compare (pspec1:path_spec, pspec2:path_spec) =
    let val arun1 = #a_run pspec1;
        val arun2 = #a_run pspec2;
        val brun1 = #b_run pspec1;
        val brun2 = #b_run pspec2;
        fun cobs_compare (cobs1,cobs2) =
            Portable.pair_compare (Portable.bool_compare, Int.compare)
                                  (cobs1,cobs2);
        fun norm xs = nub_with (order2eq o cobs_compare)
                               (sort (curry (order2bool o cobs_compare)) xs);
        fun cobs_list_compare (xs, ys) =
            List.collate cobs_compare (norm xs, norm ys);
        val paths_compare = pair_compare (Int.compare, cobs_list_compare);
    in
      case paths_compare (arun1, arun2) of
          EQUAL => paths_compare (brun1, brun2)
        | c => c
    end;

fun init_visited () : visited_map = mkDict path_spec_compare;

fun add_visited vmap pspec t =
    let fun upd NONE = t
          | upd (SOME previous) = mk_conj (previous,t);
    in
      update (vmap,pspec,upd)
    end;

fun lookup_visited vmap pspec =
    find (vmap,pspec);

fun lookup_visited_all_paths (vmap : visited_map) =
    foldr (fn (_,conjunct,result) => mk_conj (conjunct,result)) ``T`` vmap;

fun transform_visited (vmap : visited_map) f : visited_map = transform f vmap;

end

end
