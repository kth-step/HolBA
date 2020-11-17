signature scamv_path_structLib =
sig
  include Abbrev;
  datatype cobs_repr = cobs of int * term * term * term;
  datatype path_repr = path of int * term * (cobs_repr list);
  type path_struct = path_repr list;

  type path_spec = {a_run: int * (bool * int) list, b_run: int * (bool * int) list};

  val extract_obs_variables: path_repr list -> term list
  val filter: (int * term -> bool) -> path_repr list -> path_repr list
  val gen_obs_ids:
      (unit -> int) -> (term * term * term) list -> cobs_repr list
  val gen_path_ids:
      (unit -> int) -> (term * (term * term * term) list) list -> path_repr list
  val get_distinct_path: int -> 'a -> path_repr list -> path_repr list
  val initialise:
   (term * (term * term * term) list option) list -> path_struct
  val lookup_obs : int -> cobs_repr list -> cobs_repr option
  val lookup_path : int -> path_repr list -> path_repr option

  val obs_domain: path_struct -> int list
  val obs_domain_path: cobs_repr list -> int list
  val path_cond_of: path_repr -> term
  val path_domain: path_struct -> int list
  val path_id_of: path_repr -> int
  val path_obs_of: path_repr -> cobs_repr list
  val cobs_id_of: cobs_repr -> int;
  val print_path_struct: path_repr list -> unit
  val stateful_tabulate: (int -> 'a) -> unit -> 'a
end
