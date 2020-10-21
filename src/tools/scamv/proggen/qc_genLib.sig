signature qc_genLib =
sig
    type 'a Gen;

    val return : 'a -> 'a Gen;
    val map_gen : ('a -> 'b) -> 'a Gen -> 'b Gen;
    val <$> : ('a -> 'b) * 'a Gen -> 'b Gen;
    val >>= : 'a Gen * ('a -> 'b Gen) -> 'b Gen;
    val two : 'a Gen -> 'b Gen -> ('a * 'b) Gen;
    val sequence : 'a Gen list -> 'a list Gen;
    val repeat : int -> 'a Gen -> 'a list Gen;

    val sized : (int -> 'a Gen) -> 'a Gen;
    val resize : int -> 'a Gen -> 'a Gen;
    val rand : Random.generator Gen;
    val promote : ('a -> 'b Gen) -> ('a -> 'b) Gen;
    val generate : int -> Random.generator -> 'a Gen -> 'a;
    val run_step : int -> Random.generator -> 'a Gen -> 'a * Random.generator;
    val sample : int -> int -> Random.generator -> 'a Gen -> 'a list;
    val choose : int * int -> int Gen;
    val elements : 'a list -> 'a Gen;
    val oneof : 'a Gen list -> 'a Gen;
    val frequency : (int * 'a Gen) list -> 'a Gen;
    val arb_list_of : 'a Gen -> 'a list Gen;
    val arb_option : 'a Gen -> 'a option Gen;
    val such_that : ('a -> bool) -> 'a Gen -> 'a Gen;
end
