structure armv8_prefetch_genLib : armv8_prefetch_genLib =
struct

open asm_genLib;
infix 5 <$>;
infix 5 >>=;

val total_sets = 128;
(* fun tag_set_to_addr (tag, set) =
   tag * 64 * total_sets + set * 64;
fun tag_of x = x div total_sets div 64; *)
fun set_of x = (x div 64) mod total_sets;
fun offset_of (x,n) = 64*(set_of (x) + n);

fun mk_preamble_of reg1 reg2 reg3 =
    ["lsl " ^ reg1 ^ ", " ^ reg1 ^ ", 7"
    ,"add " ^ reg2 ^ ", " ^ reg1 ^ ", " ^ reg2
    ,"lsl " ^ reg3 ^ ", " ^ reg2 ^ ", 6"] (* addr is in reg3 *)
fun arb_regname_except xs =
    such_that (fn r => not (exists (fn x => x = r) xs)) arb_armv8_regname;

fun arb_ld_offset reg offset =
    arb_regname_except [reg] >>= (fn target =>
    return (Load (Reg target, Ld (SOME offset, reg))));

fun arb_stride stride_step =
    let fun go 0 = [0]
          | go i =  (64*i*stride_step) :: go (i-1)
        fun offsets stride_length = rev (go stride_length);
    in
        choose (1,4) >>= (fn l =>
        repeat 3 (arb_regname_except ["x1", "x0"]) >>= (fn [reg1,reg2,reg3] =>
        sequence (map (arb_ld_offset reg3) (offsets l)) >>= (fn result =>
        return (result, [reg1,reg2,reg3])
        )))
    end

val arb_stride_lds =
    elements [1,2,3,4] >>= arb_stride

local
    open Random;
    val fresh_seed = false;
    val g = ref (if fresh_seed
                 then newgen ()
                 else newgenseed 3141592.654);
in
fun prog_gen_prefetch_stride n =
    let val ((p,[reg1,reg2,reg3]), rnd) = run_step n (!g) arb_stride_lds;
        val _ = (g := rnd);
    in
       (* mk_preamble_of reg1 reg2 reg3 @ *) pp_program p
    end
end

end
