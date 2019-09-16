signature bslSyntax =
sig

    include Abbrev

    (**************************************************************************)
    (* Term <-> BSL                                                           *)
    (**************************************************************************)

    (* Program definition (:thm)
     *
     * TODO? bdefprog: string -> ('a bir_block_t) list term -> thm
     * bdefprog_list: hol_type (* overserved type *)
     *             -> string (* program name *)
     *             -> (bir_label_t * ('a bir_stmt_basic_t) list * bir_stmt_end_t) list
     *             -> thm
     *
     * Note: `val my_prog_def = bdefprog "my_prog" blocks;` is equivalent to:
     * ```
     * val my_prog_def = Define `
     *   my_prog = BirProgram ^blocks
     * `;
     * ```
     *)
    (*val bdefprog: string -> term -> thm*)
    val bdefprog_list: hol_type -> string -> (term * term list * term) list -> thm

    (**************************************************************************)
    (* Environment                                                            *)
    (**************************************************************************)

    (* Variales (BVar: bir_var_t)
     *
     * bvar: string -> bir_type_t -> bir_var_t
     *
     * bvarimm:     int -> string -> bir_var_t
     * bvarimm1:    string -> bir_var_t
     * bvarimm8:    string -> bir_var_t
     * bvarimm16:   string -> bir_var_t
     * bvarimm32:   string -> bir_var_t
     * bvarimm64:   string -> bir_var_t
     * bvarimm128:  string -> bir_var_t
     *
     * bvarmem:         (int * int) -> string -> bir_var_t
     * bvarmem8_1:      string -> bir_var_t
     * bvarmem16_1:     string -> bir_var_t
     * bvarmem32_1:     string -> bir_var_t
     * bvarmem64_1:     string -> bir_var_t
     * bvarmem128_1:    string -> bir_var_t
     * bvarmem8_8:      string -> bir_var_t
     * bvarmem16_8:     string -> bir_var_t
     * bvarmem32_8:     string -> bir_var_t
     * bvarmem64_8:     string -> bir_var_t
     * bvarmem128_8:    string -> bir_var_t
     * bvarmem8_16:     string -> bir_var_t
     * bvarmem16_16:    string -> bir_var_t
     * bvarmem32_16:    string -> bir_var_t
     * bvarmem64_16:    string -> bir_var_t
     * bvarmem128_16:   string -> bir_var_t
     * bvarmem8_32:     string -> bir_var_t
     * bvarmem16_32:    string -> bir_var_t
     * bvarmem32_32:    string -> bir_var_t
     * bvarmem64_32:    string -> bir_var_t
     * bvarmem128_32:   string -> bir_var_t
     * bvarmem8_64:     string -> bir_var_t
     * bvarmem16_64:    string -> bir_var_t
     * bvarmem32_64:    string -> bir_var_t
     * bvarmem64_64:    string -> bir_var_t
     * bvarmem128_64:   string -> bir_var_t
     * bvarmem8_128:    string -> bir_var_t
     * bvarmem16_128:   string -> bir_var_t
     * bvarmem32_128:   string -> bir_var_t
     * bvarmem64_128:   string -> bir_var_t
     * bvarmem128_128:  string -> bir_var_t
     *)
    val bvar:           string -> term -> term

    val bvarimm:        int -> string -> term
    val bvarimm1:       string -> term
    val bvarimm8:       string -> term
    val bvarimm16:      string -> term
    val bvarimm32:      string -> term
    val bvarimm64:      string -> term
    val bvarimm128:     string -> term

    val bvarmem:        (int * int) -> string -> term
    val bvarmem8_1:     string -> term
    val bvarmem16_1:    string -> term
    val bvarmem32_1:    string -> term
    val bvarmem64_1:    string -> term
    val bvarmem128_1:   string -> term
    val bvarmem8_8:     string -> term
    val bvarmem16_8:    string -> term
    val bvarmem32_8:    string -> term
    val bvarmem64_8:    string -> term
    val bvarmem128_8:   string -> term
    val bvarmem8_16:    string -> term
    val bvarmem16_16:   string -> term
    val bvarmem32_16:   string -> term
    val bvarmem64_16:   string -> term
    val bvarmem128_16:  string -> term
    val bvarmem8_32:    string -> term
    val bvarmem16_32:   string -> term
    val bvarmem32_32:   string -> term
    val bvarmem64_32:   string -> term
    val bvarmem128_32:  string -> term
    val bvarmem8_64:    string -> term
    val bvarmem16_64:   string -> term
    val bvarmem32_64:   string -> term
    val bvarmem64_64:   string -> term
    val bvarmem128_64:  string -> term
    val bvarmem8_128:   string -> term
    val bvarmem16_128:  string -> term
    val bvarmem32_128:  string -> term
    val bvarmem64_128:  string -> term
    val bvarmem128_128: string -> term

    (**************************************************************************)
    (* Program                                                                *)
    (**************************************************************************)

    (* Labels (:bir_label_t)
     *
     * blabel_str: string -> bir_label_t
     *
     * Notes:
     *  - blabel_addr handles words of a valid size, booleans and list of
     *    booleans of supported length (it uses bir_immSyntax.gen_mk_Imm).
     *
     * blabel_addr: bool_t       -> bir_label_t
     * blabel_addr: bool_t list  -> bir_label_t
     * blabel_addr: 'a word_t    -> bir_label_t
     *
     * blabel_addr1:    int -> bir_label_t
     * blabel_addr8:    int -> bir_label_t
     * blabel_addr16:   int -> bir_label_t
     * blabel_addr32:   int -> bir_label_t
     * blabel_addr64:   int -> bir_label_t
     * blabel_addr128:  int -> bir_label_t
     *
     * blabel_addrii:   int (length) -> int (value) -> bir_label_t
     * blabel_addrimm:  bir_imm_t -> bir_label_t
     *)
    val blabel_str:       string -> term
    val blabel_addr:      term -> term
    val blabel_addr1:     int -> term
    val blabel_addr8:     int -> term
    val blabel_addr16:    int -> term
    val blabel_addr32:    int -> term
    val blabel_addr64:    int -> term
    val blabel_addr128:   int -> term
    val blabel_addrii:    int -> int -> term
    val blabel_addrimm:   term -> term
    val blabel_addr_s:    term -> string -> term
    val blabel_addr1_s:   int -> string -> term
    val blabel_addr8_s:   int -> string -> term
    val blabel_addr16_s:  int -> string -> term
    val blabel_addr32_s:  int -> string -> term
    val blabel_addr64_s:  int -> string -> term
    val blabel_addr128_s: int -> string -> term
    val blabel_addrii_s:  int -> int -> string -> term
    val blabel_addrimm_s: term -> string -> term

    (* Label expressions (:bir_label_exp_t)
     *
     * belabel:       bir_label_t -> bir_label_exp_t
     * belabel_expr:  bir_exp_t -> bir_label_exp_t
     *
     * The following are the same than bir_label_t-producing ones, but produce
     * bir_label_exp_t instead.
     *
     * belabel_str: string -> bir_label_exp_t
     *
     * belabel_addr: bool_t       -> bir_label_exp_t
     * belabel_addr: bool_t list  -> bir_label_exp_t
     * belabel_addr: 'a word_t    -> bir_label_exp_t
     *
     * belabel_addr1:   int -> bir_label_exp_t
     * belabel_addr8:   int -> bir_label_exp_t
     * belabel_addr16:  int -> bir_label_exp_t
     * belabel_addr32:  int -> bir_label_exp_t
     * belabel_addr64:  int -> bir_label_exp_t
     * belabel_addr128: int -> bir_label_exp_t
     *
     * belabel_addrii:  int (length) -> int (value) -> bir_label_exp_t
     * belabel_addrimm: bir_imm_t -> bir_label_exp_t
     *)
    val belabel: term -> term
    val belabel_expr: term -> term

    val belabel_str:        string -> term
    val belabel_addr:       term -> term
    val belabel_addr1:      int -> term
    val belabel_addr8:      int -> term
    val belabel_addr16:     int -> term
    val belabel_addr32:     int -> term
    val belabel_addr64:     int -> term
    val belabel_addr128:    int -> term
    val belabel_addrii:     int -> int -> term
    val belabel_addrimm:    term -> term
    val belabel_addr_s:     term -> string -> term
    val belabel_addr1_s:    int -> string -> term
    val belabel_addr8_s:    int -> string -> term
    val belabel_addr16_s:   int -> string -> term
    val belabel_addr32_s:   int -> string -> term
    val belabel_addr64_s:   int -> string -> term
    val belabel_addr128_s:  int -> string -> term
    val belabel_addrii_s:   int -> int -> string -> term
    val belabel_addrimm_s:  term -> string -> term

    (* Basic statements (:bir_stmt_basic_t)
     * | BStmt_Assign     => bassign
     * | BStmt_Assert     => bassert
     * | BStmt_Assume     => bassume
     * | BStmt_Observe    => TODO
     *
     * bassign:   (bir_var_t * bir_exp_t) -> bir_stmt_basic_t
     * bassert:   bir_exp_t -> bir_stmt_basic_t
     * bassume:   bir_exp_t -> bir_stmt_basic_t
     *
     * Note: BStmt_Observe hasn't been added due to lack of use case. Please add
     * it if you need it. In the meantime, use bir_programSyntax.
     *)
    val bassign: (term * term) -> term
    val bassert: term -> term
    val bassume: term -> term

    (* End statements (:bir_stmt_end_t)
     * | BStmt_Jmp        => bjmp
     * | BStmt_CJmp       => bcjmp
     * | BStmt_Halt       => bhalt
     *
     * bjmp:  bir_label_exp_t -> bir_stmt_end_t
     * bcjmp: (bir_exp_t * bir_label_exp_t * bir_label_exp_t) -> bir_stmt_end_t
     * bhalt: bir_exp_t -> bir_stmt_end_t
     *)
    val bjmp: term -> term
    val bcjmp: (term * term * term) -> term
    val bhalt: term -> term

    (* Statements (:bir_stmt_t)
     * | BStmtB         => bstmtb
     * | BStmtE         => bstmte
     *
     * bstmtb: ('a bir_stmt_basic_t) -> bir_stmt_t
     * bstmte: bir_stmt_end_t -> bir_stmt_t
     *)
    val bstmtb: term -> term
    val bstmte: term -> term

    (* Blocks (:bir_block_t)
     *
     * bblock: hol_type (* the observed type *)
     *      -> (bir_label_t * ('a bir_stmt_basic_t) list * bir_stmt_end_t)
     *      -> bir_block_t
     *
     * Note: If you don't use BStmt_Observe, use any hol_type, or just 'a.
     *)
    val bblock:   hol_type -> (term * term list * term) -> term
    val bblocks:  hol_type -> (term * term list * term) list -> term

    (* Programs (:bir_program_t)
     *
     * TODO? bprog: ('a bir_block_t) list term -> bir_program_t
     * bprog_list: hol_type
     *          -> (bir_label_t * ('a bir_stmt_basic_t) list * bir_stmt_end_t) list
     *          -> bir_program_t
     *)
    (*val bprog: term -> term*)
    val bprog_list: hol_type -> (term * term list * term) list -> term

    (**************************************************************************)
    (* Expressions (Datatype `bir_exp_t`)                                     *)
    (**************************************************************************)

    (* Constants (BExp_Const: bir_exp_t)
     *
     * Notes:
     *  - bconst handles words of a valid size, booleans and list of booleans of
     *    supported length (it uses bir_immSyntax.gen_mk_Imm).
     *  - bconstimm and bconstii will fail if the word lenght isn't supported
     *    in BIR.
     *
     * bconst:    bool_t       -> bir_exp_t
     * bconst:    bool_t list  -> bir_exp_t
     * bconst:    'a word_t    -> bir_exp_t
     *
     * bconst1:   int -> bir_exp_t
     * bconst8:   int -> bir_exp_t
     * bconst16:  int -> bir_exp_t
     * bconst32:  int -> bir_exp_t
     * bconst64:  int -> bir_exp_t
     * bconst128: int -> bir_exp_t
     *
     * bconstii:  int (length) -> int (value) -> bir_exp_t
     * bconstimm: bir_imm_t -> bir_exp_t
     *
     * btrue:     bir_exp_t
     * bfalse:    bir_exp_t
     *)
    val bconst:     term -> term

    val bconst1:    int -> term
    val bconst8:    int -> term
    val bconst16:   int -> term
    val bconst32:   int -> term
    val bconst64:   int -> term
    val bconst128:  int -> term

    val bconstii:   int -> int -> term
    val bconstimm:  term -> term

    val btrue:      term
    val bfalse:     term

    (* Memory constants (BExp_MemConst: bir_exp_t)
     *
     * Notes:
     *  - bconstmem takes an address type length, a value type
     *    length and a list of key-value pairs to build up a
     *    finite map using FUPDATE and FEMPTY. The address and
     *    value sizes have to be supported by BIR.
     *
     * bconstmemii:  int (address type) -> int (value type) ->
                       (int * int) list -> bir_exp_t
     *)

    val bconstmemii: int -> int -> (int * int) list -> term

    (* Den (BExp_Den: bir_exp_t)
     *
     * bden: bir_var_t -> bir_exp_t
     *)
    val bden: term -> term

    (* Casts (BExp_Cast: bir_exp_t)
     * | BIExp_UnsignedCast   => BIExp_UnsignedCast_tm
     * | BIExp_SignedCast     => BIExp_SignedCast_tm
     * | BIExp_HighCast       => BIExp_HighCast_tm
     * | BIExp_LowCast        => BIExp_LowCast_tm
     *
     * bcast:     bir_cast_t -> bir_immtype_t -> bir_exp_t -> bir_exp_t
     * bcasti:    bir_cast_t -> int           -> bir_exp_t -> bir_exp_t
     * bcast1:    bir_cast_t                  -> bir_exp_t -> bir_exp_t
     * bcast8:    bir_cast_t                  -> bir_exp_t -> bir_exp_t
     * bcast16:   bir_cast_t                  -> bir_exp_t -> bir_exp_t
     * bcast32:   bir_cast_t                  -> bir_exp_t -> bir_exp_t
     * bcast64:   bir_cast_t                  -> bir_exp_t -> bir_exp_t
     * bcast128:  bir_cast_t                  -> bir_exp_t -> bir_exp_t
     *
     * bucast:                  bir_immtype_t -> bir_exp_t -> bir_exp_t
     * bucasti:                 int           -> bir_exp_t -> bir_exp_t
     * bucast1:                                  bir_exp_t -> bir_exp_t
     * bucast8:                                  bir_exp_t -> bir_exp_t
     * bucast16:                                 bir_exp_t -> bir_exp_t
     * bucast32:                                 bir_exp_t -> bir_exp_t
     * bucast64:                                 bir_exp_t -> bir_exp_t
     * bucast128:                                bir_exp_t -> bir_exp_t
     *
     * bscast:                  bir_immtype_t -> bir_exp_t -> bir_exp_t
     * bscasti:                 int           -> bir_exp_t -> bir_exp_t
     * bscast1:                                  bir_exp_t -> bir_exp_t
     * bscast8:                                  bir_exp_t -> bir_exp_t
     * bscast16:                                 bir_exp_t -> bir_exp_t
     * bscast32:                                 bir_exp_t -> bir_exp_t
     * bscast64:                                 bir_exp_t -> bir_exp_t
     * bscast128:                                bir_exp_t -> bir_exp_t
     *
     * bhighcast:               bir_immtype_t -> bir_exp_t -> bir_exp_t
     * bhighcasti:              bint          -> bir_exp_t -> bir_exp_t
     * bhighcast1:                               bir_exp_t -> bir_exp_t
     * bhighcast8:                               bir_exp_t -> bir_exp_t
     * bhighcast16:                              bir_exp_t -> bir_exp_t
     * bhighcast32:                              bir_exp_t -> bir_exp_t
     * bhighcast64:                              bir_exp_t -> bir_exp_t
     * bhighcast128:                             bir_exp_t -> bir_exp_t
     *
     * blowcast:                bir_immtype_t -> bir_exp_t -> bir_exp_t
     * blowcasti:               int           -> bir_exp_t -> bir_exp_t
     * blowcast1:                                bir_exp_t -> bir_exp_t
     * blowcast8:                                bir_exp_t -> bir_exp_t
     * blowcast16:                               bir_exp_t -> bir_exp_t
     * blowcast32:                               bir_exp_t -> bir_exp_t
     * blowcast64:                               bir_exp_t -> bir_exp_t
     * blowcast128:                              bir_exp_t -> bir_exp_t
     *)
    val bcast: term -> term -> term -> term
    val bcasti: term -> int -> term -> term
    val bcast1: term -> term -> term
    val bcast8: term -> term -> term
    val bcast16: term -> term -> term
    val bcast32: term -> term -> term
    val bcast64: term -> term -> term
    val bcast128: term -> term -> term
    
    val bucast: term -> term -> term
    val bucasti: int -> term -> term
    val bucast1: term -> term
    val bucast8: term -> term
    val bucast16: term -> term
    val bucast32: term -> term
    val bucast64: term -> term
    val bucast128: term -> term
    
    val bscast: term -> term -> term
    val bscasti: int -> term -> term
    val bscast1: term -> term
    val bscast8: term -> term
    val bscast16: term -> term
    val bscast32: term -> term
    val bscast64: term -> term
    val bscast128: term -> term
    
    val bhighcast: term -> term -> term
    val bhighcasti: int -> term -> term
    val bhighcast1: term -> term
    val bhighcast8: term -> term
    val bhighcast16: term -> term
    val bhighcast32: term -> term
    val bhighcast64: term -> term
    val bhighcast128: term -> term
    
    val blowcast: term -> term -> term
    val blowcasti: int -> term -> term
    val blowcast1: term -> term
    val blowcast8: term -> term
    val blowcast16: term -> term
    val blowcast32: term -> term
    val blowcast64: term -> term
    val blowcast128: term -> term

    (* Unary expressions (BExp_UnaryExp: bir_exp_t)
     * | BIExp_ChangeSign => bchsign
     * | BIExp_Not        => bnot
     * | BIExp_CLZ        => bclz
     * | BIExp_CLS        => bcls
     *
     * bunexp: bir_unary_exp_t -> bir_exp_t -> bir_exp_t
     *
     * bchsign: bir_exp_t -> bir_exp_t
     * bnot: bir_exp_t -> bir_exp_t
     * bclz: bir_exp_t -> bir_exp_t
     * bcls: bir_exp_t -> bir_exp_t
     *)
    val bunexp:   term -> term -> term
    val bchsign:  term -> term
    val bnot:     term -> term
    val bclz:     term -> term
    val bcls:     term -> term

    (* Binary expressions (BExp_BinExp: bir_exp_t)
     * | BIExp_And              => band bandl
     * | BIExp_Or               => bor borl
     * | BIExp_Xor              => bxor bxorl
     * | BIExp_Plus             => bplus bplusl
     * | BIExp_Minus            => bminus bminusl
     * | BIExp_Mult             => bmult bmultl
     * | BIExp_Div              => bdiv bdivl
     * | BIExp_SignedDiv        => bsdiv bsdivl
     * | BIExp_Mod              => bmod bmodl
     * | BIExp_SignedMod        => bsmod bsmodl
     * | BIExp_LeftShift        => blshift blshiftl
     * | BIExp_RightShift       => brshift brshiftl
     * | BIExp_SignedRightShift => bsrshift bsrshiftl
     *
     * bbinexp:      bir_bin_exp_t -> (bir_exp_t * bir_exp_t) -> bir_exp_t
     * bbinexpl:     bir_bin_exp_t -> bir_exp_t list          -> bir_exp_t
     *
     * band:        (bir_exp_t * bir_exp_t) -> bir_exp_t
     * bor:         (bir_exp_t * bir_exp_t) -> bir_exp_t
     * bxor:        (bir_exp_t * bir_exp_t) -> bir_exp_t
     * bplus:       (bir_exp_t * bir_exp_t) -> bir_exp_t
     * bminus:      (bir_exp_t * bir_exp_t) -> bir_exp_t
     * bmult:       (bir_exp_t * bir_exp_t) -> bir_exp_t
     * bdiv:        (bir_exp_t * bir_exp_t) -> bir_exp_t
     * bsdiv:       (bir_exp_t * bir_exp_t) -> bir_exp_t
     * bmod:        (bir_exp_t * bir_exp_t) -> bir_exp_t
     * bsmod:       (bir_exp_t * bir_exp_t) -> bir_exp_t
     * blshift:     (bir_exp_t * bir_exp_t) -> bir_exp_t
     * brshift:     (bir_exp_t * bir_exp_t) -> bir_exp_t
     * bsrshift:    (bir_exp_t * bir_exp_t) -> bir_exp_t

     * bandl:       bir_exp_t list -> bir_exp_t
     * borl:        bir_exp_t list -> bir_exp_t
     * bxorl:       bir_exp_t list -> bir_exp_t
     * bplusl:      bir_exp_t list -> bir_exp_t
     * bminusl:     bir_exp_t list -> bir_exp_t
     * bmultl:      bir_exp_t list -> bir_exp_t
     * bdivl:       bir_exp_t list -> bir_exp_t
     * bsdivl:      bir_exp_t list -> bir_exp_t
     * bmodl:       bir_exp_t list -> bir_exp_t
     * bsmodl:      bir_exp_t list -> bir_exp_t
     * blshiftl:    bir_exp_t list -> bir_exp_t
     * brshiftl:    bir_exp_t list -> bir_exp_t
     * bsrshiftl:   bir_exp_t list -> bir_exp_t
     *)
    val bbinexp:    term -> (term * term) -> term
    val bbinexpl:   term -> term list -> term

    val band:       (term * term) -> term
    val bor:        (term * term) -> term
    val bxor:       (term * term) -> term
    val bplus:      (term * term) -> term
    val bminus:     (term * term) -> term
    val bmult:      (term * term) -> term
    val bdiv:       (term * term) -> term
    val bsdiv:      (term * term) -> term
    val bmod:       (term * term) -> term
    val bsmod:      (term * term) -> term
    val blshift:    (term * term) -> term
    val brshift:    (term * term) -> term
    val bsrshift:   (term * term) -> term

    val bandl:      term list -> term
    val borl:       term list -> term
    val bxorl:      term list -> term
    val bplusl:     term list -> term
    val bminusl:    term list -> term
    val bmultl:     term list -> term
    val bdivl:      term list -> term
    val bsdivl:     term list -> term
    val bmodl:      term list -> term
    val bsmodl:     term list -> term
    val blshiftl:   term list -> term
    val brshiftl:   term list -> term
    val bsrshiftl:  term list -> term

    (* Binary predicates (BExp_BinPred: bir_exp_t)
     * | BIExp_Equal                => beq beql
     * | BIExp_NotEqual             => bneq bneql
     * | BIExp_LessThan             => blt bltl
     * | BIExp_SignedLessThan       => bslt bsltl
     * | BIExp_LessOrEqual          => ble blel
     * | BIExp_SignedLessOrEqual    => bsle bslel
     *
     * Note: list versions `bxxxl` will generate conjunctions of `bxxx`.
     *
     * bbinpred:    bir_bin_pred_t -> (bir_exp_t * bir_exp_t) -> bir_exp_t
     * bbinpredl:   bir_bin_pred_t -> bir_exp_t list          -> bir_exp_t
     *
     * beq:         (bir_exp_t * bir_exp_t) -> bir_exp_t
     * bneq:        (bir_exp_t * bir_exp_t) -> bir_exp_t
     * blt:         (bir_exp_t * bir_exp_t) -> bir_exp_t
     * bslt:        (bir_exp_t * bir_exp_t) -> bir_exp_t
     * ble:         (bir_exp_t * bir_exp_t) -> bir_exp_t
     * bsle:        (bir_exp_t * bir_exp_t) -> bir_exp_t
     *
     * beql:        bir_exp_t list -> bir_exp_t
     * bneql:       bir_exp_t list -> bir_exp_t
     * bltl:        bir_exp_t list -> bir_exp_t
     * bsltl:       bir_exp_t list -> bir_exp_t
     * blel:        bir_exp_t list -> bir_exp_t
     * bslel:       bir_exp_t list -> bir_exp_t
     *
     * # BSL sugar:
     * bgt:         (bir_exp_t * bir_exp_t) -> bir_exp_t
     * bsgt:        (bir_exp_t * bir_exp_t) -> bir_exp_t
     * bge:         (bir_exp_t * bir_exp_t) -> bir_exp_t
     * bsge:        (bir_exp_t * bir_exp_t) -> bir_exp_t
     *
     * bgtl:        bir_exp_t list -> bir_exp_t
     * bsgtl:       bir_exp_t list -> bir_exp_t
     * bgel:        bir_exp_t list -> bir_exp_t
     * bsgel:       bir_exp_t list -> bir_exp_t
     *)
    val bbinpred:   term -> (term * term) -> term
    val bbinpredl:  term -> term list -> term

    val beq:        (term * term) -> term
    val bneq:       (term * term) -> term
    val blt:        (term * term) -> term
    val bslt:       (term * term) -> term
    val ble:        (term * term) -> term
    val bsle:       (term * term) -> term

    val beql:       term list -> term
    val bneql:      term list -> term
    val bltl:       term list -> term
    val bsltl:      term list -> term
    val blel:       term list -> term
    val bslel:      term list -> term

    val bgt:        (term * term) -> term
    val bsgt:       (term * term) -> term
    val bge:        (term * term) -> term
    val bsge:       (term * term) -> term

    val bgtl:       term list -> term
    val bsgtl:      term list -> term
    val bgel:       term list -> term
    val bsgel:      term list -> term

    (* Memory equality (BExp_MemEq: bir_exp_t)
     *
     * bmemeq: (bir_exp_t * bir_exp_t) -> bir_exp_t
     *)
    val bmemeq: (term * term) -> term

    (* Conditionals (BExp_IfThenElse: bir_exp_t)
     *
     * If-Then-Else:
     *  - bite: (bir_exp_t * bir_exp_t * bir_exp_t) -> bir_exp_t
     *
     * Cases: list of conditions tested in order, stopping at the first match
     *  - bcases: (bir_exp_t * bir_exp_t) list -> bir_exp_t -> bir_exp_t
     *
     * Example: This will evaluate to `bconstii 32 1`, and only the first two
     * comparisons will be executed (lazy evaluation).
     * ```
     * bcases [
     *   (beq (bconst8 2) (bconst8 4), bconst32 0),
     *   (beq (bconst32 3) (bconst32 3), bconst32 1),
     *   (beq (bconst128 7) (bconst128 7), bconst32 2),
     *   bconst32 100
     * ]
     * ```
     *)
    val bite:   (term * term * term) -> term
    val bcases: (term * term) list -> term -> term

    (* Memory loads (BExp_Load: bir_exp_t)
     *
     * bload: bir_exp_t     (* the memory to load from *)
     *     -> bir_exp_t     (* the address *)
     *     -> bir_endian_t  (* the endianness *)
     *     -> bir_immtype_t (* the type of the value to load *)
     *     -> bir_exp_t     (* the loaded value *)
     *
     * Specializations:
     *  - `_le` stands for Little Endian
     *  - `_be` stands for Big Endian
     *  - `_ne` stands for No Endian
     *  - `nn` specializes the length of the loaded value
     *
     * bloadi:    bir_exp_t -> bir_exp_t -> bir_endian_t -> int -> bir_exp_t
     * bloadi_le: bir_exp_t -> bir_exp_t -> int -> bir_exp_t
     * bloadi_be: bir_exp_t -> bir_exp_t -> int -> bir_exp_t
     * bloadi_ne: bir_exp_t -> bir_exp_t -> int -> bir_exp_t
     *
     * bload1:    bir_exp_t -> bir_exp_t -> bir_endian_t -> bir_exp_t
     * bload8:    bir_exp_t -> bir_exp_t -> bir_endian_t -> bir_exp_t
     * bload16:   bir_exp_t -> bir_exp_t -> bir_endian_t -> bir_exp_t
     * bload32:   bir_exp_t -> bir_exp_t -> bir_endian_t -> bir_exp_t
     * bload64:   bir_exp_t -> bir_exp_t -> bir_endian_t -> bir_exp_t
     * bload128:  bir_exp_t -> bir_exp_t -> bir_endian_t -> bir_exp_t
     *
     * bload_le:    bir_exp_t -> bir_exp_t -> bir_immtype_t-> bir_exp_t
     * bload1_le:   bir_exp_t -> bir_exp_t -> bir_exp_t
     * bload8_le:   bir_exp_t -> bir_exp_t -> bir_exp_t
     * bload16_le:  bir_exp_t -> bir_exp_t -> bir_exp_t
     * bload32_le:  bir_exp_t -> bir_exp_t -> bir_exp_t
     * bload64_le:  bir_exp_t -> bir_exp_t -> bir_exp_t
     * bload128_le: bir_exp_t -> bir_exp_t -> bir_exp_t
     *
     * bload_be:    bir_exp_t -> bir_exp_t -> bir_immtype_t-> bir_exp_t
     * bload1_be:   bir_exp_t -> bir_exp_t -> bir_exp_t
     * bload8_be:   bir_exp_t -> bir_exp_t -> bir_exp_t
     * bload16_be:  bir_exp_t -> bir_exp_t -> bir_exp_t
     * bload32_be:  bir_exp_t -> bir_exp_t -> bir_exp_t
     * bload64_be:  bir_exp_t -> bir_exp_t -> bir_exp_t
     * bload128_be: bir_exp_t -> bir_exp_t -> bir_exp_t
     *
     * bload_ne:  bir_exp_t -> bir_exp_t -> bir_immtype_t-> bir_exp_t
     * bload1_ne: bir_exp_t -> bir_exp_t -> bir_exp_t
     * bload8_ne: bir_exp_t -> bir_exp_t -> bir_exp_t
     *)
    val bload:    term -> term -> term -> term -> term
    val bloadi:   term -> term -> term -> int -> term
    val bload1:   term -> term -> term -> term
    val bload8:   term -> term -> term -> term
    val bload16:  term -> term -> term -> term
    val bload32:  term -> term -> term -> term
    val bload64:  term -> term -> term -> term
    val bload128: term -> term -> term -> term

    val bload_le:     term -> term -> term -> term
    val bloadi_le:    term -> term -> int -> term
    val bload1_le:    term -> term -> term
    val bload8_le:    term -> term -> term
    val bload16_le:   term -> term -> term
    val bload32_le:   term -> term -> term
    val bload64_le:   term -> term -> term
    val bload128_le:  term -> term -> term

    val bload_be:     term -> term -> term -> term
    val bloadi_be:    term -> term -> int -> term
    val bload1_be:    term -> term -> term
    val bload8_be:    term -> term -> term
    val bload16_be:   term -> term -> term
    val bload32_be:   term -> term -> term
    val bload64_be:   term -> term -> term
    val bload128_be:  term -> term -> term

    val bload_ne:   term -> term -> term -> term
    val bloadi_ne:  term -> term -> int -> term
    val bload1_ne:  term -> term -> term
    val bload8_ne:  term -> term -> term

    (* Memory stores (BExp_Store: bir_exp_t)
     *
     * bstore: bir_exp_t    (* the initial memory *)
     *      -> bir_exp_t     (* the address *)
     *      -> bir_endian_t  (* the endianness *)
     *      -> bir_exp_t     (* the value to store *)
     *      -> bir_exp_t     (* the new memory *)
     *
     * Specializations:
     *  - `_le` stands for Little Endian
     *  - `_be` stands for Big Endian
     *  - `_ne` stands for No Endian
     *
     * bstore_le: bir_exp_t -> bir_exp_t -> bir_exp_t -> bir_exp_t
     * bstore_be: bir_exp_t -> bir_exp_t -> bir_exp_t -> bir_exp_t
     * bstore_ne: bir_exp_t -> bir_exp_t -> bir_exp_t -> bir_exp_t
     *)
     val bstore:    term -> term -> term -> term -> term
     val bstore_le: term -> term -> term -> term
     val bstore_be: term -> term -> term -> term
     val bstore_ne: term -> term -> term -> term

    (* Extra expressions (:bir_exp_t)
     * | BExp_Align                   => balign
     * | BExp_Aligned                 => baligned
     * | BExp_word_reverse_1_8        => bword_reverse_1_8
     * | BExp_word_reverse_1_16       => bword_reverse_1_16
     * | BExp_word_reverse_1_32       => bword_reverse_1_32
     * | BExp_word_reverse_1_64       => bword_reverse_1_64
     * | BExp_word_reverse_1_128      => bword_reverse_1_128
     * | BExp_word_reverse_8_16       => bword_reverse_8_16
     * | BExp_word_reverse_8_32       => bword_reverse_8_32
     * | BExp_word_reverse_8_64       => bword_reverse_8_64
     * | BExp_word_reverse_8_128      => bword_reverse_8_128
     * | BExp_word_reverse_16_32      => bword_reverse_16_32
     * | BExp_word_reverse_16_64      => bword_reverse_16_64
     * | BExp_word_reverse_16_128     => bword_reverse_16_128
     * | BExp_word_reverse_32_64      => bword_reverse_32_64
     * | BExp_word_reverse_32_128     => bword_reverse_32_128
     * | BExp_word_reverse_64_128     => bword_reverse_64_128
     * | BExp_MSB                     => bmsb
     * | BExp_LSB                     => blsb
     * | BExp_word_bit                => bword_bit
     * | BExp_word_bit_exp            => bword_bit_exp
     * | BExp_ror_exp                 => bror_exp
     * | BExp_ror                     => bror
     * | BExp_rol_exp                 => brol_exp
     * | BExp_rol                     => brol
     * | BExp_extr                    => bextr
     *
     * Note: In the following, `num` have types `int` for ease of use, but they
     * must be positive.
     *
     * balign:    (bir_immtype_t * num) -> bir_exp_t
     * baligned:  (bir_immtype_t * num) -> bir_exp_t
     *
     * bword_reverse_1_8:     bir_exp_t -> bir_exp_t
     * bword_reverse_1_16:    bir_exp_t -> bir_exp_t
     * bword_reverse_1_32:    bir_exp_t -> bir_exp_t
     * bword_reverse_1_64:    bir_exp_t -> bir_exp_t
     * bword_reverse_1_128:   bir_exp_t -> bir_exp_t
     * bword_reverse_8_16:    bir_exp_t -> bir_exp_t
     * bword_reverse_8_32:    bir_exp_t -> bir_exp_t
     * bword_reverse_8_64:    bir_exp_t -> bir_exp_t
     * bword_reverse_8_128:   bir_exp_t -> bir_exp_t
     * bword_reverse_16_32:   bir_exp_t -> bir_exp_t
     * bword_reverse_16_64:   bir_exp_t -> bir_exp_t
     * bword_reverse_16_128:  bir_exp_t -> bir_exp_t
     * bword_reverse_32_64:   bir_exp_t -> bir_exp_t
     * bword_reverse_32_128:  bir_exp_t -> bir_exp_t
     * bword_reverse_64_128:  bir_exp_t -> bir_exp_t
     *
     * bmsb:  (bir_immtype_t * bir_exp_t) -> bir_exp_t
     * blsb:  (bir_immtype_t * bir_exp_t) -> bir_exp_t
     *
     * bword_bit:     (bir_immtype_t * bir_exp_t * num) -> bir_exp_t
     * bword_bit_exp: (bir_immtype_t * bir_exp_t * bir_exp_t) -> bir_exp_t
     *
     * bror:      (bir_immtype_t * bir_exp_t * num) -> bir_exp_t
     * bror_exp:  (bir_immtype_t * bir_exp_t * bir_exp_t) -> bir_exp_t
     *
     * brol:      (bir_immtype_t * bir_exp_t * num) -> bir_exp_t
     * brol_exp:  (bir_immtype_t * bir_exp_t * bir_exp_t) -> bir_exp_t
     *
     * bextr: (bir_immtype_t * bir_exp_t * bir_exp_t * bir_exp_t) -> bir_exp_t
     *)
    val balign:    term -> (term * term) -> term
    val baligni:    int -> (term * term) -> term
    val baligned:  term -> (term * term) -> term
    val balignedi:  int -> (term * term) -> term

    val bword_reverse_1_8:     term -> term
    val bword_reverse_1_16:    term -> term
    val bword_reverse_1_32:    term -> term
    val bword_reverse_1_64:    term -> term
    val bword_reverse_1_128:   term -> term
    val bword_reverse_8_16:    term -> term
    val bword_reverse_8_32:    term -> term
    val bword_reverse_8_64:    term -> term
    val bword_reverse_8_128:   term -> term
    val bword_reverse_16_32:   term -> term
    val bword_reverse_16_64:   term -> term
    val bword_reverse_16_128:  term -> term
    val bword_reverse_32_64:   term -> term
    val bword_reverse_32_128:  term -> term
    val bword_reverse_64_128:  term -> term

    val bmsb:  term -> term -> term
    val bmsbi: int  -> term -> term
    val blsb:  term -> term

    val bword_bit:      term -> (term * term) -> term
    val bword_biti:     int  -> (term * term) -> term
    val bword_bit_exp:  term -> (term * term) -> term
    val bword_bit_expi: int  -> (term * term) -> term

    val bror:      term -> (term * term) -> term
    val brori:     int  -> (term * term) -> term
    val bror_exp:  term -> (term * term) -> term
    val bror_expi: int  -> (term * term) -> term

    val brol:      term -> (term * term) -> term
    val broli:     int  -> (term * term) -> term
    val brol_exp:  term -> (term * term) -> term
    val brol_expi: int  -> (term * term) -> term

    val bextr:  term -> (term * term * term) -> term
    val bextri: int  -> (term * term * term) -> term

end (* bslLib *)
