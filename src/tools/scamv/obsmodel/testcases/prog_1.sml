(* ========================= prog_1 - empty program =========================== *)

val prog_1 = ``
BirProgram []
:bir_val_t bir_program_t
``;

val prog_1_mem_address_pc = ``
BirProgram []
:bir_val_t bir_program_t
``;

val prog_1_cache_tag_index = ``
BirProgram []
:bir_val_t bir_program_t
``;

val prog_1_cache_tag_only = ``
BirProgram []
:bir_val_t bir_program_t
``;

val prog_1_cache_index_only = ``
BirProgram []
:bir_val_t bir_program_t
``;

val prog_1_cache_tag_index_part = ``
BirProgram []
:bir_val_t bir_program_t
``;

val prog_1_cache_tag_index_part_page = ``
BirProgram []
:bir_val_t bir_program_t
``;

val prog_1_cache_speculation = ``
F
``;

val prog_1_cache_speculation_first = ``
F
``;

val prog_1_test =
  ("prog_1 - empty program", prog_1,
     (prog_1_mem_address_pc,
      prog_1_cache_tag_index,
      prog_1_cache_tag_only,
      prog_1_cache_index_only,
      prog_1_cache_tag_index_part,
      prog_1_cache_tag_index_part_page,
      prog_1_cache_speculation,
      prog_1_cache_speculation_first)
  );
