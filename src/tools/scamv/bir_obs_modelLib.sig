signature OBS_MODEL =
    sig
        val obs_hol_type : term

        (* In HOL: 'a bir_program_t -> obs_hol_type bir_program_t *)
        val add_obs : term -> term
    end

