## General
- Tidy code 
    - [x] Change indent to 2 spaces (or less for proofs)
    - [x] Add semicolons at the end of statements
    - [x] Clean double asterisks comment
    - [x] Add a top level comment describing each files / theories
    - Split into more directories
        - [x] Create theories directory
        - [x] Create example directories
    - [x] Add `.holpath`
- [ ] Begin presentation

## Expression semantics
- Add Examples
    
- Benchmark examples
    - [ ] `EVAL`
    - [ ] `cv_eval` with the deep embedding translation

- Tidy files
    - [ ] Name variables (like in case split)

- Add Memory expressions
    - [ ] Syntax
    - [ ] Semantics
    - [ ] Update proofs


## Statements semantics
- Add statement semantics
    - [ ] Assign / Jumps
    - [ ] Rest of the statements

## Future
- Try lifting
    - Check `examples/riscv/isqrt` for reference cf `bir_isqrt_prog_def`
    - Benchmark evaluation on those bigger programs
- Check Quotation library and apply it to smol-bir
    - Check `src/shared/bir_quotationLib.sml` and comments in it
