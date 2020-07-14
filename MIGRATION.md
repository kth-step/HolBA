# HolBA Kananaskis-13 Migration notes

## Biggest changes relevant to HolBA (from Kananaskis-12)

* Theorem names:
  - rich_listTheory:
    
    COUNT_LIST_AUX_def_compute 
    becomes
    COUNT_LIST_AUX_compute
    
    SEG_TAKE_BUTFISTN
    becomes
    SEG_TAKE_DROP
    
* Type `term` is no longer an equality type

  - Equality on terms is now implemented by operator ~~
  
  - bir_utilLib provides some helper functions that expect an explicit equality function
    (might be better to move this somewhere else)
    
  - This change is especially relevant to SML code that works on HOL4 terms.
  
* Precedence:

   In Kananaskis-13, = binds more tightly than /\ to reduce parentheses in
   definitions such as
   
   val foo_def = Define`
      foo [] = ...
   /\ foo (x::xs) = ...
   `

   This breaks some existing definitions if there was a conjunction on the right
   hand side, e.g.
   
   `foo a b = a /\ b`
   
   would now be interpreted as `(foo a b = a) /\ b`, so it needs to be written as
   
   `foo a b = (a /\ b)`

   In some proofs there are quotations that use both = and /\, so those often
   break too. If a proof breaks, it is often a good idea to check either the
   statement of the theorem or any explicit quotations/subgoals in the proof
   script for wrong grouping. Most proofs have been fixed by adding/changing
   parentheses accordingly.
