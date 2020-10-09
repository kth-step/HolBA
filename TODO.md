


* Peterson's algorithm

Mutual exclusion
for all traces t.
if pc(core i) in critical region then for all cores j <> i. pc(core j) is not in critical region


* Interleaving2
 All possible orderings of store and load occur
 
 * TAS locks, prove that mutual exclusion scales to an arbitrary number of cores
 
 * Other concurrency properties: deadlock freedom, starvation freedom
 
 * Translation of properties back to ISA level
 
 * Post-lifting processing
  Putting lifted programs into canonical form for the multicore semantics
  e.g.
  
  MEM[3] := R0 + R1  ----> R3 := R0 + R1; MEM[3] := R3;
  
* Modeling memory hierarchies

* Modeling out of order execution

* Formalising conditions for using sequential/core-local semantics / proving refinement between multicore and sequential semantics

* Proving properties of lock-free data structures

* Related work / state of the art exploration
    CertiKOS? limited to locks, doesn't include lock-free structures
    seL4, check concurrency formalization
    find smaller ongoing/past projects
    controversial pen and paper proofs of algorithms in concurrency
