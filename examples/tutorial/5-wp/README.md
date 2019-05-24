# Introduction

This directory is a tutorial on how to obtain the weakest precondition of code segments, given their postconditions.

From the previous directory `4-bir-to-arm` we should have a number of contracts on code segments, in the shape of Hoare triples. In order to prove that these contracts hold, we take the postcondition and code segment of the contract, then generate and prove the corresponding weakest precondition, thereby obtaining a new Hoare triple. _Weakest_ precondition means the least restrictive condition on the initial states which always leads to execution reaching a final state satisfying the postcondition. The theorems stating weakest preconditions corresponding with the individual BIR statements can be found in `bir_wpTheory`.

Since the postcondition and code segment are the same, proving the contract - loosely speaking - simply means that we must prove that the contractual precondition implies the weakest precondition. This can be thought of as proving that the set of initial states which fulfil the precondition are a subset of the set of initial states which fulfil the weakest precondition (the least restrictive condition under which execution from the initial state always leads to a final state fulfilling the postcondition).

# Stepwise walkthrough
