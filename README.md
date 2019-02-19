# Software versions

HOL4 commit: ae1feaa27180bbbe081e70f9004859321d0d426f (tags/kananaskis-12)
PolyML (e.g. standard Ubuntu) 5.6


# How to compile

* use `{HOLDIR}/bin/Holmake` in `src`
* if the previous step fails, try to clean your git working directory by `make cleanslate` in the project root directory


# Branches
## Branch `master`

* core functionality for BIR language
  * `core`
  * `core-props`
  * `tools/cfg` (non-proof-producing)
* the binary lifter
  * `tools/l3`
  * `tools/lifter`


## Branch `wp`

* weakest precondition propagation and related substitution simplification prototype for verification
  * `tools/wp`


## Branch `benchmarks`

* some binaries and disassembly files of binaries for benchmarking of the `lifter` and `wp`, and also parts of the resulting data
  * `tools/lifter/benchmark/binaries` (non-proof-producing)
  * `tools/wp/benchmark/binaries` (non-proof-producing)


## Branch policy

* one branch per feature
  * commit in a feature branch must compile
  * Holmake must work
  * Can cheat
  * Code can be commented

* master is the standard branch where completed features are merged
  * bug-fixes ok
  * must correctly compile
  * self tests must succeed
  * should be tested
  * merge to development 1 review (Andreas or Roberto, not the same one that developed the feature)
  * no cheat

* if you want to violate the rules for temporary development or experiments (only for feature branches)
  * fork
  * merge in feature branch after history rewrite

* suggestions
  * for long running feature branches keep in sync with base branch and rebase if easily possible

* HOL source code
  * Spaces, no tabs
  * No unicode
  * name_surname_etc_etc
