# Software versions

HOL4 commit: d0a474d1d1cba7c32acb6056a6288c44c2f1a75b
PolyML (e.g. standard Ubuntu) 5.6


# How to compile

* use `{HOLDIR}/bin/Holmake` in `src`
* if the previous step fails, try to clean your git working directory by `make cleanslate` in the project root directory


# Branch policy

* one branch per feature
  * commit in a feature branch must compile
  * Holmake must work
  * Can cheat
  * Code can be commented

* master is the stable release (probably 1 or 2 months behind the development)
  * bug-fixes ok
  * changes that do not affect existing code ok (e.g. new theories, functions. etc)
  * should be tested
  * merge to master only after pull request and 2 reviews (for now Roberto + Thomas)
  * no cheat

* development is the standard branch where completed features are merged
  * must correctly compile
  * self tests must succeed
  * merge to development 1 review (Thomas or Roberto, not the same one that developed the feature)
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
