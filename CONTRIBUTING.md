# Coding style

* like HOL source code
  - Spaces, no tabs
  - No unicode
  - `snake_case` (e.g. `bir_number_of_mem_splits_def`)



# Branch policy

## `master` branch

`master` is the branch where every feature is available, but not necessarily finalized:
 - Can cheat, but has to be avoided (TODO: if a check is present as CI test, maintain its exception list)
 - Code should not be be commented out
 - Our Travis CI must pass
   - **Holmake must work** (i.e. must correctly compile)
   - All tests must succeed
 - Bug-fixing commits are ok
 - At least 1 accepting review is needed in order to merge into `master`

Notice:
 - **No development happens on the `master` branch**, but rather on separate feature branches
 - **In order to prevent mayhem**, define good interfaces for your code (so that development won't break existing code)

Follow these instructions whenever you merge to master:
  - `grep` for "cheat" (TODO: add this as a CI test)
  - Check that the `README` is up to date (especially tool status)
  - Find a reviewer for your Pull Request


## tags

tags are like `master` and on top of this:
 - Should have as many **completed features** as possible
 - No cheats in the directory `src` (TODO: if check is present as CI test, add text here to check CI output for possible excluded directories)


## Feature branches

Every "somewhat" working tool should be available in the `master` branch, but new
features or any development must go on new branches prefixed with `dev_`, fixes with `fix_`.

Guidelines:
 - Branch names must be short and explicit (prefer explicit over short)
 - Every feature branch should involve small developments
 - **Rebase** feature branches on `master` **often**, by using `git rebase` or `git merge`: work on small features
 - Commits in a feature branch should compile, unless explicitly stated in commit message (with the prefix `[WIP] ...` for instance)
 - Further subbranch to do implementation experiments (keep them small)

If you want to violate the rules for temporary development or experiments (only
for feature branches):
  1. Fork
  2. Do a good mess
  3. Merge in feature branch after history rewrite




