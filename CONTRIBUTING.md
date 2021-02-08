## Coding style

* like HOL source code
  - Spaces, no tabs
  - No unicode
  - `snake_case` (e.g. `bir_number_of_mem_splits_def`)


## Branch policy

### `master` branch

`master` is the branch where every feature is available, but not necessarily finalized:
 - Can cheat, but has to be avoided (cheats are reported by the CI in Pull Requests)
   - You must explicitely say why you cheated if it's not too obvious
 - Code should not be be commented out
 - Our CI must pass
   - **Holmake must work** (i.e. must correctly compile)
   - All tests must succeed
 - Bug-fixing commits are ok
 - At least 1 accepting review is needed in order to merge into `master`

Notice:
 - **No development happens on the `master` branch**, but rather on separate feature branches
 - **In order to prevent mayhem**, define good interfaces for your code (so that development won't break existing code)

Follow these instructions whenever you merge to master:
  - `grep` for "cheat"
  - Check that the `README` is up to date (especially tool status)
  - Find a reviewer for your Pull Request

### tags

tags are like `master` and on top of this:
 - Should have as many **completed features** as possible
 - The `README` must be up to date, **especially in presence of cheat**

### Feature branches

Every "somewhat" working tool should be available in the `master` branch, but new
features or any development must go on new branches prefixed with `dev_`, fixes with `fix_`.

Guidelines:
 - Branch names must be short and explicit (prefer explicit over short)
 - Every feature branch should involve small developments
 - **Rebase** feature branches on `master` **often**, by using `git rebase` or `git merge`: work on small features
 - Commits in a feature branch should compile, unless explicitly stated in commit message (with the prefix `[WIP] ...` for instance)
 - Further subbranch to do implementation experiments (keep them small)

If you want to violate the rules for temporary development or experiments (only for feature branches):
  1. Fork
  2. Do a good mess
  3. Merge in feature branch after history rewrite

### Merging pull requests with GitHub
  1. Preferably and if possible, rebase the changes for a cleaner and more readable history. And to avoid merging overhead for ongoing work later.
  2. Have somebody review the pull request, especially if the change is more involving or around the core parts.
  3. Make sure that one of the CI tasks that build and run the tests completes successfully. One is allowed to timeout for unclear PolyML/HOL4 reasons.
  4. Merge the pull request with a merge commit to enable a standard GitHub commit message with reference to the pull request it belongs to.

### CI > Static analysis

This CI performs basic static analysis on the code:
 - locates all the places where `cheat` is used.
 - locates all the places where `TODO` or `FIXME` appear.
 
 It then post the results as a comment on the Pull Request (and in the CI logs as well). However, the CI **cannot** post a comment on the PR if the PR comes from a fork, for security reasons. In this case, there will be no comment posted. See #58 for more history.
