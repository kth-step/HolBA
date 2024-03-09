# Contribution guide for the HolBA library

## Coding style

Like HOL4 source code:

- Spaces, no tabs
- No unicode
- `snake_case` (e.g., `bir_number_of_mem_splits_def`)

## Branch and tag policy

- The `master` is the branch where every feature is available, but not necessarily finalized
- No development happens on the `master` branch, but rather on separate topic branches,
  either inside the repository or in repository forks
- When your changes are ready to be integrated into `master`, open a Pull Request (PR)

### `master` branch

PRs to `master` must abide by the following rules: 

- HolBA Continuous Integration (CI) must pass
  - Running `Holmake` must work (i.e., the changes must correctly compile)
  - All tests run in CI must succeed
- Use of `cheat` should be a last resort (cheats are reported by the CI in PRs)
  - You must explicitly say why you used `cheat` if it's not obvious
  - `grep` for unexpected occurrences of `cheat` before submitting your PR
- Code should not be be commented out
- PRs that only fix bugs are welcome but should be documented as such
- At least one accepting review is needed in order to merge into `master`
- Standard ML code should come with interfaces (`.sig` files), so that new development won't easily break existing code
- `README.md` must be up to date (especially w.r.t. tool status)

### Tags

Tags are like the `master` branch with the following additional rules:

- A tag should have as many **completed features** as possible
- `README.md` must be up to date, in particular if there are uses of `cheat`

### Topic branches

- Features or other new developments should go in new branches prefixed with `dev_`
- Branch names should be short and explicit (prefer explicit over short)
- Try to keep changes in feature branches as small as possible
- **Rebase** feature branches on top of `master` **often**, by using `git rebase` or `git merge`
- Commits in a feature branch should compile, unless explicitly stated in the commit message (with the prefix `[WIP] ...` for instance)

## Merging branches on GitHub

1. Preferably and if possible, rebase the changes against the target branch for a cleaner and more readable history, and to avoid merging overhead for later work.
2. Have somebody review the PR, especially if changes are extensive or affect core modules of HolBA.
3. Make sure that CI builds and runs the tests successfully. It is allowed to timeout for unclear PolyML/HOL4 reasons.
4. Merge the PR with a merge commit to enable a standard GitHub commit message with reference to the pull request it belongs to.
