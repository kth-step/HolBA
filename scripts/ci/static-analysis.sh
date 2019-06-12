#!/usr/bin/env bash

###############################################################################
# Runs the static analysis on the repository and sends the results as both    #
# text output on STDOUT and GitHub comment on the PR (if ran in a Travis PR   #
# job).                                                                       #
###############################################################################

# This script must be run from the root directory
[[ -d "scripts/" ]] || { echo 'This script must be run from the root directory.'; exit 1; }

printf '%80s\n' ' ' | tr ' ' '#' >&2

# Grep 'cheat'
GREP_CHEAT_MARKDOWN=$(./scripts/ci/static-analysis/grep-analysis.sh 'cheat' '\<cheat\>')

# Grep 'TODO' or 'FIXME'
GREP_TODO_MARKDOWN=$(./scripts/ci/static-analysis/grep-analysis.sh 'TODO/FIXME' '\<TODO\>|\<FIXME\>|\<todo\>|\<fixme\>')

# Build the GitHub comment
GITHUB_COMMENT="
:robot: Results of: \`scripts/ci/static-analysis.sh\`

---

Grep-cheat analysis:
$GREP_CHEAT_MARKDOWN

---

Grep-todo analysis:
$GREP_TODO_MARKDOWN

---

**Note**: I'm a script, and I'm simple, so I may be missing something or show false positives. You can review the script [here](https://github.com/${TRAVIS_REPO_SLUG}/blob/${TRAVIS_COMMIT}/scripts/ci/static-analysis.sh).
"
## End of "Build the GitHub comment"

# Post the comment to GitHub
./scripts/ci/post-comment-on-PR.sh <<< "$GITHUB_COMMENT"

printf '%80s\n' ' ' | tr ' ' '#' >&2

