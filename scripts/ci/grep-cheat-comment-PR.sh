#!/usr/bin/env bash

printf '%80s\n' ' ' | tr ' ' '#'

# Grep for 'cheat' in the $GREP_DIR directory
GREP_PATTERN='\<cheat\>'
echo "grep command: grep -r $GREP_PATTERN --include='*Script.sml' \$GREP_DIR"
N_CHEATS_SRC=$(grep -r $GREP_PATTERN --include='*Script.sml' src/ | wc -l)
N_CHEATS_EXAMPLES=$(grep -r $GREP_PATTERN --include='*Script.sml' examples/ | wc -l)
N_CHEATS=$(($N_CHEATS_SRC + $N_CHEATS_EXAMPLES))
WITH_CONTEXT=$(grep -rn -C6 $GREP_PATTERN --include='*Script.sml' src/ examples/)
FILE_LINES=$(grep -rn $GREP_PATTERN --include='*Script.sml' src/ examples/ \
    | cut -d: -f-2 --output-delimiter=' ')
PRETTY_FILE_LINES=$(<<< "$FILE_LINES" awk "{printf \" - %s line %d\n\", \$1, \$2;}")
GITHUB_LOCATIONS=$(<<< "$FILE_LINES" awk "{printf \"- [%s, line %d]\", \$1, \$2;
            printf \"(https://github.com/${TRAVIS_REPO_SLUG}/blob/${TRAVIS_COMMIT}/%s#L%d)\n\", \$1, \$2;}")

# Build the comment that will be posted on the PR
if [[ "$N_CHEATS" -eq 0 ]]; then
    COMMENT_CONTENT="No \`cheat\` found in <code>src/</code> or <code>examples/</code>."
else
    COMMENT_CONTENT="
<details>
<summary>Found $N_CHEATS_SRC occurences of <code>cheat</code> in <code>src/</code> and $N_CHEATS_EXAMPLES in <code>examples/</code>.</summary>

$GITHUB_LOCATIONS

<details>
<summary>Click here for details</summary>

\`\`\`
$WITH_CONTEXT
\`\`\`

</details>
</details>
"
fi

COMMENT_BODY="
:robot: Results of: \`scripts/ci/grep-cheat-comment-PR.sh\`

$COMMENT_CONTENT

---

**Note**: I'm a script, and I'm simple. I only do \`grep -r $GREP_PATTERN --include='*Script.sml' $GREP_DIR\`, so I may be missing something or show false positives. You can review the script [here](https://github.com/${TRAVIS_REPO_SLUG}/blob/${TRAVIS_COMMIT}/scripts/ci/grep-cheat-comment-PR.sh).
"
## End of "Build the comment..."

# Print the comment
if [[ "$N_CHEATS" -eq 0 ]]; then
    printf 'Grep-cheat analysis results:\n -> No cheat found in src/ and examples/.\n'
else
    printf 'Grep-cheat analysis results:\n%s\n' "$PRETTY_FILE_LINES"
fi

# Post the comment on the PR (if any)
./scripts/ci/post-comment-on-PR.sh <<< "$COMMENT_BODY"

printf '%80s\n' ' ' | tr ' ' '#'

