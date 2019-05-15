#!/usr/bin/env bash

# Check that this script is run during a PR job
if [[ "$TRAVIS_PULL_REQUEST" == "false" ]]; then
   echo '$TRAVIS_PULL_REQUEST is false, exiting.'
   exit 0
fi

# Check that the env variables we need are correct
[[ -n "$TRAVIS_PULL_REQUEST" ]] && echo "\$TRAVIS_PULL_REQUEST: $TRAVIS_PULL_REQUEST" \
    || { echo '$TRAVIS_PULL_REQUEST not set, exiting.'; exit 1; }
[[ -n "$TRAVIS_REPO_SLUG" ]] && echo "\$TRAVIS_REPO_SLUG: $TRAVIS_REPO_SLUG" \
    || { echo '$TRAVIS_REPO_SLUG not set, exiting.'; exit 1; }
[[ -n "$TRAVIS_COMMIT" ]] && echo "\$TRAVIS_COMMIT: $TRAVIS_COMMIT" \
    || { echo '$TRAVIS_COMMIT not set, exiting.'; exit 1; }

## The GitHub token has a special treatment (it's secret)
[[ -n "$HOLBA_BOT_GITHUB_TOKEN" ]] && echo "\$HOLBA_BOT_GITHUB_TOKEN is set." \
    || { echo '$HOLBA_BOT_GITHUB_TOKEN not set, exiting.'; exit 1; }

# Grep for 'cheat' in the $GREP_DIR directory
GREP_PATTERN='\<cheat\>'
GREP_DIR='src/'
echo "grep command: grep -r $GREP_PATTERN --include='*Script.sml' $GREP_DIR"
N_CHEATS=$(grep -r $GREP_PATTERN --include='*Script.sml' $GREP_DIR | wc -l)
WITH_CONTEXT=$(grep -rn -C6 $GREP_PATTERN --include='*Script.sml' $GREP_DIR)
ONLY_LINES=$(grep -rn $GREP_PATTERN --include='*Script.sml' $GREP_DIR \
    | cut -d: -f-2 --output-delimiter=' ' \
    | awk "{printf \"- [%s, line %d]\", \$1, \$2;
            printf \"(https://github.com/${TRAVIS_REPO_SLUG}/blob/${TRAVIS_COMMIT}/%s#L%d)\n\", \$1, \$2;}")

# Build the comment that will be posted on the PR
if [[ "$N_CHEATS" -eq 0 ]]; then
    COMMENT_CONTENT="No \`cheat\` found in \`$GREP_DIR\`."
else
    COMMENT_CONTENT="
<details>
<summary>Found $N_CHEATS occurences of <code>cheat</code> in <code>$GREP_DIR</code>.</summary>

$ONLY_LINES

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

# Escape the comment to respect JSON format
json_escape () {
    printf '%s' "$1" | python -c 'import json,sys; print(json.dumps(sys.stdin.read()))'
}
COMMENT_BODY=$(json_escape "$COMMENT_BODY")

# Send the result to the PR
curl --silent --show-error \
    -H "Authorization: token ${HOLBA_BOT_GITHUB_TOKEN}" \
    -X POST \
    -d "{\"body\": ${COMMENT_BODY}}" \
    "https://api.github.com/repos/${TRAVIS_REPO_SLUG}/issues/${TRAVIS_PULL_REQUEST}/comments" \
    | grep -v '"body":' | cat # Filter out the body to reduce verbosity

