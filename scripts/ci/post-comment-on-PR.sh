#!/usr/bin/env bash

###############################################################################
# Posts the content received on STDIN as a comment on the current PR. This    #
# script only works when run in Travis (otherwise, it exits with 1). If the   #
# environment is misconfigured, the script exits with 2.                      #
###############################################################################

# Check that this script is run during a PR job
if [[ -z "$TRAVIS_PULL_REQUEST" || "$TRAVIS_PULL_REQUEST" == "false" ]]; then
    echo 'Not a Travis PR job ($TRAVIS_PULL_REQUEST is false or unset), not sending.'
    exit 1
fi

# Check that the env variables we need are correct
[[ -n "$TRAVIS_PULL_REQUEST" ]] && echo "\$TRAVIS_PULL_REQUEST: $TRAVIS_PULL_REQUEST" \
    || { echo '$TRAVIS_PULL_REQUEST not set, not sending.'; exit 2; }
[[ -n "$TRAVIS_REPO_SLUG" ]] && echo "\$TRAVIS_REPO_SLUG: $TRAVIS_REPO_SLUG" \
    || { echo '$TRAVIS_REPO_SLUG not set, not sending.'; exit 2; }
[[ -n "$TRAVIS_COMMIT" ]] && echo "\$TRAVIS_COMMIT: $TRAVIS_COMMIT" \
    || { echo '$TRAVIS_COMMIT not set, not sending.'; exit 2; }

## The GitHub token has a special treatment (it's secret)
[[ -n "$HOLBA_BOT_GITHUB_TOKEN" ]] && echo "\$HOLBA_BOT_GITHUB_TOKEN is set." \
    || { echo '$HOLBA_BOT_GITHUB_TOKEN not set, exiting.'; exit 2; }

# Get the comment body from stdin
declare COMMENT_BODY="$(cat)"

# Escape the comment to respect JSON format
json_escape () {
    printf '%s' "$1" | python3 -c 'import json,sys; print(json.dumps(sys.stdin.read()))'
}
declare COMMENT_BODY=$(json_escape "$COMMENT_BODY")

# Send the result to the PR
echo 'Sending the comment to GitHub...'
curl --silent --show-error \
    -H "Authorization: token ${HOLBA_BOT_GITHUB_TOKEN}" \
    -X POST \
    -d "{\"body\": ${COMMENT_BODY}}" \
    "https://api.github.com/repos/${TRAVIS_REPO_SLUG}/issues/${TRAVIS_PULL_REQUEST}/comments" \
    | grep -v '"body":' | cat # Filter out the body to reduce verbosity

