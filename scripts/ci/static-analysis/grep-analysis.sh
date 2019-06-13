#!/usr/bin/env bash

###############################################################################
# Greps for '$1' in src/ and examples/. Prints GitHub Markdown results to     #
# STDOUT and text results to STDERR.                                          #
#                                                                             #
# See below for mandatory and optional parameters.                            #
###############################################################################

printf '%60s\n' ' ' | tr ' ' '*' >&2

# Mandatory parameters
[[ -n "$1" ]] && >&2 echo "PRETTY_PATTERN=$1" \
    || { >&2 echo "You must supply the pretty name of the grepped pattern."; exit 1; }
[[ -n "$2" ]] && >&2 echo "GREP_PATTERN=$2" \
    || { >&2 echo "You must supply the grep pattern."; exit 1; }
PRETTY_PATTERN="$1"
GREP_PATTERN="$2"

# Optional parameters
GREP_INCLUDE=${GREP_INCLUDE:-"*Script.sml"}

# Grep for the given pattern in both src/ and examples/
>&2 echo "grep command: grep -r -E $GREP_PATTERN --include='$GREP_INCLUDE' \$GREP_DIR"
N_CHEATS_SRC=$(grep -r -E $GREP_PATTERN --include="$GREP_INCLUDE" src/ | wc -l)
N_CHEATS_EXAMPLES=$(grep -r -E $GREP_PATTERN --include="$GREP_INCLUDE" examples/ | wc -l)
N_CHEATS=$(($N_CHEATS_SRC + $N_CHEATS_EXAMPLES))
WITH_CONTEXT=$(grep -rn -C6 -E $GREP_PATTERN --include="$GREP_INCLUDE" src/ examples/)
FILE_LINES=$(grep -rn -E $GREP_PATTERN --include="$GREP_INCLUDE" src/ examples/ \
    | cut -d: -f-2 --output-delimiter=' ')
PRETTY_FILE_LINES=$(<<< "$FILE_LINES" awk "{printf \" - %s line %d\n\", \$1, \$2;}")
GITHUB_LOCATIONS=$(<<< "$FILE_LINES" awk "{printf \"- [%s, line %d]\", \$1, \$2;
            printf \"(https://github.com/${TRAVIS_REPO_SLUG}/blob/${TRAVIS_COMMIT}/%s#L%d)\n\", \$1, \$2;}")

# Build the comment that will be posted on the PR
if [[ "$N_CHEATS" -eq 0 ]]; then
    MARKDOWN="No \`$PRETTY_PATTERN\` found in <code>src/</code> or <code>examples/</code>."
else
    MARKDOWN="
<details>
<summary>Found $N_CHEATS_SRC occurences of <code>$PRETTY_PATTERN</code> in <code>src/</code> and $N_CHEATS_EXAMPLES in <code>examples/</code>.</summary>

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
## End of "Build the comment..."

# Text output on STDERR
if [[ "$N_CHEATS" -eq 0 ]]; then
    >&2 printf "Grep '$PRETTY_PATTERN' analysis results:\n -> No '$PRETTY_PATTERN' found in src/ and examples/.\n"
else
    >&2 printf "Grep '$PRETTY_PATTERN' analysis results:\n%s\n" "$PRETTY_FILE_LINES"
fi

# GitHub Markdown output on STDOUT
echo "$MARKDOWN"

printf '%60s\n' ' ' | tr ' ' '*' >&2

