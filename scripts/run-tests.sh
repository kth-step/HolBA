#!/usr/bin/env bash

set -e

if [ "$#" -ne 0 ]; then
    echo "Usage: $0"
    exit 1
fi

TEST_SUCCESS_FILE=holba-tests.success
TEST_LOG_FILE=holba-tests.log

function cleanup {
    rm -f "$TEST_SUCCESS_FILE" "$TEST_LOG_FILE"
}
trap cleanup EXIT

function print_report {
    declare SUCCESSFUL=$(                                 \
        grep "== Test successful:" "$TEST_LOG_FILE"       \
        | sed -r 's/== Test successful: (\S+) ==/\1/')
    declare FAILED=$(                                     \
        grep "== Test failed:" "$TEST_LOG_FILE"           \
        | sed -r 's/== Test failed: (\S+) ==/\1/')
    declare MAKE_FAILED=$(                                           \
        grep -R "recipe for target .* failed" "$TEST_LOG_FILE"       \
        | cut -d"'" -f2)

    declare N_SUCCESSFUL=$(printf '%s' "$SUCCESSFUL" | grep -c '')
    declare N_FAILED=$(printf '%s' "$FAILED" | grep -c '')
    declare N_MAKE_FAILED=$(printf '%s' "$MAKE_FAILED" | grep -c '')

    # Print a separator
    echo
    printf '%*s\n' 80 '' | tr ' ' '#'

    # Successful tests
    if (($N_SUCCESSFUL == 0)); then
        echo
        printf 'No successful tests.\n'
    else
        echo
        printf 'Successful tests: (%d total)\n' $N_SUCCESSFUL
        echo "$SUCCESSFUL" | sed -e 's/^/- /'
    fi


    # `make` failed tests
    if (($N_MAKE_FAILED > 0)); then
        echo
        printf 'make failed for some tests: (%d total)\n' $N_MAKE_FAILED
        echo "$MAKE_FAILED" | sed -e 's/^/- /'
    fi


    # Failed tests
    if (($N_FAILED > 0)); then
        echo
        printf 'Failed tests: (%d total)\n' $N_FAILED
        echo "$FAILED" | sed -e 's/^/- /'
    fi

    if (($N_FAILED + $N_MAKE_FAILED == 0)); then
        echo
        printf 'All tests succeeded.\n'
    fi
}

function tests_succeeded {
    print_report
    exit 0
}

function tests_failed {
    print_report

    if (($TEST_JOBS > 1)); then
        echo
        echo "NOTE: You can set TEST_JOBS=1 to avoid having interleaved test"
        echo "outputs, or directly use: run-test.sh path/to/failed-test.sml"
        echo
    fi

    exit 1
}

# Delete the log files, in case of partial run
cleanup

# Use make to run the tests
TEST_JOBS=${TEST_JOBS:-4}
(make -k --silent -j$TEST_JOBS _run_tests && touch "$TEST_SUCCESS_FILE") \
    | tee "$TEST_LOG_FILE"

# Determine whether tests succeeded with $TEST_SUCCESS_FILE
if [ -f "$TEST_SUCCESS_FILE" ]; then
    tests_succeeded
else
    tests_failed
fi

# Logs are automatically cleaned-up with the trap

