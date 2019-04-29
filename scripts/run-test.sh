#!/usr/bin/env bash

set -e
TEST_PATH=$1

function find_hol4_bin_dir {
    declare HOLMAKE=${HOLMAKE:-"Holmake"}
    declare HOLMAKE_NOFLAGS=$(echo $HOLMAKE | awk '{print $1;}')

    which $HOLMAKE_NOFLAGS >/dev/null \
        || (echo "Holmake not found. Please set a HOlMAKE env variable." && exit 1)

    dirname $(which $HOLMAKE_NOFLAGS)
}

function run_sml_file {
    # This function must be inside the directory containing the .sml test file

    declare HOLBINDIR=$(find_hol4_bin_dir)
    declare BUILDHEAP="$HOLBINDIR/buildheap"
    declare HEAPNAME="$HOLBINDIR/heapname"

    # Determine in which heap to execute by looking at the Holmakefile.gen file
    declare HEAP=$(grep -E '^HOLHEAP' Holmakefile.gen | sed -r 's/HOLHEAP\s*=\s*(\S+)/\1/')
    if [ ! -f "$HEAP" ]; then
        declare HEAP=`$HEAPNAME`
    fi

    declare SML_MODULE=$(echo $1 | sed -r 's/.sml//')

    # This line executes the test. If the test fails (exit status not 0), then
    # test_failed_trap will be executed and the script will fail. This is due
    # to `set -e` and `trap test_failed_trap EXIT`
    $BUILDHEAP --gcthreads=1 --holstate="$HEAP" $SML_MODULE
}

function enclose {
    declare MAX_LEN=$(for s in "$@"; do printf "$s" | wc -c; done | sort -r | head -n1)
    declare LINE_LENGTH=$((MAX_LEN + 6)) # 6 is the length of "==  =="
    declare BAR=$(printf "%*s" $LINE_LENGTH "" | tr ' ' '=')

    echo "$BAR"
    for s in "$@"; do
        printf "== %-*s ==\n" "$MAX_LEN" "$s"
    done
	echo "$BAR"
}

function test_failed_trap {
    declare END_TIME=$(date +%s.%N)
    declare DURATION=$(echo "$END_TIME - $START_TIME" | bc)
    enclose "Test failed: $TEST_PATH" "$(printf "Elapsed time: %3g sec.\n" "$DURATION")"
}

function test_sml_file {
    declare DIR=$(dirname $1)
    declare FILENAME=$(basename $1)

    enclose "Testing: $1"

    declare -g START_TIME=$(date +%s.%N)
    trap test_failed_trap EXIT

    cd $DIR && run_sml_file $FILENAME
    #sleep 1
    #if (($RANDOM < 20000)); then exit 1; fi

    declare END_TIME=$(date +%s.%N)
    declare DURATION=$(echo "$END_TIME - $START_TIME" | bc)

    enclose "Test successful: $1" "$(printf "Elapsed time: %3g sec.\n" "$DURATION")"

    trap - EXIT # Remove the trap
}

if [ "$#" -ne 1 ]; then
    echo "Usage: $0 TEST_FILE"
    exit 1
fi
[[ ! -f "$TEST_PATH" ]] && (echo "Test not found: '$TEST_PATH'" && exit 1)
test_sml_file $TEST_PATH

