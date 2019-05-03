#!/usr/bin/env bash

set -e
TEST_PATH=$1
declare -g WATCH_PID=''

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

function start_watcher {
    declare WATCHER_START_TIME=$(date +%s.%N)
    while [ 1 ]; do
        sleep 30
        declare END_TIME=$(date +%s.%N)
        declare DURATION=$(python2 -c "print($END_TIME - $WATCHER_START_TIME)")
        enclose "Test running: $TEST_PATH" "$(printf 'Time so far: %3g sec.\n' "$DURATION")"
    done &
    declare -g WATCH_PID=$!
}

function stop_watcher {
    kill "$WATCH_PID"
}

function test_failed_trap {
    declare END_TIME=$(date +%s.%N)
    declare DURATION=$(python2 -c "print($END_TIME - $START_TIME)")
    enclose "Test failed: $TEST_PATH" "$(printf 'Elapsed time: %3g sec.\n' "$DURATION")"
    stop_watcher
}

function test_script_file {
    declare DIR=$(dirname $1)
    declare FILENAME=$(basename $1)

    enclose "Testing: $1"

    declare -g START_TIME=$(date +%s.%N)
    trap test_failed_trap EXIT

    cd $DIR && ./$FILENAME
    #sleep 1
    #if (($RANDOM < 20000)); then exit 1; fi

    declare END_TIME=$(date +%s.%N)
    declare DURATION=$(python2 -c "print($END_TIME - $START_TIME)")

    enclose "Test successful: $1" "$(printf "Elapsed time: %3g sec.\n" "$DURATION")"

    trap - EXIT # Remove the trap
}

if [ "$#" -ne 1 ]; then
    echo "Usage: $0 TEST_FILE"
    exit 1
fi
[[ ! -f "$TEST_PATH" ]] && (echo "Test not found: '$TEST_PATH'" && exit 1)

start_watcher
test_script_file $TEST_PATH
stop_watcher

