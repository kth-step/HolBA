#!/usr/bin/env bash

set -e
SML_PATH=$1

function find_hol4_bin_dir {
    declare HOLBA_HOLMAKE=${HOLBA_HOLMAKE:-"Holmake"}
    declare HOLMAKE_NOFLAGS=$(echo $HOLBA_HOLMAKE | awk '{print $1;}')

    which $HOLMAKE_NOFLAGS >/dev/null \
        || (echo "Holmake not found. Please set a HOLBA_HOlMAKE env variable." && exit 1)

    dirname $(which $HOLMAKE_NOFLAGS)
}

function mk_exe_for_sml_file {
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

    # Generate the .exe file as executable
    RUN_CMD="\"${BUILDHEAP}\" --gcthreads=1 --holstate=\"${HEAP}\" ${SML_MODULE}"
    EXE_FILE_CONTENTS="#!/bin/sh\nset -e\n${RUN_CMD}\nexit 0"
    echo -e ${EXE_FILE_CONTENTS} > ${SML_MODULE}.exe
    chmod +x ${SML_MODULE}.exe
}


declare DIR=$(dirname "${SML_PATH}")
declare FILENAME=$(basename "${SML_PATH}")

cd "${DIR}"
mk_exe_for_sml_file "${FILENAME}"
echo "--- created .exe file for ${SML_PATH}"




