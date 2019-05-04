#!/usr/bin/env bash

# exit immediately if an error happens
set -e

MAKETARGET_PARAM=$1

# find the environment variables
# - Makefile already does this where needed
#set --
#source scripts/setup/autoenv.sh

# compile the project
# -------------------------------
export HOLBA_HOLMAKE_OPTS="--qof"
make ${MAKETARGET_PARAM}


