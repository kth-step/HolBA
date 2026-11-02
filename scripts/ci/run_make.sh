#!/usr/bin/env bash

# exit immediately if an error happens
set -e

MAKETARGET_PARAM=$1

# find the environment variables
# - Makefile already does this where needed
#set --
#source ./env.sh

# compile the project
# -------------------------------
# --no-project: ignore the holproject.toml files, which are for holbuild
export HOLBA_HOLMAKE_OPTS="--qof --no-project"
make ${MAKETARGET_PARAM}


