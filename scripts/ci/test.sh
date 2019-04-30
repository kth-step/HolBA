#!/usr/bin/env bash

# exit immediately if an error happens
set -e

# compile the project
# -------------------------------
export HOLBA_HOLMAKE="${HOLBA_HOLMAKE} --qof"
make tests

