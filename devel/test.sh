#!/bin/bash

# exit immediately if an error happens
set -e

# setup environment
. ${ENV_EXPORT_SCRIPT}

# compile the project
# -------------------------------
export HOLMAKE="${CACHE_DIR}/HOL/bin/Holmake --qof"
make -k tests


