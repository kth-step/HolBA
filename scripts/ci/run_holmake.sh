#!/usr/bin/env bash

# exit immediately if an error happens
set -e

# find the environment variables
source ./env.sh

# compile the project
# -------------------------------
${HOLBA_HOL_DIR}/bin/Holmake


