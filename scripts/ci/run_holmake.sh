#!/usr/bin/env bash

# exit immediately if an error happens
set -e

# find the environment variables
source ./env.sh

# compile the project
# -------------------------------
# --no-project: ignore the holproject.toml files, which are for holbuild
${HOLBA_HOL_DIR}/bin/Holmake --no-project


