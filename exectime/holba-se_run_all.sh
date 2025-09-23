#!/usr/bin/env bash

# exit immediately if an error happens
set -e

# get setup directory path
HOLBA_DIR=$(dirname "${BASH_SOURCE[0]}")/..
HOLBA_DIR=$(readlink -f "${HOLBA_DIR}")

##################################################################

cd $HOLBA_DIR

make examples/arm_cm0/tiny
make examples/arm_cm0/aes
make examples/arm_cm0/modexp_simple
make examples/arm_cm0/motor_set
make examples/arm_cm0/balrob/v2-faster

# TODO: write all relevant logs to: logs/armcm0/holba-se/
# TODO: remove unimportant parts of logs from the files manually
