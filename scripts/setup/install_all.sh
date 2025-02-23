#!/usr/bin/env bash

# exit immediately if an error happens
set -e

OPT_DIR_PARAM=$1

# get setup directory path
SETUP_DIR=$(dirname "${BASH_SOURCE[0]}")
SETUP_DIR=$(readlink -f "${SETUP_DIR}")

# find the environment variables
set --
source "${SETUP_DIR}/env_config_gen.sh" "${OPT_DIR_PARAM}"

##################################################################







# install the base (poly, hol4 and basic setup)
echo
echo "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%"
echo

"${SETUP_DIR}/install_base.sh"

echo
echo "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%"
echo


# install Z3
echo "-----------------------------------------------"
echo "--------------- installing Z3 -----------------"
echo "-----------------------------------------------"
"${SETUP_DIR}/install_z3.sh"
echo


# install gcc_arm8
echo "-----------------------------------------------"
echo "------------ installing gcc_arm8 --------------"
echo "-----------------------------------------------"
"${SETUP_DIR}/install_gcc_arm8.sh"
echo


# install gcc_arm
echo "-----------------------------------------------"
echo "------------ installing gcc_arm ---------------"
echo "-----------------------------------------------"
"${SETUP_DIR}/install_gcc_arm.sh"
echo


# install gcc_riscv64
echo "-----------------------------------------------"
echo "---------- installing gcc_riscv64 -------------"
echo "-----------------------------------------------"
"${SETUP_DIR}/install_gcc_riscv64.sh"
echo


