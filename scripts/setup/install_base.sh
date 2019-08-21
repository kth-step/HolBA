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

# create the directory if it doesn't exist yet
mkdir -p "${HOLBA_OPT_DIR}"
mkdir -p "${HOLBA_SCAMV_LOGS}"




# install poly
echo "-----------------------------------------------"
echo "------------- installing polyml ---------------"
echo "-----------------------------------------------"
"${SETUP_DIR}/install_poly.sh"
echo


# install hol4
echo "-----------------------------------------------"
echo "-------------- installing HOL4 ----------------"
echo "-----------------------------------------------"
"${SETUP_DIR}/install_hol4.sh"
echo

