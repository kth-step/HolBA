#!/usr/bin/env bash

OPT_DIR_PARAM=$1

# get setup directory path
SETUP_DIR=$(dirname "${BASH_SOURCE[0]}")
SETUP_DIR=$(readlink -f "${SETUP_DIR}")

# find the environment variables
. "${SETUP_DIR}/env.sh" "${OPT_DIR_PARAM}"

##################################################################

# create the directory if it doesn't exist yet
mkdir -p "${HOLBA_OPT_DIR}"


echo "-----------------------------------------------"
echo "-- using HOLBA_OPT_DIR=${HOLBA_OPT_DIR}"
echo "-----------------------------------------------"


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


# place Makefile.local to set Holmake
echo "-----------------------------------------------"
echo "---------- placing Makefile.local -------------"
echo "-----------------------------------------------"
. "${SETUP_DIR}/env.sh"
echo "HOLBA_HOLMAKE=${HOLBA_HOLMAKE}" > Makefile.local
echo

