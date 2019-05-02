#!/usr/bin/env bash

# exit immediately if an error happens
set -e

OPT_DIR_PARAM=$1

# get setup directory path
SETUP_DIR=$(dirname "${BASH_SOURCE[0]}")
SETUP_DIR=$(readlink -f "${SETUP_DIR}")

# find the environment variables
set --
source "${SETUP_DIR}/autoenv.sh" "${OPT_DIR_PARAM}"

##################################################################


# download package
Z3_URL="https://github.com/Z3Prover/z3/releases/download/z3-4.8.4/z3-4.8.4.d6df51951f4c-x64-debian-8.11.zip"

Z3_DIR=${HOLBA_OPT_DIR}/z3-4.8.4.d6df51951f4c








##################################################################


# if the output directory exists, we already have a z3 in the cache
if [ -d "${Z3_DIR}" ]; then
  echo "z3 is already available in the cache, exiting."
  exit 0
else
  echo "z3 is not in the cache, downloading it now."
fi

# download z3
mkdir "${Z3_DIR}"
wget ${Z3_URL} -O z3_temp.zip
unzip z3_temp.zip -d "${Z3_DIR}"
rm z3_temp.zip

# tar it
tar -C "${Z3_DIR}" -cf z3_temp.tar .
rm -rf "${Z3_DIR}"
mkdir "${Z3_DIR}"

# untar it again
tar -C "${Z3_DIR}" -xf z3_temp.tar --strip-components 2
rm z3_temp.tar


