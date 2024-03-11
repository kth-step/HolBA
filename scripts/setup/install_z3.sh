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

# use a default z3 version if it is not specified in the environment
Z3_VERSION="4.12.2"
if [[ ! -z "${HOLBA_Z3_VERSION}" ]]; then
  Z3_VERSION=${HOLBA_Z3_VERSION}
fi

Z3_ASSET_SUFFIX="-x64-glibc-2.31.zip"
if [[ ! -z "${HOLBA_Z3_ASSET_SUFFIX}" ]]; then
  Z3_ASSET_SUFFIX=${HOLBA_Z3_ASSET_SUFFIX}
fi

# download package
Z3_URL="https://github.com/Z3Prover/z3/releases/download/z3-${Z3_VERSION}/z3-${Z3_VERSION}${Z3_ASSET_SUFFIX}"

Z3_DIR=${HOLBA_OPT_DIR}/z3-${Z3_VERSION}








##################################################################


# if the output directory exists, we already have a z3 in the cache
if [[ -d "${Z3_DIR}" ]]; then
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


