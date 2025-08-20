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


# based on HOL4 developers/install-poly.sh
# --------------------------------------------
POLY_BASE="https://github.com/polyml/polyml"

# use a default polyml version if it is not specified in the environment
POLY_VERSION="v5.9.2"
if [[ ! -z "${HOLBA_POLYML_VERSION}" ]]; then
  POLY_VERSION=${HOLBA_POLYML_VERSION}
fi

POLY_URL=${POLY_BASE}/archive/${POLY_VERSION}.tar.gz

POLY_DIR=${HOLBA_OPT_DIR}/polyml_${POLY_VERSION}
POLY_DIR_SRC=${HOLBA_OPT_DIR}/polyml_${POLY_VERSION}_src




##################################################################

if [[ "${POLY_VERSION}" == "PREPACKAGED" ]]; then
  # check if poly is available
  POLY_CMD=$(which poly || echo "")
  if [[ -z "${POLY_CMD}" ]]; then
    echo "could not find poly, installing polyml now"
    sudo apt install polyml libpolyml-dev
    # check again after installing
    POLY_CMD=$(which poly || echo "")
    if [[ -z "${POLY_CMD}" ]]; then
      echo "couldn't install poly"
      exit 1
    fi
  fi
  echo ${POLY_CMD}
  # try to run poly
  POLY_VERSION_STR=$(poly -v)
  echo "polyml is installed, version: ${POLY_VERSION_STR}"
  # check if the version output is as expected
  if [[ ! "${POLY_VERSION_STR}" =~ ^"Poly/ML " ]]; then
    echo "something is wrong with the version string"
    exit 2
  fi
  exit 0
fi

# if the output directory exists, we already have a polyml in the cache
if [[ -d "${POLY_DIR}" ]]; then
  echo "polyml is already available in the cache, exiting."
  exit 0
else
  echo "polyml is not in the cache, downloading it now."
fi

# prepare directories
mkdir "${POLY_DIR_SRC}"
mkdir "${POLY_DIR}"

# download polyml
wget -qO- ${POLY_URL} | \
  tar xvz -C "${POLY_DIR_SRC}" --strip-components 1

# compile polyml
cd "${POLY_DIR_SRC}"
echo "*** Configuring PolyML for prefix: ${POLY_DIR}"
./configure --prefix="${POLY_DIR}"
make

# install polyml to prefix dir
make install

# remove source directory
cd "${HOLBA_OPT_DIR}"
rm -rf "${POLY_DIR_SRC}"

