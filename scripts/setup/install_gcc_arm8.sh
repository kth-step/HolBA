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


# download package
GCC_URL="https://developer.arm.com/-/media/Files/downloads/gnu-a/8.2-2018.08/gcc-arm-8.2-2018.08-x86_64-aarch64-elf.tar.xz"

GCC_DIR=${HOLBA_OPT_DIR}/gcc-arm8-8.2-2018.08-aarch64-elf








##################################################################


# if the output directory exists, we already have a gcc in the cache
if [[ -d "${GCC_DIR}" ]]; then
  echo "gcc_arm8 is already available in the cache, exiting."
  exit 0
else
  echo "gcc_arm8 is not in the cache, downloading it now."
fi

# download gcc
mkdir "${GCC_DIR}"
wget -qO- ${GCC_URL} | tar -xJ -C "${GCC_DIR}" --strip-components 1


