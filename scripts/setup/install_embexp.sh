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

# embexp git urls
GIT_URL_PROG_PLAT=https://github.com/kth-step/EmbExp-ProgPlatform.git
GIT_URL_REMOTE=https://github.com/kth-step/EmbExp-Remote.git

EMBEXP_DIR=${HOLBA_OPT_DIR}/embexp


##################################################################


# if the output directory exists, we already have a embexp in the cache
if [ -d "${EMBEXP_DIR}" ]; then
  echo "embexp is already available in the cache, exiting."
  exit 0
else
  echo "embexp is not in the cache, downloading it now."
fi

# create the containing directory for embexp
mkdir ${EMBEXP_DIR}
cd ${EMBEXP_DIR}

# clone both relevant embexp repositories
git clone ${GIT_URL_PROG_PLAT}
git clone ${GIT_URL_REMOTE}

