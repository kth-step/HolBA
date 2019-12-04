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

# embexp git urls
GIT_URL_PROG_PLAT_HTTPS=https://github.com/kth-step/EmbExp-ProgPlatform.git
GIT_URL_BOX_HTTPS=https://github.com/kth-step/EmbExp-Box.git

GIT_URL_PROG_PLAT_SSH=git@github.com:kth-step/EmbExp-ProgPlatform.git
GIT_URL_BOX_SSH=git@github.com:kth-step/EmbExp-Box.git

EMBEXP_DIR=${HOLBA_OPT_DIR}/embexp


##################################################################


# if the output directory exists, we already have a embexp in the cache
if [[ -d "${EMBEXP_DIR}" ]]; then
  echo "embexp is already available in the cache, exiting."
  exit 0
else
  echo "embexp is not in the cache, downloading it now."
fi

# create the containing directory for embexp
mkdir ${EMBEXP_DIR}
cd ${EMBEXP_DIR}

# clone both relevant embexp repositories
echo "Do you want to clone with public key authentication?"
select yn in "Yes" "No"; do
  case $yn in
    Yes ) git clone "${GIT_URL_PROG_PLAT_SSH}"; git clone "${GIT_URL_BOX_SSH}"; break;;
    No ) git clone "${GIT_URL_PROG_PLAT_HTTPS}"; git clone "${GIT_URL_BOX_HTTPS}"; break;;
  esac
done

