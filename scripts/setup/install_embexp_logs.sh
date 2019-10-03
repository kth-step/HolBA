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
GIT_URL_HTTPS=https://github.com/kth-step/EmbExp-Logs.git
GIT_URL_SSH=git@github.com:kth-step/EmbExp-Logs.git

LOGS_DIR=${HOLBA_LOGS_DIR}/EmbExp-Logs

##################################################################

# if the output directory exists, we already have a embexp-logs
if [[ -d "${LOGS_DIR}" ]]; then
  echo "embexp-logs is already available in the holba_logs directory"
  exit 0
else
  echo "embexp-logs is not in holba_logs, downloading it now."
fi


cd "${HOLBA_LOGS_DIR}"

echo "Do you want to clone with public key authentication?"
select yn in "Yes" "No"; do
  case $yn in
    Yes ) git clone "${GIT_URL_SSH}"; break;;
    No ) git clone "${GIT_URL_HTTPS}"; break;;
  esac
done

