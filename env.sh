#!/usr/bin/env bash



# get current holba directory path
HOLBA_DIR=$(dirname "${BASH_SOURCE[0]:-${(%):-%x}}")
HOLBA_DIR=$(readlink -f "${HOLBA_DIR}")


#####################################################
# check that this script is sourced
#####################################################

# script needs to run sourced
if [[ "$0" == "$BASH_SOURCE" ]]; then
  echo "ERROR: script is not sourced"
  exit 1
fi


#####################################################
# source config.env.sh
#####################################################

set --
source "${HOLBA_DIR}/config.env.sh"


#####################################################
# source env_derive.sh
#####################################################

set --
source "${HOLBA_DIR}/scripts/setup/env_derive.sh"


