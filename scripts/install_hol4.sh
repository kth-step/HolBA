#!/bin/bash

# exit immediately if an error happens
set -e

# setup environment
. ${ENV_EXPORT_SCRIPT}

# go to cache directory
mkdir -p ${CACHE_DIR}
cd ${CACHE_DIR}

# HOL source and branch
GIT_URL=git://github.com/kth-step/HOL.git
GIT_BRANCH=for_holba



# if HOL does exist, check if it is up-to-date and remove it in case it is not
if [ -d "HOL" ]; then
  cd HOL
  git fetch origin

  # does the remote branch exist locally?
  if [ ! `git branch --all --list origin/${GIT_BRANCH}` ]; then
    echo "the cached HOL4 version seems to be on another branch, deleting it now"
    # delete the stale HOL4 build
    cd ..
    rm -rf HOL
  else
    # is there a difference between the current and the remote branch?
    GIT_DIFF=$(git diff)
    GIT_DIFF_REMOTE=$(git diff HEAD remotes/origin/${GIT_BRANCH})
    if [ "${GIT_DIFF}${GIT_DIFF_REMOTE}" ]; then
      echo "the cached HOL4 version has differences, deleting it now"
      # delete the stale HOL4 build
      cd ..
      rm -rf HOL
    else
      echo "the cached HOL4 version is correct, keeping it"
      cd ..
    fi
  fi
fi



# if HOL does not exist already, clone and build
if [ -d "HOL" ]
then
  cd HOL
else
  # clone the right HOL4 branch
  git clone -b ${GIT_BRANCH} --single-branch ${GIT_URL}
  cd HOL

  # compile HOL4
  poly < tools/smart-configure.sml
  bin/build --nograph
fi



# build some l3 models
#(cd examples/l3/.. && ${CACHE_DIR}/HOL/bin/Holmake)

