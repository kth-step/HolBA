#!/bin/bash

# exit immediately if an error happens
set -e

# for the cache
export CACHE_DIR=$HOME/cache

# make polyml binaries and libraries available
export PATH=$CACHE_DIR/polyml/bin:$PATH
export LD_LIBRARY_PATH=$CACHE_DIR/polyml/lib:$LD_LIBRARY_PATH


