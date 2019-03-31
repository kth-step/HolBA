#!/bin/bash

export SCAMVBASE=../../../../../
export Z3BASE=${SCAMVBASE}/z3-4.8.4.d6df51951f4c-x64-debian-8.11/

# test setup
#PYTHONPATH=${Z3BASE}/bin/python LD_LIBRARY_PATH=${Z3BASE}/bin python3

export PYTHONPATH=${Z3BASE}/bin/python
export LD_LIBRARY_PATH=${Z3BASE}/bin:$LD_LIBRARY_PATH
export HOL4_Z3_EXECUTABLE=${Z3BASE}/bin/z3

export HOL4_Z3_WRAPPED_EXECUTABLE=${SCAMVBASE}/HolBA/src/libs/z3_wrapper.py


