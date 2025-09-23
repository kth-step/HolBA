#!/usr/bin/env bash

# exit immediately if an error happens
set -e

# get setup directory path
HOLBA_DIR=$(dirname "${BASH_SOURCE[0]}")/..
HOLBA_DIR=$(readlink -f "${HOLBA_DIR}")

##################################################################

cd $HOLBA_DIR

# run all verifications
make examples/arm_cm0/tiny
make examples/arm_cm0/aes
make examples/arm_cm0/modexp_simple
make examples/arm_cm0/motor_set
make examples/arm_cm0/balrob/v2-faster

# pull all relevant logs
mkdir -p logs/armcm0/holba-se

cp examples/arm_cm0/tiny/.hollogs/tiny_analysisTheory logs/armcm0/holba-se/ldldbr8

cp examples/arm_cm0/aes/.hollogs/aes_o0_wholeTheory logs/armcm0/holba-se/aes

cp examples/arm_cm0/modexp_simple/.hollogs/modexp_asmTheory logs/armcm0/holba-se/modexp
cp examples/arm_cm0/modexp_simple/.hollogs/modexp_asm_uidivmodTheory logs/armcm0/holba-se/modexp_uidivmod

cp examples/arm_cm0/motor_set/.hollogs/motor_o0Theory logs/armcm0/holba-se/motor_set
cp examples/arm_cm0/motor_set/.hollogs/motor_o3Theory logs/armcm0/holba-se/motor_set_o3

cp examples/arm_cm0/balrob/v2-faster/.hollogs/balrob_topTheory logs/armcm0/holba-se/balrob
cp examples/arm_cm0/balrob/v2-faster/.hollogs/balrob_faddTheory logs/armcm0/holba-se/balrob_fadd
cp examples/arm_cm0/balrob/v2-faster/.hollogs/balrob_fdivTheory logs/armcm0/holba-se/balrob_fdiv
