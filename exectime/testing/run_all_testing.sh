#!/usr/bin/env bash

rm -rf testing_logs
mkdir testing_logs

make && rm -rf output && mkdir output && cp output_o0_floortop/* output/ && make run

cd pyRC
./benchmark.py -h
./benchmark.py ldldbr8 > ../testing_logs/ldldbr8_o0_output.txt
./benchmark.py aes > ../testing_logs/aes_o0_output.txt
./benchmark.py modexp > ../testing_logs/modexp_o0_output.txt
./benchmark.py modexp_uidivmod > ../testing_logs/modexp_uidivmod_o0_output.txt
./benchmark.py motor_set > ../testing_logs/motor_set_o0_output.txt
./benchmark.py balrob_fadd > ../testing_logs/balrob_fadd_o0_output.txt
./benchmark.py balrob_fdiv > ../testing_logs/balrob_fdiv_o0_output.txt
./benchmark.py balrob > ../testing_logs/balrob_o0_output.txt
cd ..

rm -rf output && mkdir output && cp output_o3_floortop/* output/ && make run
cd pyRC
./benchmark.py motor_set > ../testing_logs/motor_set_o3_output.txt
cd ..

