#!/usr/bin/env python3


import sys
import os
sys.path.append(os.path.join(os.path.dirname(__file__), "lib"))

import threading
import time
import json

from datetime import datetime
import os
import argparse

import balrobcomm
import benchmarklib

# parse arguments
parser = argparse.ArgumentParser()
parser.add_argument("experiment_name", help="select from: ldldbr8, aes, modexp, modexp_uidivmod, motor_set, balrob, balrob_fadd, balrob_fdiv")
args = parser.parse_args()

# beginning of the script
# ===============================================================
print("generating inputs")
special_inputs = benchmarklib.dict_to_inputs(benchmarklib.fixed_inputs_dict_5)
num_exps = 1000
inputs_list = [benchmarklib.gen_random_inputs_binary() for _ in range(num_exps)]
#inputs_list = [benchmarklib.gen_random_inputs_distribution() for _ in range(num_exps)]
#inputs_list = [special_inputs]
#inputs_list = [benchmarklib.gen_random_input_binary_k_variation(special_inputs) for _ in range(num_exps)]

experiment_results = []
now_str = datetime.now().strftime("%Y-%m-%d_%H-%M-%S")
results_dir = "experiment_results"
experiment_results_filename = f"{results_dir}/{now_str}.json"
if not os.path.isdir(results_dir):
	os.mkdir(results_dir)

#experiment_name = "ldldbr8"
#experiment_name = "aes"
#experiment_name = "modexp_uidivmod"
#experiment_name = "modexp"
#experiment_name = "motor_set"
#experiment_name = "balrob_fadd"
#experiment_name = "balrob_fdiv"
#experiment_name = "balrob"
experiment_name = args.experiment_name

if experiment_name != "balrob":
	overall_start_time = time.time()
	min_exp = (9999999999, None)
	max_exp = (0, None)
	experiment_results = []
	try:
		with balrobcomm.BalrobComm() as bc:
			for _ in range(num_exps):
				a = benchmarklib.gen_rand_float()
				b = benchmarklib.gen_rand_float()
				c = benchmarklib.gen_rand_int32()
				d = benchmarklib.gen_rand_int32()
				#c = benchmarklib.gen_rand_uint32()
				#d = benchmarklib.gen_rand_uint32()
				#e = benchmarklib.gen_rand_uint32()
				#inputs_s = (a, b)
				inputs_s = (c, d)
				#inputs_s = (c, d, e)
				#inputs_s = (c,)
				cycles = None
				try:
					# --------
					# ----- the ldldbr8 example only has one function
					# ----- this function takes no arguments
					# --------
					if experiment_name == "ldldbr8":
						cycles = benchmarklib.run_experiment__reffunc_test4(bc)

					# --------
					# ----- the aes example only has one function
					# ----- this experiment handles random input generation internally
					# --------
					elif experiment_name == "aes":
						cycles = benchmarklib.execute_experiment_my_aes(bc)

					# --------
					# ----- the modexp example consists of the modexp function and the modulo emulation function
					# ----- my_modexp_asm takes 3 int arguments, my_uidivmod_mod_asm takes two uints
					# --------
					elif experiment_name == "modexp_uidivmod":
						c = benchmarklib.gen_rand_uint32()
						d = benchmarklib.gen_rand_uint32()
						inputs_s = (c, d)
						cycles = benchmarklib.execute_experiment__my_uidivmod_mod_asm(bc, *inputs_s)
					elif experiment_name == "modexp":
						c = benchmarklib.gen_rand_uint32()
						d = benchmarklib.gen_rand_uint32()
						e = benchmarklib.gen_rand_uint32()
						inputs_s = (c, d, e)
						cycles = benchmarklib.execute_experiment__my_modexp_asm(bc, *inputs_s)
						#
						#inputs_s = ((2 ** 8) - 1, (2 ** 25) - 1, (2 ** 17) - 1)
						#cycles = benchmarklib.run_experiment__mymodexp(bc, *inputs_s)
						#inputs_s = ((2 ** 32) - 1, 1)
						#cycles = benchmarklib.run_experiment_uidivmod(bc, *inputs_s)

					# --------
					# ----- motor_set_l and motor_set_r are the elementary functions for the motor binary, which internally call motor_prep_input
					# ----- all use int as datatypes; motor_set and motor_set_multi take two arguments, the others take only one
					# ----- for the experiments, only motor_set and motor_set_multi are relevant
					# -------- 
					elif experiment_name == "motor_set":
						c = benchmarklib.gen_rand_int32()
						d = benchmarklib.gen_rand_int32()
						inputs_s = (c, d)
						cycles = benchmarklib.execute_experiment_motor_set(bc, *inputs_s) # call to motor_set (calls motor_set_l and motor_set_r)
					#else if experiment_name == "motor_set_multi":
					#	cycles = benchmarklib.run_experiment_motor_set_multi(bc, *inputs_s) # function that calls to motor_set twice (FRAGILE, ONLY WORKS WITH O3)
					#
					#cycles = benchmarklib.execute_experiment_motor_set_l(bc, *inputs_s)
					#cycles = benchmarklib.execute_experiment_motor_prep_input(bc, *inputs_s)
					#cycles = benchmarklib.execute_experiment__motor_prep_input(bc, *inputs_s)
					#cycles = benchmarklib.execute_experiment__motor_prep_input_mod(bc, *inputs_s)


					# --------
					# ----- the pid example has subfunctions fadd and fdiv, the pid evaluation is further below in this file
					# ----- fadd and fdiv takes two floats, pid has a special input generator and setter (there are no arguments, but several state components in memory)
					# --------
					elif experiment_name == "balrob_fadd":
						a = benchmarklib.gen_rand_float()
						b = benchmarklib.gen_rand_float()
						inputs_s = (a, b)
						cycles = benchmarklib.execute_experiment_fadd(bc, *inputs_s)
					elif experiment_name == "balrob_fdiv":
						a = benchmarklib.gen_rand_float()
						b = benchmarklib.gen_rand_float()
						inputs_s = (a, b)
						cycles = benchmarklib.execute_experiment_fdiv(bc, *inputs_s)
					
          
					print(f"==========>>>>> {cycles}")
					if cycles > max_exp[0]:
						max_exp = (cycles, inputs_s)
					if cycles < min_exp[0]:
						min_exp = (cycles, inputs_s)
				finally:
					experiment_result = (inputs_s, cycles, None)
					experiment_results.append(experiment_result)
	except KeyboardInterrupt:
		print("")
	finally:
		with open(experiment_results_filename, "w") as f:
			json.dump(experiment_results, f)
		print("min cycles experiment:")
		print(min_exp)
		print("max cycles experiment:")
		print(max_exp)
		time_diff = time.time() - overall_start_time
		print(40 * "=")
		print(f"    overall benchmarking time: {time_diff:.2f}s")
		print(40 * "=")
	print("terminating.")
	sys.exit(0)

print("starting experiments")
overall_start_time = time.time()
min_exp = (9999999999, None)
max_exp = (0, None)
try:
	with open(experiment_results_filename + "_log", "w") as f_log:
		f_log.write("[\n")
		with balrobcomm.BalrobComm() as bc:
			# loop through several inputs
			for inputs in inputs_list:
				#inputs = dict_to_inputs(fixed_inputs_dict_2)
				#inputs = gen_random_inputs_binary()
				#inputs = benchmarklib.set_inputs_msg_flag(inputs)
				#inputs = benchmarklib.set_inputs_motor_on(inputs)
				#print(inputs_to_dict(inputs)["motor_on"])

				# prepare inputs for storing
				inputs_s = benchmarklib.bytes_to_base64(inputs)

				# run the experiment
				cycles = None
				time_diff = None
				try:
					start_time = time.time()
					cycles = benchmarklib.execute_experiment(bc, inputs)
					time_diff = time.time() - start_time
					print(f"==========>>>>> {cycles} (exp time: {time_diff:.2f}s)")
					if cycles > max_exp[0]:
						max_exp = (cycles, inputs_s)
					if cycles < min_exp[0]:
						min_exp = (cycles, inputs_s)
				finally:
					# store inputs and cycle count
					time_diff_s = None if time_diff == None else f"{time_diff:.2f}"
					experiment_result = (inputs_s, cycles, time_diff_s)
					experiment_results.append(experiment_result)
					f_log.write(json.dumps(experiment_result))
					f_log.write(",\n")
					f_log.flush()
		f_log.write("null\n]\n")

except KeyboardInterrupt:
	print("")
finally:
	with open(experiment_results_filename, "w") as f:
		json.dump(experiment_results, f)
	print("min cycles experiment:")
	print(min_exp)
	print("max cycles experiment:")
	print(max_exp)
	time_diff = time.time() - overall_start_time
	print(40 * "=")
	print(f"    overall benchmarking time: {time_diff:.2f}s")
	print(40 * "=")

print("terminating.")

