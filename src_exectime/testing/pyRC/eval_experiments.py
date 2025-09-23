#!/usr/bin/env python3


import sys
import os
sys.path.append(os.path.join(os.path.dirname(__file__), "lib"))

import json

import benchmarklib

results_dir = "experiment_results"
#results_dir = "experiment_results/../../../BALROB_EXPRESULTS_SAFE/batch1_optimized/binrand_fadd"#/binrand"
#results_dir = "experiment_results/../../../BALROB_EXPRESULTS_SAFE/batch1_optimized/binrand_fdiv"#/binrand"

experiment_results = []
for filename in os.listdir(results_dir):
	filename = os.path.join(results_dir, filename)
	if not filename.endswith(".json"):
		continue
	print(f"loading {filename}")

	with open(filename) as f:
		data = json.load(f)
		assert(type(data) == list)
	experiment_results += data

print(f"found {len(experiment_results)} experiment results")

experiment_results_filtered = [x for x in experiment_results if x[1] != None]

print(f"found {len(experiment_results_filtered)} experiment results that didn't fail")

maxval = max(list(map(lambda x: x[1], experiment_results_filtered)))
minval = min(list(map(lambda x: x[1], experiment_results_filtered)))
print(f"max: {maxval}; min: {minval}")

exps_with_max = list(filter(lambda x: x[1] == maxval, experiment_results_filtered))

# visualize inputs
def convert_inputs(x):
	try:
		return benchmarklib.inputs_to_dict(benchmarklib.base64_to_bytes(x[0]))
	except:
		return x
exps_convertd = list(map(convert_inputs, exps_with_max))

#print(exps_convertd)

