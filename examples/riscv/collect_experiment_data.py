#!/usr/bin/env python3

import subprocess
import os
import sys
import traceback

def get_example_dirs():
	excluded_dirs = ["common", "motor-unopt"]
	path = os.getcwd()
	example_dirs = [f.path for f in os.scandir(path) if f.is_dir() and f.name not in excluded_dirs]
	return example_dirs

def holmake_clean_dir(path):
	print(f"-> running 'Holmake cleanAll' in '{path}'")
	result = subprocess.run(["${HOLBA_HOL_DIR}/bin/Holmake cleanAll"], shell=True, cwd=path, check=True)

def holmake_dir(path):
	print(f"-> running 'Holmake' in '{path}'")
	result = subprocess.run(["${HOLBA_HOL_DIR}/bin/Holmake"], shell=True, cwd=path, check=True)

def find_symbexec_logs(path):
	logfile_paths = [f.path for f in os.scandir(os.path.join(path, ".hollogs")) if f.is_file() and f.name.endswith("_symb_execTheory")]
	return logfile_paths

def clean_output(data):
	idx_start = 0
	for i in range(len(data)):
		if data[i].startswith(">>>"):
			idx_start = i
			break
	idx_end = len(data) - 1
	for i in reversed(range(len(data))):
		if data[i].startswith(" > bir_symb_analysis"):
			idx_end = i
			break
	return data[idx_start:idx_end+1]

def parse_output(data):
	data = data[-5:]
	exec_parts_time = data[1][19:-1]
	exec_all_time = data[4][26:-1]
	return f"execution of parts: {exec_parts_time}; execution of all: {exec_all_time}"

def collect_outputs(path):
	log_paths = find_symbexec_logs(path)
	#print(log_paths)
	outputs = []
	for log_path in log_paths:
		print(f"Reading log '{log_path}'")
		with open(log_path,"r") as file:
			logname = log_path.split("/")[-3] + "/" + log_path.split("/")[-1][:-(len("_symb_execTheory"))]
			data = file.readlines()
			out = parse_output(clean_output(data))
			outputs.append((logname, out))
	return outputs

def present_output(output):
	(logname, out) = output
	result = ""
	result += f"{logname}:\n"
	result += f"  {out}\n"
	return result

example_data = """
Saved definition ____ "mod2_birenvtyl_def"
Saved theorem _______ "mod2_prog_vars_thm"

>>>>>> executed step in 0.012s

>>>>>> STEP in 0.000s

>>>>>> SUBST in 0.000s
now reducing it to one sound structure

sequential composition with singleton mid_state set

>>>>>> executed step in 0.008s

>>>>>> SUBST in 0.000s

>>> took and sequentially composed a step in 0.011s

no executable states left, terminating here

======
 > exec_until took 0.013s

======
 > bir_symb_analysis took 0.083s
[oracles: DISK_THM] [axioms: ]
Saved theorem _______ "mod2_bsysprecond_thm"
""".splitlines()
if False:
	#print(clean_output(example_data))
	output = ("testdata", parse_output(clean_output(example_data)))
	#print(output)
	present_output(output)
	sys.exit()

example_dirs = get_example_dirs()
#print(example_dirs)

exceptions_happened = False
collected_outputs = []
for path in example_dirs:
	try:
		print()
		#holmake_clean_dir(path)
		holmake_dir(path)
		outputs = collect_outputs(path)
		collected_outputs.extend(outputs)
	except Exception:
		exceptions_happened = True
		#collect_errors += f"Exception during execution of '{path}'\n"
		print(traceback.format_exc())

if exceptions_happened:
	print("Check the output for errors during execution.")
else:
	print("Holmake ran without errors.")

print()
#print(collected_outputs)
collected_results = ""
for output in collected_outputs:
	collected_results += present_output(output)

print(collected_results)
with open("experiment_data.log","w") as file:
	file.write(collected_results)

