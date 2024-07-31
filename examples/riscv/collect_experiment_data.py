#!/usr/bin/env python3

import argparse
import subprocess
import os
import sys
import traceback
import re
import shutil
from datetime import datetime

parser = argparse.ArgumentParser()
parser.add_argument("-t", "--testing",        help="run in test mode", action="store_true")
parser.add_argument("-ch", "--clearholheap",  help="clear the holheap in directory common", action="store_true")
parser.add_argument("-c", "--clear",          help="clear the example directories before running", action="store_true")
parser.add_argument("-f", "--fast",           help="exclude long-running examples", action="store_true")
args = parser.parse_args()

def get_example_dirs():
	excluded_dirs = ["common", "motor-unopt"] + (["aes", "aes-unopt"] if args.fast else [])
	filterfun = lambda x: not x.startswith(".")
	path = os.getcwd()
	example_dirs = [f.path for f in os.scandir(path) if f.is_dir() and f.name not in excluded_dirs and filterfun(f.name)]
	return example_dirs

def backup_file(path):
	now = datetime.now()
	datetimestr = now.strftime("%Y-%m-%d_%H-%M-%S")
	backuppath = path + "_backup_" + datetimestr
	shutil.copyfile(path, backuppath)

def holmake_clean_dir(path):
	print(f"-> running 'Holmake cleanAll' in '{path}'")
	result = subprocess.run(["${HOLBA_HOL_DIR}/bin/Holmake cleanAll"], shell=True, cwd=path, check=True)

def remove_holheap():
	path = os.getcwd()
	holheap_path = os.path.join(path, "common/examples-riscv-common-heap")
	os.remove(holheap_path)

def holmake_dir(path):
	print(f"-> running 'Holmake' in '{path}'")
	result = subprocess.run(["${HOLBA_HOL_DIR}/bin/Holmake"], shell=True, cwd=path, check=True)

def find_symbexec_logs(path):
	logfile_paths = [f.path for f in os.scandir(os.path.join(path, ".hollogs")) if f.is_file() and f.name.endswith("_symb_execTheory")]
	return logfile_paths

def clean_output(data):
	startstr = "======\n > bir_symb_analysis_thm started\n"
	endstr = "======\n > bir_symb_analysis_thm took "
	symbexec_runs = []
	while True:
		startidx = data.find(startstr)
		if startidx < 0:
			break
		endidx1 = data[startidx:].find(endstr)
		if endidx1 < 0:
			raise Exception("should find this, something in the output is wrong")
		endidx2 = data[startidx+endidx1+len(endstr):].find("\n")
		if endidx2 < 0:
			raise Exception("should find a newline here, something in the output is wrong")
		endidx = startidx+endidx1+len(endstr)+endidx2
		symbexec_runs.append(data[startidx:endidx])
		data = data[endidx:]
	return symbexec_runs

def parse_output(data):
	data = data.split("\n")[-5:]
	#exec_parts_time = data[1][19:]
	exec_all_time = data[4][30:]
	return f"{exec_all_time}"

def collect_outputs(path):
	log_paths = find_symbexec_logs(path)
	for log_path in log_paths:
		backup_file(log_path)
	#print(log_paths)
	outputs = []
	for log_path in log_paths:
		print(f"Reading log '{log_path}'")
		with open(log_path,"r") as file:
			logname = log_path.split("/")[-3] + "/" + log_path.split("/")[-1][:-(len("_symb_execTheory"))]
			data = file.read()
			i = 0
			for symbexec_run in clean_output(data):
				out = parse_output(symbexec_run)
				outputs.append((logname + "/" + str(i), out))
				i += 1
	return outputs

def present_output(output):
	(logname, out) = output
	result = ""
	result += f"{logname}:\n"
	result += f"  {out}\n"
	return result

example_data = """
/home/andreas/data/hol/HolBA_symbexec/src/tools/symbexec/birs_composeLib.sml:247: warning: Matches are not exhaustive. Found near fn ([t]) => t
<<HOL message: Created theory "isqrt_symb_exec">>

======
 > bir_symb_analysis_thm started

>>>>>> executed step in 0.036s

>>>>>> STEP in 0.001s

>>>>>> SUBST in 0.000s
now reducing it to one sound structure

sequential composition with singleton mid_state set

>>>>>> executed step in 0.020s

>>>>>> SUBST in 0.000s

>>> took and sequentially composed a step in 0.032s

sequential composition with singleton mid_state set

>>>>>> executed step in 0.034s

>>>>>> SUBST in 0.000s

>>> took and sequentially composed a step in 0.043s

sequential composition with singleton mid_state set

>>>>>> executed step in 0.020s

>>>>>> SUBST in 0.000s

>>> took and sequentially composed a step in 0.028s

no executable states left, terminating here

======
 > exec_until took 0.110s

======
 > bir_symb_analysis_thm took 0.721s
[oracles: DISK_THM] [axioms: ]
Saved theorem _______ "isqrt_bsysprecond_1_thm"
[oracles: DISK_THM] [axioms: ]
Saved theorem _______ "isqrt_symb_analysis_1_thm"

======
 > bir_symb_analysis_thm started

>>>>>> executed step in 0.033s

>>>>>> STEP in 0.001s

>>>>>> SUBST in 0.000s
now reducing it to one sound structure

sequential composition with singleton mid_state set

>>>>>> executed step in 0.018s

>>>>>> SUBST in 0.000s

>>> took and sequentially composed a step in 0.030s

sequential composition with singleton mid_state set

>>>>>> executed step in 0.035s

>>>>>> SUBST in 0.001s

>>> took and sequentially composed a step in 0.046s

sequential composition with singleton mid_state set

>>>>>> executed step in 0.021s

>>>>>> SUBST in 0.001s

>>> took and sequentially composed a step in 0.029s

sequential composition with singleton mid_state set

>>>>>> executed step in 0.040s

>>>>>> SUBST in 0.000s

>>> took and sequentially composed a step in 0.048s

sequential composition with singleton mid_state set

>>>>>> executed step in 0.022s

>>>>>> SUBST in 0.000s

>>> took and sequentially composed a step in 0.031s

no executable states left, terminating here

======
 > exec_until took 0.198s

======
 > bir_symb_analysis_thm took 0.460s
[oracles: DISK_THM] [axioms: ]
Saved theorem _______ "isqrt_bsysprecond_2_thm"
[oracles: DISK_THM] [axioms: ]
Saved theorem _______ "isqrt_symb_analysis_2_thm"

======
 > bir_symb_analysis_thm started

>>>>>> executed step in 0.093s

>>>>>> STEP in 0.001s
now reducing it to one sound structure

no executable states left, terminating here

======
 > exec_until took 0.005s

======
 > bir_symb_analysis_thm took 0.332s
[oracles: DISK_THM] [axioms: ]
Saved theorem _______ "isqrt_bsysprecond_3_thm"
[oracles: DISK_THM] [axioms: ]
Saved theorem _______ "isqrt_symb_analysis_3_thm"
Exporting theory "isqrt_symb_exec" ... done.
Theory "isqrt_symb_exec" took 1.4s to build
"""
if args.testing:
	#print("\n..................\n".join(clean_output(example_data)))
	output = ("testdata", parse_output(clean_output(example_data)[0]))
	print(output)
	present_output(output)
	sys.exit()

# --------------------------------------------

if args.clearholheap:
	remove_holheap()

example_dirs = get_example_dirs()
#print(example_dirs)
exceptions_happened = False
collected_outputs = []
for path in example_dirs:
	try:
		print()
		if args.clear:
			holmake_clean_dir(path)
		holmake_dir(path)
		outputs = collect_outputs(path)
		collected_outputs.extend(outputs)
	except Exception:
		exceptions_happened = True
		#collect_errors += f"Exception during execution of '{path}'\n"
		print(traceback.format_exc())

print()
print("=====================")
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

