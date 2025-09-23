#!/usr/bin/env python3

import os
import subprocess
import argparse

# parse arguments
parser = argparse.ArgumentParser()
parser.add_argument("gdb_cmd", help="")
parser.add_argument("gdb_remote", help="")
parser.add_argument("gdb_elf", help="")
parser.add_argument("gdb_boardconfig", help="")
parser.add_argument("gdb_mode", help="run/debug/run_exp")
args = parser.parse_args()

gdb_mode = args.gdb_mode
if gdb_mode != "run" and gdb_mode != "debug" and gdb_mode != "run_exp":
	raise Exception(f"not a valid gdb_mode: {gdb_mode}")

def add_gdb_script(l, scriptname, mustexist = False, alt_scriptname = None):
	filename = f"scripts/gdb/{scriptname}.gdb"
	if not os.path.isfile(filename):
		if alt_scriptname != None:
			return add_gdb_script(l, alt_scriptname, mustexist)
		if mustexist:
			raise Exception(f"script file not found: {filename}")
		return l
	return l + ["-x", filename]

gdb_exec_l = [args.gdb_cmd, f"--eval-command=target remote {args.gdb_remote}"]
gdb_exec_l = add_gdb_script(gdb_exec_l, f"reset_{args.gdb_boardconfig}")
gdb_exec_l = add_gdb_script(gdb_exec_l, "load", True)

if os.environ["PROGPLAT_LOAD_ELF_IN"] == "":
	print("!!!! PROGPLAT_LOAD_ELF_IN is empty !!!!")
else:
	gdb_exec_l += ["--eval-command=load " + os.environ["PROGPLAT_LOAD_ELF_IN"], "--eval-command=set confirm off", "--eval-command=delete"]

gdb_exec_l = add_gdb_script(gdb_exec_l, f"prep_{args.gdb_boardconfig}", False, "prep")
gdb_exec_l = add_gdb_script(gdb_exec_l, gdb_mode, True)
gdb_exec_l = gdb_exec_l + [args.gdb_elf]

temprunlog  = "./temp/gdb.log"

run_timeout = None
if gdb_mode == "run_exp":
	# read timeout for run from config file
	with open("Makefile.config", "r") as f:
		for line in f:
			if line.strip() == "":
				continue
			parts = line.split("=")
			assert len(parts) == 2
			k = parts[0].strip()
			v = parts[1].strip()
			if k.upper() == "PROGPLAT_RUN_TIMEOUT":
				assert run_timeout == None
				run_timeout = int(v)
	# default value
	if run_timeout == None:
		run_timeout = None
	# value range
	if run_timeout < 0:
		raise Exception("run_timeout cannot be negative")
	# special value for no timeout
	if run_timeout == 0:
		run_timeout = None

print( "---------------------------")
print(f"gdb log  > {temprunlog}")
print( "---------------------------")

subprocess.call(["mkdir", "-p", os.path.dirname(temprunlog)])
subprocess.call(["rm", "-f", temprunlog])

with open(temprunlog, "w") as runlog:
	print("starting run logging")

	if gdb_mode == "run_exp":
		gdb_stdin  = subprocess.PIPE
		gdb_stdout = runlog
		gdb_stderr = subprocess.STDOUT
	else:
		gdb_stdin  = None
		gdb_stdout = None
		gdb_stderr = None

	try:
		subprocess.call(gdb_exec_l, stdin=gdb_stdin, stdout=gdb_stdout, stderr=gdb_stderr, timeout=run_timeout)
	except subprocess.TimeoutExpired:
		print("!" * 60)
		print("!!! the execution on the board didn't finish. something is off.")
		print("!" * 60)
		raise
	print()
	print("finishing run logging process")

