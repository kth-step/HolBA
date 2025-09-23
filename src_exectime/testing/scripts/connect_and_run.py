#!/usr/bin/env python3

import subprocess
import time
import sys

makeswitches = ["--silent", "--ignore-errors", "--no-print-directory"]

rdycheck__exec = ["scripts/check_ready.sh"]
clscheck__exec = ["scripts/check_closed.sh"]
connect_exec = ["make"] + makeswitches + ["connect"]
runlog__exec = ["make"] + makeswitches + ["runlog"]

tempfile = "./temp/interactive.log"

retval = subprocess.call(rdycheck__exec)
if retval == 0:
	raise Exception("connection has already been established, find the running process and stop it first")

print( "---------------------------")
print(f"interactive output > {tempfile}")
print( "---------------------------")

subprocess.call(["mkdir", "-p", "temp"])
subprocess.call(["rm", "-f", tempfile])


with open(tempfile, "w+") as connectlog:
	connectlog.flush()
	connectproc = subprocess.Popen(connect_exec, stdin=subprocess.PIPE, stdout=connectlog, stderr=subprocess.STDOUT)
	try:
		# wait until the connect process is ready
		found = False
		while not found and connectproc.poll() == None:
			time.sleep(1)
			with open(tempfile, "r") as connectlog_observer:
				for line in connectlog_observer:
					#print(line)
					if line.strip() == "===    finished starting    ===":
						found = True
						break
			print(".", end='')
			sys.stdout.flush()
		print()

		print("checking whether ports are already open")
		for i in range(0,7):
			retval = subprocess.call(rdycheck__exec)
			if retval == 0:
				break
			time.sleep(0.5)

		if retval != 0:
			raise Exception("connection has not been established yet, something is off")
		# wait a bit for some reason, seems like ports are open but server is not ready yet
		time.sleep(1)

		print("starting connect logging")

		print("starting runlog process")
		subprocess.call(runlog__exec)
		print()
		print("finishing runlog process")
		print("finishing connect logging")
	finally:
		print()
		print("terminating connect process")
		connectproc.terminate()
		connectproc.wait()
		while subprocess.call(clscheck__exec, stderr=subprocess.DEVNULL, stdout=subprocess.DEVNULL) != 0:
			print(".", end='', flush=True)
			time.sleep(1)
		print()

