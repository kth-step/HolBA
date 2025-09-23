#!/usr/bin/env python3


import sys
import os
sys.path.append(os.path.join(os.path.dirname(__file__), "lib"))

import threading

import balrobcomm
import balrob

from tkinter import *

with balrobcomm.BalrobComm() as bc:
	def readloop():
		while True:
			balrob.handle_message(bc, balrob.package_handler)
	threading.Thread(target = readloop, daemon=True).start()

	master = Tk()
	kp_scale = Scale(master, from_=-1.0, to=1.0, resolution=0.002, orient=HORIZONTAL, length=1000)
	kp_scale.set(0.0)
	ki_scale = Scale(master, from_=-1.0, to=1.0, resolution=0.002, orient=HORIZONTAL, length=1000)
	ki_scale.set(0.0)
	kd_scale = Scale(master, from_=-0.1, to=0.1, resolution=0.0002, orient=HORIZONTAL, length=1000)
	kd_scale.set(0.0)
	angle_scale = Scale(master, from_=-1.0, to=1.0, resolution=0.002, orient=HORIZONTAL, length=1000)
	angle_scale.set(0.0)

	kp_scale.set(0.096)
	ki_scale.set(0.096)
	kd_scale.set(0.0124)

	def rob_motor_on():
		balrob.set_motor(bc, True)
	def rob_motor_off():
		balrob.set_motor(bc, False)
	def rob_update_values():
		# (0.398, 0.002, 0.0084)
		# -14.206
		kp_base = 0.0
		ki_base = 0.0
		kd_base = 0.0
		angle_base = -3

		kp_val = kp_base + kp_scale.get() *1
		ki_val = ki_base + ki_scale.get() *1
		kd_val = kd_base + kd_scale.get() *1
		angle_val = angle_base + angle_scale.get() *10

		balrob.set_pid_kp(bc, kp_val)
		balrob.set_pid_ki(bc, ki_val)
		balrob.set_pid_kd(bc, kd_val)
		balrob.set_angle(bc, angle_val)

	def rob_run0():
		balrob.set_exec(bc, 0)
	def rob_run1():
		balrob.set_exec(bc, 0)
	def rob_prog():
		balrob.send_binary(bc, "output/balrob.elf.reloadtext", 1, False)
	def rob_verif():
		balrob.send_binary(bc, "output/balrob.elf.reloadtext", 1, True)

	Label(master, text="Kp").pack()
	kp_scale.pack()
	Label(master, text="Ki").pack()
	ki_scale.pack()
	Label(master, text="Kd").pack()
	kd_scale.pack()
	Label(master, text="angle").pack()
	angle_scale.pack()
	Label(master, text="buttons").pack()
	Button(master, text='Update values', command=rob_update_values).pack()
	Button(master, text='Motor OFF', command=rob_motor_off).pack()
	Button(master, text='Motor ON', command=rob_motor_on).pack()
	Label(master, text="program&exec").pack()
	Button(master, text='E-base', command=rob_run0).pack()
	Button(master, text='Program', command=rob_prog).pack()
	Button(master, text='Verify', command=rob_verif).pack()
	Button(master, text='E-sw', command=rob_run1).pack()

	try:
		mainloop()
	except KeyboardInterrupt:
		pass

#

