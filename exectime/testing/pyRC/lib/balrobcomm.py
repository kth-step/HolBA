import threading
import queue

import serial
import socket
import sys

import struct
import time

# serial interface
def get_balrob_comm_serial():
	serialdevice = "/dev/serial/by-id/usb-Silicon_Labs_CP2102_USB_to_UART_Bridge_Controller_0001-if00-port0"
	return serial.Serial(serialdevice, 9600, timeout=None)

# tcp interface (embexp remote)
def get_balrob_comm_tcp():
	s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
	s.connect(("localhost", 20000))
	return s

# general function to connect
def get_balrob_comm():
	return get_balrob_comm_tcp()

# general function to read
def read_balrob_comm(comm, n = 1):
	if (type(comm) == serial.Serial):
		return comm.read(n)
	elif (type(comm) == socket.socket):
		buf = b""
		while len(buf) < n:
			buf += comm.recv(n - len(buf))
		return buf
	else:
		raise Exception("unknown comm type - cannot read")

# general function to write
def write_balrob_comm(comm, d):
	if (type(comm) == serial.Serial):
		comm.write(d)
		time.sleep(0.3)
		return None
	elif (type(comm) == socket.socket):
		comm.send(d)
		return None
	else:
		raise Exception("unknown comm type - cannot write")

# decoding of packages received from a comm
def decode_packages_loop(comm, handler):
	n_failpacks = 0
	while True:
		x = None
		while True:
			x = read_balrob_comm(comm)[0]
			if x == 0x55:
				break
			print(f"aaaaaa - {x}")

		x = read_balrob_comm(comm)[0]
		if x != 0xAA:
			print(f"aaaaaa22222 - {x}")
			continue

		m_ch = read_balrob_comm(comm)[0]
		m_len = read_balrob_comm(comm)[0]
		m = read_balrob_comm(comm, m_len)

		m_ok = True
		m_ok = m_ok and (read_balrob_comm(comm)[0] == 0x88)
		m_ok = m_ok and (read_balrob_comm(comm)[0] == 0x11)

		if m_ok:
			msg = (m_ch, m)
			handler(msg)
		else:
			n_failpacks += 1
			print(f"wrong packets = {n_failpacks}")

# encoding of a package and transmission to a comm
def encode_package(comm, ch, m):
	m_len = len(m)
	if m_len >= 255:
		raise Exception(f"message too long ({m_len}): {m}")

	m1 = struct.pack("<BBBB", 0x55, 0xAA, ch, m_len)
	m2 = struct.pack("<BB", 0x88, 0x11)

	msg = m1 + m + m2
	#print(msg)

	write_balrob_comm(comm, msg)

# abstraction for messages (helper classes)
# ======================================================================
class CommInputThread(threading.Thread):
	def __init__(self, comm, state):
		threading.Thread.__init__(self, daemon=True)
		self.comm = comm
		self.state = state

	def run(self):
		self.state.f_thread_rec_ok = True
		try:
			decode_packages_loop(self.comm, lambda msg: self.state.add_element(msg))
		except:
			print(sys.exc_info()[0])
			raise
		finally:
			self.state.f_thread_rec_ok = False

class CommState:
	def __init__(self):
		self.f_thread_rec_ok = False
		self.f_queue = queue.Queue()

	def get_element(self, timeout = 2):
		return self.f_queue.get(timeout=timeout)

	def get_num_available(self):
		return self.f_queue.qsize()

	def add_element(self, e):
		self.f_queue.put(e)

	def check_thread_rec(self):
		if not self.f_thread_rec_ok:
			raise Exception("comm reception handler died")


# abstraction for messages (interface class)
# ======================================================================
class BalrobComm:
	def __init__(self):
		self.comm = get_balrob_comm()
		self.state = CommState()
		self._input_thread = CommInputThread(self.comm, self.state)

	def __enter__(self):
		self.comm.__enter__()
		self._input_thread.start()
		return self

	def __exit__(self, exc_type, exc_val, exc_tb):
		self.comm.__exit__(exc_type, exc_val, exc_tb)

	def recv_message(self, timeout = 2):
		self.state.check_thread_rec()
		return self.state.get_element(timeout)

	def recv_available(self):
		self.state.check_thread_rec()
		return self.state.get_num_available()

	def send_message(self, msg):
		self.state.check_thread_rec()
		(ch, m) = msg
		encode_package(self.comm, ch, m)



