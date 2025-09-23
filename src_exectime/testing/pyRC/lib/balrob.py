import struct



def handle_message(bc, handler, timeout = None):
	(ch, m) = bc.recv_message(timeout)
	handler(ch, m)

def parse_pid_pack(m):
	#print(m)
	#print(len(m))
	s = struct.unpack("<LLLffffBxxx", m)
	p = {
		"pid_sampletime": s[0],
		"pid_handlertime": s[1],
		"pid_counter": s[2],

		"angle": s[3],
		"error": s[4],
		"errorDiff": s[5],
		"errorSum": s[6],

		"last_noyield": s[7]
	}
	return p

def trydecode(m):
	try:
		return m.decode()
	except:
		return m

def package_handler(ch, m):
	if ch == 0:
		print(f"inf - {trydecode(m)}")
	elif ch == 1:
		print(f"dbg - {trydecode(m)}")
	elif ch == 2:
		print(f"err - {trydecode(m)}")
	elif ch == 10:
		print("pid")
		print(parse_pid_pack(m))
	else:
		print(f"unhandled channel {ch} - {m}")

def send_data(bc, ch, m):
	bc.send_message((ch, m))

def set_motor(comm, is_on):
	m = struct.pack("<l", 1 if is_on else 0)
	send_data(comm, 50, m)

def set_pid_info(comm, is_on):
	m = struct.pack("<l", 1 if is_on else 0)
	send_data(comm, 51, m)

def set_exec(comm, v):
	m = struct.pack("<l", v)
	send_data(comm, 80, m)

def add_angle(comm, a):
	m = struct.pack("<f", a)
	send_data(comm, 71, m)

def reset_uploads(comm):
	m = struct.pack("<l", 0)
	send_data(comm, 81, m)

def send_code(comm, mloc, dat, verify_data = True):
	c = 82 if verify_data else 83
	m = struct.pack("<L", mloc)
	send_data(comm, c, m+dat)

def send_binary(comm, filename, idx, verify_data = True):
	s_procedure = "verification" if verify_data else "writing"
	print(f"start {s_procedure} - {filename} - {idx}")
	reset_uploads(comm)

	#send_code(comm, 0x0, b"\xb0\xb5")
	#send_code(comm, 0x2, b"\x98\xb0")
	#return

	print("")
	with open(filename, "rb") as f:
		filelength = 0xa00
		for _ in range(idx):
			f.read(filelength)
		chunksize = 200
		n_processed = 0
		for addr in range(0xa00):
			if addr % chunksize != 0:
				continue
			mloc = addr + idx * 0xa00
			n_remaining = filelength - n_processed
			n_curchunk = min(chunksize, n_remaining)
			dat = f.read(n_curchunk)
			n_processed += len(dat)
			send_code(comm, mloc, dat, verify_data)
			print(f"\r{n_processed/filelength*100:.{1}f}%", end = '')
	print("")
	print(f"done {s_procedure} - {filename} - {idx}")



def set_pid_kp(comm, v):
	m = struct.pack("<f", v)
	send_data(comm, 60, m)

def set_pid_ki(comm, v):
	m = struct.pack("<f", v)
	send_data(comm, 61, m)

def set_pid_kd(comm, v):
	m = struct.pack("<f", v)
	send_data(comm, 62, m)

def set_angle(comm, v):
	m = struct.pack("<f", v)
	send_data(comm, 70, m)

