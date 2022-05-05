#!/usr/bin/python3
import numpy as np
import matplotlib.pyplot as plt

resolve = np.genfromtxt('resolve', delimiter=',', names=['size', 'time'])

plt.plot(resolve['size'], resolve['time'], label='Execution time for resolve_indirect_jumps on synthetic BIR programs')
plt.xlabel('Program size (middle blocks)')
plt.ylabel('Time (seconds)')
plt.title('Experiment 1')
plt.legend()
plt.savefig('resolve.png')

plt.figure()


partial_resolve = np.genfromtxt('partial_resolve', delimiter=',', names=['size', 'time'])

plt.plot(partial_resolve['size'], partial_resolve['time'], label='Execution time for resolve_indirect_jumps on synthetic BIR programs')
plt.xlabel('Program size (middle blocks)')
plt.ylabel('Time (seconds)')
plt.title('Experiment 2')
plt.legend()
plt.savefig('partial_resolve.png')

plt.figure()


constant_resolve = np.genfromtxt('constant_resolve', delimiter=',', names=['size', 'time'])

plt.plot(constant_resolve['size'], constant_resolve['time'], label='Execution time for resolve_indirect_jumps on synthetic BIR programs')
plt.xlabel('Program size (middle blocks)')
plt.ylabel('Time (seconds)')
plt.title('Experiment 3')
plt.legend()
plt.savefig('constant_resolve.png')

plt.figure()


transfer = np.genfromtxt('transfer', delimiter=',', names=['size', 'time'])

plt.plot(transfer['size'], transfer['time'], label='Execution time for transfer_contract on synthetic BIR programs')
plt.xlabel('Program size (middle blocks)')
plt.ylabel('Time (seconds)')
plt.title('Experiment 4')
plt.legend()
plt.savefig('transfer.png')

plt.show()
