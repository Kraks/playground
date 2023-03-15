import cirq
from cirq import H, X, CX, CCX, Moment
import qsimcirq
import time
import numpy as np

# Get a rectangular grid of qubits.
# qubits = cirq.GridQubit.rect(4, 5)
# Generates a random circuit on the provided qubits.
#circuit = cirq.experiments.random_rotations_between_grid_interaction_layers_circuit(
#    qubits=qubits, depth=16)

# simon's problem
"""
q0, q1, q2, q3 = cirq.LineQubit.range(4)
circuit = cirq.Circuit(
    cirq.H(q0),
    cirq.H(q1),
    cirq.CX(q0, q2),
    cirq.CX(q0, q3),
    cirq.CX(q1, q2),
    cirq.CX(q1, q3),
    cirq.H(q0),
    cirq.H(q1),
)
"""

# rand16
q = cirq.LineQubit.range(16)
cs = [
    H(q[0]), H(q[1]), H(q[2]), H(q[3]), H(q[4]), H(q[5]),
      H(q[6]), H(q[7]), H(q[8]), H(q[9]), H(q[10]), H(q[11]),
      H(q[12]), H(q[13]), H(q[14]), H(q[15]),
      CX(q[0], q[2]), CX(q[0], q[3]), CX(q[1], q[2]), CX(q[1], q[3]), CX(q[5], q[10]), CX(q[6], q[7]), CX(q[1], q[3]),
      CX(q[11], q[8]), CX(q[14], q[3]), CX(q[1], q[12]), CX(q[9], q[3]), CX(q[7], q[10]), CX(q[15], q[4]), CX(q[1], q[13]),
      H(q[11]), H(q[12]), H(q[13]), H(q[14]),
      CCX(q[11], q[2], q[7]), CCX(q[3], q[6], q[8]), X(q[1]), CX(q[1], q[3]),
      CCX(q[2], q[5], q[10]), CX(q[6], q[7]), CX(q[12], q[4]), CX(q[1], q[3]),
      H(q[1]), H(q[2]), H(q[3]), H(q[4]), H(q[5]), H(q[6]), H(q[7]), H(q[8]),
      X(q[10]), CX(q[6], q[7]), CX(q[12], q[4]), CX(q[1], q[3]),
      #cirq.measure(q)
      ]
#circuit = cirq.Circuit(Moment([c]) for c in cs)
circuit = cirq.Circuit(H(q[0]), H(q[1]), H(q[2]), H(q[3]), H(q[4]), H(q[5]),
      H(q[6]), H(q[7]), H(q[8]), H(q[9]), H(q[10]), H(q[11]),
      H(q[12]), H(q[13]), H(q[14]), H(q[15]),
      CX(q[0], q[2]), CX(q[0], q[3]), CX(q[1], q[2]), CX(q[1], q[3]), CX(q[5], q[10]), CX(q[6], q[7]), CX(q[1], q[3]),
      CX(q[11], q[8]), CX(q[14], q[3]), CX(q[1], q[12]), CX(q[9], q[3]), CX(q[7], q[10]), CX(q[15], q[4]), CX(q[1], q[13]),
      H(q[11]), H(q[12]), H(q[13]), H(q[14]),
      CCX(q[11], q[2], q[7]), CCX(q[3], q[6], q[8]), X(q[1]), CX(q[1], q[3]),
      CCX(q[2], q[5], q[10]), CX(q[6], q[7]), CX(q[12], q[4]), CX(q[1], q[3]),
      H(q[1]), H(q[2]), H(q[3]), H(q[4]), H(q[5]), H(q[6]), H(q[7]), H(q[8]),
      X(q[10]), CX(q[6], q[7]), CX(q[12], q[4]), CX(q[1], q[3]))
print("Circuit:")
print(circuit)
print("---------------------------")


# Simulate the circuit with Cirq and print the runtime.
cirq_simulator = cirq.Simulator()
cirq_start = time.time()

for lp in range(1):
  cirq_results = cirq_simulator.simulate(circuit)
print(cirq_results)
#for r in cirq_results.final_state_vector:
#    print(r)
#print(np.around(np.sort(cirq_results.state_vector()), 3))

cirq_elapsed = time.time() - cirq_start
print(f'Cirq runtime: {cirq_elapsed} seconds.')
print("---------------------------")

exit()

# Simulate the circuit with qsim and print the runtime.
qsim_simulator = qsimcirq.QSimSimulator()
qsim_start = time.time()

for lp in range(1):
  qsim_results = qsim_simulator.simulate(circuit)
#print(len(qsim_results.state_vector()))
print(qsim_results)

qsim_elapsed = time.time() - qsim_start
print(f'qsim runtime: {qsim_elapsed} seconds.')
