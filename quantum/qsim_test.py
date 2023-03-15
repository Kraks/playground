import cirq
import qsimcirq

# Define qubits and a short circuit.
q0, q1 = cirq.LineQubit.range(2)
circuit = cirq.Circuit(cirq.H(q0), cirq.CX(q0, q1))
print("Circuit:")
print(circuit)
print()

# Simulate the circuit with Cirq and return the full state vector.
#print('Cirq results:')
#cirq_simulator = cirq.Simulator()
#cirq_results = cirq_simulator.simulate(circuit)
#print(cirq_results)

#print("---------------------")

# Simulate the circuit with qsim and return the full state vector.
print('qsim results:')
qsim_simulator = qsimcirq.QSimSimulator()
qsim_results = qsim_simulator.simulate(circuit)
print(qsim_results)
