# https://barghouthi.github.io/2021/08/05/quantum/

import numpy as np

""" Representing n bits using 2^n values.
    Examples:

    0 [0
    1  1]
    represents 1, since the value at index 1 is 1.

    0 [1
    1  0]
    represents 0, since the value at index 0 is 1.

    0 0 [1
    0 1  0
    1 0  0
    1 1  0]
    represents [0 0], since its indexed position is 1.
"""

isq2 = 1.0 / (2.0 ** 0.5)

class QState:
  def __init__(self, n):
    self.n = n
    self.state = np.zeros(2 ** self.n, dtype=complex)
    self.state[0] = 1

  def op(self, t, i):
    # I_{2^i}
    eyeL = np.eye(2**i, dtype=complex)
    # I_{2^{n-i-1}}
    eyeR = np.eye(2**(self.n - i - int(t.shape[0]**0.5)), dtype=complex)
    # eyeL ⊗ t ⊗ eyeR
    t_all = np.kron(np.kron(eyeL, t), eyeR)
    self.state = np.matmul(t_all, self.state)

  def NOT(self, i):
    not_matrix = np.array([
      [0, 1],
      [1, 0]
    ])
    self.op(not_matrix, i)

  def SWAP(self, i):
    # swaps bits i and i+1
    swap_matrix = np.array([
      [1, 0, 0, 0],
      [0, 0, 1, 0],
      [0, 1, 0, 0],
      [0, 0, 0, 1]
    ])
    self.op(swap_matrix, i)

  def AND(self, i):
    # and bits i and i+1, the first bit stores the result
    and_matrix = np.array([
      [1, 0, 1, 0],
      [0, 1, 0, 0],
      [0, 0, 0, 0],
      [0, 0, 0, 1]
    ])
    self.op(and_matrix, i)

  def OR(self, i):
    or_matrix = np.array([
      [1, 0, 0, 0],
      [0, 0, 0, 0],
      [0, 0, 1, 0],
      [0, 1, 0, 1]
    ])
    self.op(or_matrix, i)

  def H(self, i):
    h_matrix = isq2 * np.array([
      [1,  1],
      [1, -1],
    ])
    self.op(h_matrix, i)

  def CNOT(self, i):
    # stores the result in the second bit
    cnot_matrix = np.array([
      [1, 0, 0, 0],
      [0, 1, 0, 0],
      [0, 0, 0, 1],
      [0, 0, 1, 0]
    ])
    self.op(cnot_matrix, i)

  # S and T gate doesn't change the prob of amplitudes but the phase of amplitudes
  def s(self, i):
    s_matrix = np.array([
      [1,0],
      [0,1j]
    ])
    self.op(s_matrix,i)

  def t(self, i):
    t_matrix = np.array([
      [1,0],
      [0,isq2 + isq2 * 1j]
    ])
    self.op(t_matrix, i)

# initialize state
# Recall that Cstate initializes all bits to 0
s = QState(2)
s.NOT(0)
s.NOT(1)
s.AND(0)

print(s.state)

# an EPR pair
s = QState(2)
s.H(0)
s.CNOT(0)
s.s(0)
s.t(0)

print(s.state)
