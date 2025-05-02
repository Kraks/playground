import time
import numpy as np
from numpy import kron, matmul, array, eye, absolute, real, imag, log2, zeros, sqrt

c1 = array([[1, 0, 0, 0],
            [0, 0, 0, 1],
            [0, 0, 1, 0],
            [0, 1, 0, 0]])

c2 = array([
  [1, 0, 0, 0],
  [0, 1, 0, 0],
  [0, 0, 0, 1],
  [0, 0, 1, 0]
])

SWAP = array([
  [1, 0, 0, 0],
  [0, 0, 1, 0],
  [0, 1, 0, 0],
  [0, 0, 0, 1]
])

print(matmul(matmul(c1, c2), c1))

print(kron(SWAP, eye(1)))
