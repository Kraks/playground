import time
import numpy as np
from numpy import kron, matmul, array, eye, absolute, real, imag, log2, zeros, sqrt

def Init(i):
  s = zeros(2 ** i, dtype=complex)
  s[0] = 1
  return s
def print_binary(index, size_sqrt):
  bin_format = f"0{int(log2(size_sqrt**2))}b"
  binary = format(index, bin_format)
  print(f"{binary}", end="")
def print_result(arr, size):
  print("[", end="")
  for i in range(size):
    if absolute(real(arr[i])) < 1e-18 and imag(arr[i]) == 0.0:
      continue
    print(arr[i], end="")
    print("|", end="")
    print_binary(i, sqrt(size))
    print("⟩", end="")
    if i < size - 1:
      print(", ", end="")
  print("]")

def timeOf(n, f):
  avg = []
  for i in range(0, n):
    start_time = time.time()
    f()
    end_time = time.time()
    duration = end_time - start_time
    avg.append(duration)
    print("iteration %s: %s sec" % (i, duration))
  print("avg: %s sec" % (sum(avg) / len(avg)))
def Id(i): return eye(i, dtype=complex)

SWAP = array([
  [1, 0, 0, 0],
  [0, 0, 1, 0],
  [0, 1, 0, 0],
  [0, 0, 0, 1]
])
CNOT = array([
  [1, 0, 0, 0],
  [0, 1, 0, 0],
  [0, 0, 0, 1],
  [0, 0, 1, 0]
])

Id2 = Id(2)
InvId2 = array([[0, 1],
                [1, 0]])
Z2 = array([[0, 0],
            [0, 0]])
CNOT = np.block([[Id2, Z2],
                 [Z2, InvId2]])
isq2 = 1.0 / (2.0 ** 0.5)
H = isq2 * array([
  [1,  1],
  [1, -1],
], dtype=complex)

def simon():
  x1 = Id(1)
  x2 = Id(8)
  x3 = kron(kron(x1, H), x2)
  x4 = Init(4)
  x4 = matmul(x3, x4)
  x5 = Id(2)
  x6 = Id(4)
  x4 = matmul(kron(kron(x5, H), x6), x4)
  x4 = matmul(kron(kron(x1, SWAP), x6), x4)
  x4 = matmul(kron(kron(x5, CNOT), x5), x4)
  x4 = matmul(kron(kron(x6, SWAP), x1), x4)
  x4 = matmul(kron(kron(x5, CNOT), x5), x4)
  x4 = matmul(kron(kron(x1, SWAP), x6), x4)
  x4 = matmul(kron(kron(x5, SWAP), x5), x4)
  x4 = matmul(kron(kron(x6, CNOT), x1), x4)
  x4 = matmul(kron(kron(x5, SWAP), x5), x4)
  x4 = matmul(kron(kron(x5, CNOT), x5), x4)
  x4 = matmul(kron(kron(x1, H), x2), x4)
  x4 = matmul(kron(kron(x5, H), x6), x4)
  print_result(x4, 2 ** 4)

timeOf(10, simon)
