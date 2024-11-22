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
"""
CNOT = array([
  [1, 0, 0, 0],
  [0, 1, 0, 0],
  [0, 0, 0, 1],
  [0, 0, 1, 0]
])
"""

Id1 = Id(1)
Id2 = Id(2)
Id4 = Id(4)
Id8 = Id(8)

Zr2 = zeros((2, 2), dtype=complex)
Zr4 = zeros((4, 4), dtype=complex)
Zr8 = zeros((8, 8), dtype=complex)

InvId2 = array([[0, 1],
                [1, 0]])
CNOT = np.block([[Id2, Zr2],
                 [Zr2, InvId2]])
isq2 = 1.0 / (2.0 ** 0.5)
H = isq2 * array([
  [1,  1],
  [1, -1],
], dtype=complex)

def simon():
  x1 = Id1
  x2 = Id8
  x4 = Init(4)
  x5 = Id2
  x6 = Id4

  x3 = kron(H, x2)
  t6 = kron(H, x6)
  t11 = kron(SWAP, x6) #TODO: how to decompose SWAP
  t12 = kron(SWAP, x5)

  #x3 = kron(kron(x1, H), x2)
  #   = kron(H, x2)
  x4 = matmul(x3, x4)

  # kron(Id2, H) == t1
  t1 = np.block([[H, Zr2],
                 [Zr2, H]])
  # kron(Id2, CNOT) == t2
  t2 = np.block([[CNOT, Zr4],
                 [Zr4, CNOT]])
  # kron(Id2, SWAP) == t3
  t3 = np.block([[SWAP, Zr4],
                 [Zr4, SWAP]])
  t4 = np.block([[t3, Zr8],
                 [Zr8, t3]])
  t5 = np.block([[t2, Zr8],
                 [Zr8, t2]])
  # kron(Id1, H) == H

  #t7 = Zr8 #kron(Zr2, x6)
  #t8 = kron(kron(x5, H), x6)
  #   = kron(kron(Id2, H), x6)
  #   = kron(t1, x6)
  #   = [[kron(H, x6), kron(Zr2, x6)],
  #      [kron(Zr2, x6), kron(H, x6)]
  #   = [[t6, Zr8],
  #      [Zr8, t6]]
  t8 = np.block([[t6, Zr8],
                 [Zr8, t6]])

  InvId4 = np.block([[Zr2, x5],
                     [x5, Zr2]])
  # t9 = kron(CNOT, x5)
  #    = [[kron(Id2, x5), kron(Zr2, x5)],
  #    =  [kron(Zr2, x5), kron(InvId2, x5)]
  #    = [[[x5, Id2], Zr4],
  #        [Id2, x5]
  #    =  [Zr4, [Zr2, x5]
  #             [x5, Zr2]]
  #    = [[Id4, Zr4],
  #       [Zr4, Id4]]
  t9 = np.block([[Id4, Zr4],
                 [Zr4, InvId4]])
  # t10 = kron(kron(Id2, CNOT), x5)
  #     = kron(t2, x5)
  #     = [[kron(CNOT, x5), kron(Zr4, x5)],
  #        [kron(Zr4, x5, kron(CNOT, x5)]]
  #     = [[t9, Zr8],
  #        [Zr8, t9]]
  t10 = np.block([[t9, Zr8],
                  [Zr8, t9]])

  # t4 = kron(kron(x6, SWAP), x1)
  #    = kron(kron(Id4, SWAP), x1)
  #    = kron(t4, x1)
  #    = t4

  # t13 = kron(kron(x5, SWAP), x5)
  #     = kron(t3, x5)
  #     = [[kron(SWAP, x5), kron(Zr4, x5)],
  #        [kron(Zr4, x5), kron(SWAP, x5)]]
  #     = [[t12, Zr8],
  #        [Zr8, t12]]
  t13 = np.block([[t12, Zr8],
                  [Zr8, t12]])

  # t15 = kron(kron(x5, H), x6)
  #     = kron(t1, x6)
  #     = [[kron(H, x6), kron(Zr2, x6)],
  #        [kron(Zr2, x6), kron(H, x6)]
  #     = [[t6, Zr8],
  #        [Zr8, t6]]
  t15 = np.block([[t6, Zr8],
                  [Zr8, t6]])

  x4 = matmul(t8, x4)
  x4 = matmul(t11, x4)
  x4 = matmul(t10, x4)
  x4 = matmul(t4, x4)
  x4 = matmul(t10, x4)
  x4 = matmul(t11, x4)
  x4 = matmul(t13, x4)
  x4 = matmul(t5 , x4)
  x4 = matmul(t13, x4)
  x4 = matmul(t10, x4)
  x4 = matmul(x3, x4)
  x4 = matmul(t15, x4)
  print_result(x4, 2 ** 4)

timeOf(10, simon)
