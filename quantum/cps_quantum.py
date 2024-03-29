#!/usr/bin/env python3

from typing import Union, Callable
from dataclasses import dataclass, is_dataclass
from math import sqrt

# int to specify the index of wire
# bool to specify a fixed input
Exp = int | bool

@dataclass
class CCX:
  x: Exp
  y: Exp
  z: Exp

@dataclass
class H: x: Exp

Gate = CCX | H
Circuit = list[Gate]
hscale: float = 1.0 / sqrt(2.0)
summary: dict[tuple[bool], float] = {}

@dataclass
class State:
  p: float
  bs: tuple[bool]
  def isSet(self, x: Exp) -> bool:
    if isinstance(x, bool): return x
    return self.bs[x]

def neg(bs: tuple[bool], x: int) -> tuple[bool]:
  ls = list(bs)
  ls[x] = not bs[x]
  return tuple(ls)

def evalGate(g: Gate, s: State, k: Callable[[State], None]) -> None:
  if isinstance(g, CCX):
    if s.isSet(g.x) and s.isSet(g.y):
      k(State(s.p, neg(s.bs, g.z)))
    else: k(s)
  if isinstance(g, H):
    if s.isSet(g.x):
      k(State(hscale * s.p, neg(s.bs, g.x)))
      k(State(-1.0 * hscale * s.p, s.bs))
    else:
      k(State(hscale * s.p, neg(s.bs, g.x)))
      k(State(hscale * s.p, s.bs))

def evalCircuit(c: Circuit, s: State, k: Callable[[State], None]) -> None:
  if len(c) == 0: k(s)
  else: evalGate(c[0], s, lambda s: evalCircuit(c[1:], s, k))

def summarize(s: State) -> None:
  if s.bs in summary: summary[s.bs] = summary[s.bs] + s.p
  else: summary[s.bs] = s.p

def runCircuit(c: Circuit, s: State) -> None:
  summary = {}
  evalCircuit(c, s, summarize)

#######################

bell = [H(0), CCX(True, 0, 1)]
runCircuit(bell, State(1.0, (False, False)))
print(summary)
