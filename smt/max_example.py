from z3 import *
from dataclasses import dataclass

count = 0
def fresh() -> str:
    global count
    s = "x{}".format(count)
    count += 1
    return s

def check(opt):
    print(opt)
    if opt.check() == sat:
        print('sat')
        print(opt.model())
    else:
        print('unsat')

@dataclass
class SymVec:
    x: ArithRef
    y: ArithRef

def makeSymVec() -> SymVec:
    return SymVec(Real(fresh()), Real(fresh()))

def dist(v1, v2):
    return Sqrt((v1.x - v2.x)**2 + (v1.y - v2.y)**2)

p1 = makeSymVec()
p2 = makeSymVec()
d = Real(fresh())

opt = Optimize()
opt.add(p1.x == 1)
opt.add(p1.y == 0)
opt.add(p2.x == 0)
opt.add(p2.y == 1)
opt.add(((p1.x - p2.x)**2 + (p1.y - p2.y)**2) == d**2)
check(opt)

opt = Optimize()
opt.add(p1.x == 1)
opt.add(p1.y == 0)
opt.add(p2.x < 10)
opt.add(p2.y < 10)
opt.add(p2.x > 0)
opt.add(p2.y > 0)
opt.add(((p1.x - p2.x)**2 + (p1.y - p2.y)**2) == d**2)
opt.maximize(d ** 2)
check(opt)

"""
# hard constraints
# e.g. `add(<constraint>)`
"""

exit()

# soft constraints
# e.g. `add_soft(<constraint>, <constraint_weight>)`
opt.add_soft(x > 5, 10)
opt.add_soft(y > 5, 15)

if opt.check() == sat:
    print(opt.model()) # should print [y = 6, x = -6] because y > 5 has a larger weight than x > 5
else:
    print('unsat')
