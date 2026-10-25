"""Brute-force check of the two-sided totalizer used by g_sat.py (O[k-1] <-> sum >= k)."""
import itertools, sys
sys.path.insert(0, '/home/user/degree-diameter/research/squads/r3-d8/c7')
from pysat.solvers import Cadical153

class Pool:
    def __init__(self, top=0): self.top = top
    def new(self):
        self.top += 1
        return self.top

def totalizer(lits, pool, cls):
    if len(lits) == 1:
        return [lits[0]]
    h = len(lits) // 2
    A = totalizer(lits[:h], pool, cls)
    B = totalizer(lits[h:], pool, cls)
    p, r = len(A), len(B)
    n = p + r
    O = [pool.new() for _ in range(n)]
    for i in range(p + 1):
        for j in range(r + 1):
            if i + j == 0:
                continue
            c = [O[i + j - 1]]
            if i:
                c.append(-A[i - 1])
            if j:
                c.append(-B[j - 1])
            cls.append(c)
    for i in range(p + 1):
        for j in range(r + 1):
            if i + j + 1 > n:
                continue
            c = [-O[i + j]]
            if i + 1 <= p:
                c.append(A[i])
            if j + 1 <= r:
                c.append(B[j])
            cls.append(c)
    return O

for n in range(1, 8):
    pool = Pool(n)
    cls = []
    ins = list(range(1, n + 1))
    O = totalizer(ins, pool, cls)
    assert len(O) == n
    bad = 0
    for bits in itertools.product([0, 1], repeat=n):
        assum = [ins[i] if bits[i] else -ins[i] for i in range(n)]
        s = Cadical153(bootstrap_with=cls)
        assert s.solve(assumptions=assum)
        m = set(l for l in s.get_model() if l > 0)
        cnt = sum(bits)
        for k in range(n):
            if (O[k] in m) != (cnt >= k + 1):
                bad += 1
        # the outputs must be forced: flipping any output must be UNSAT
        for k in range(n):
            assum2 = assum + [-O[k] if O[k] in m else O[k]]
            if s.solve(assumptions=assum2):
                bad += 1
        s.delete()
    print('n', n, 'bad', bad, 'clauses', len(cls))
