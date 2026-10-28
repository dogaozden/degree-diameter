"""c15: does H(q) have a perfect code (distance-2 ovoid) in the point collinearity graph?
A perfect code P: every point 2-ball (point + collinear points) contains exactly one point of P.
Each such P has q^3+1 points; a partition of the points into q^2+q+1 perfect codes would give k = q^2+q+1 colours
(the linear projection colourings of proj.py are exactly these partitions).
Usage: python3 pcode.py HEXBIN SECONDS [sym]   (SAT with exact-one per ball, cadical)"""
import sys, time, threading
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/polylev')
from hexlib import Hex
from pysat.solvers import Cadical195
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool

H = Hex(sys.argv[1]); secs = float(sys.argv[2])
N, q = H.N, H.q
B = [[int(x)] + [int(y) for l in H.PL[x] for y in H.lines[l] if y != x] for x in range(N)]
pool = IDPool(start_from=N + 1)
clauses = []
for b in B:
    lits = [int(x) + 1 for x in b]
    clauses.append(lits)                       # at least one
    clauses += [[-a, -c] for i, a in enumerate(lits) for c in lits[i + 1:]]   # at most one (pairwise)
# symmetry breaking: point 0 is in the code (every point is in a code-free ball? no: WLOG by transitivity on points)
clauses.append([1])
s = Cadical195(bootstrap_with=clauses)
t0 = time.time()
timer = threading.Timer(secs, lambda: s.interrupt())
timer.start()
r = s.solve_limited(expect_interrupt=True)
timer.cancel()
print(f'q={q} perfect code: {r} ({time.time() - t0:.1f}s)', flush=True)
if r:
    m = s.get_model()
    P = [x for x in range(N) if m[x] > 0]
    print('size', len(P), 'expected', q ** 3 + 1)
    np.array(P, dtype=np.int64).tofile(sys.argv[1] + '.pcode')
