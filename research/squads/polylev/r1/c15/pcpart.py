"""c15: partition of the points of H(q) into k perfect codes (every 2-ball contains exactly one point of each colour).
Usage: python3 pcpart.py HEXBIN k SECONDS OUT.bin   (SAT, cadical; OUT.bin: int32 colour per point when SAT)"""
import sys, time, threading
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/polylev')
from hexlib import Hex
from pysat.solvers import Cadical195

H = Hex(sys.argv[1]); k = int(sys.argv[2]); secs = float(sys.argv[3]); out = sys.argv[4]
N, q = H.N, H.q
B = [[int(x)] + [int(y) for l in H.PL[x] for y in H.lines[l] if y != x] for x in range(N)]
v = lambda e, c: e * k + c + 1
cl = []
for e in range(N):
    cl.append([v(e, c) for c in range(k)])
    cl += [[-v(e, a), -v(e, b)] for a in range(k) for b in range(a + 1, k)]
for b in B:
    for c in range(k):
        lits = [v(x, c) for x in b]
        cl.append(lits)
        cl += [[-lits[i], -lits[j]] for i in range(len(lits)) for j in range(i + 1, len(lits))]
# symmetry breaking: the point 0 has colour 0 (colour classes are interchangeable)
cl.append([v(0, 0)])
s = Cadical195(bootstrap_with=cl)
t0 = time.time()
tm = threading.Timer(secs, lambda: s.interrupt()); tm.start()
r = s.solve_limited(expect_interrupt=True); tm.cancel()
print(f'q={q} k={k} perfect-code partition: {r} ({time.time() - t0:.1f}s)', flush=True)
if r:
    m = set(x for x in s.get_model() if x > 0)
    col = np.array([next(c for c in range(k) if v(e, c) in m) for e in range(N)], dtype=np.int32)
    col.tofile(out)
    print('class sizes', np.bincount(col, minlength=k).tolist())
