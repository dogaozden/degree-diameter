"""Double surgery from a free (FA=FB=0) n=168 state to n=172 (FA=FB=2): delete quotient edges i < j, attach
fixed A-vertices to the B-orbits of qb[i], qb[j] and fixed B-vertices to the A-orbits of qa[i], qa[j].
usage: dsurgery.py STATE OUTDIR"""
import sys, os, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from surgery import load, save
FA, FB, Q, fa, fb = load(sys.argv[1])
assert FA == 0 and FB == 0
od = sys.argv[2]; os.makedirs(od, exist_ok=True)
cnt = 0
for i, j in itertools.combinations(range(len(Q)), 2):
    Q2 = [q for k, q in enumerate(Q) if k not in (i, j)]
    save(os.path.join(od, "d%04d_%03d_%03d.state" % (cnt, i, j)), 2, 2, Q2,
         [Q[i][1], Q[j][1]], [Q[i][0], Q[j][0]])
    cnt += 1
print("wrote", cnt)
