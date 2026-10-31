"""From the 3-fixed conder quotient (FA=3, FB=0, AR=27, BR=28, E=81) to n=170 with FA=1, FB=1, AR=28, BR=28, E=83:
remove two fixed A-vertices k1, k2 (their B-orbits b1, b2 get free slots), keep fixed A k0, add a new regular A-orbit
(index 27) with Q-edges (27, b1, t1), (27, b2, t2) and one fixed B-vertex attached to the new A-orbit. 27 candidates.
usage: orbit_ins.py STATE OUTDIR"""
import sys, os, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from surgery import load, save
FA, FB, Q, fa, fb = load(sys.argv[1])
assert FA == 3 and FB == 0
od = sys.argv[2]; os.makedirs(od, exist_ok=True)
cnt = 0
for k0 in range(3):
    k1, k2 = [k for k in range(3) if k != k0]
    b1, b2 = fa[k1], fa[k2]
    for t1 in range(3):
        for t2 in range(3):
            Q2 = Q + [(27, b1, t1), (27, b2, t2)]
            if len(set(Q2)) != len(Q2): continue
            save(os.path.join(od, "o%02d_%d%d%d.state" % (cnt, k0, t1, t2)), 1, 1, Q2, [fa[k0]], [27])
            cnt += 1
print("wrote", cnt)
