"""Two-edge surgery from an n = 2m state (FA, FB) to n + 2 (FA+1, FB+1), E -> E - 1.
Delete quotient edges i (ao1,bo1,t1) and j (ao2,bo2,t2); add a fixed A vertex on bo1 and a fixed B vertex on ao2 (variant 1)
or on bo2 and ao1 (variant 2), and one new quotient edge (ao1,bo2,t) (variant 1) or (ao2,bo1,t) (variant 2).
usage: surg2.py STATE OUTDIR"""
import sys, os, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from surgery import load, save
FA, FB, Q, fa, fb = load(sys.argv[1])
od = sys.argv[2]; os.makedirs(od, exist_ok=True)
cnt = 0
for i, j in itertools.combinations(range(len(Q)), 2):
    a1, b1, _ = Q[i]; a2, b2, _ = Q[j]
    rest = [q for k, q in enumerate(Q) if k not in (i, j)]
    for t in range(3):
        for var in (1, 2):
            if var == 1:
                newq = (a1, b2, t); fa2 = fa + [b1]; fb2 = fb + [a2]
            else:
                newq = (a2, b1, t); fa2 = fa + [b2]; fb2 = fb + [a1]
            Q2 = rest + [newq]
            # reject: duplicate triple
            if len(set(Q2)) != len(Q2): continue
            save(os.path.join(od, "w%06d.state" % cnt), FA + 1, FB + 1, Q2, fa2, fb2)
            cnt += 1
print("wrote", cnt)
