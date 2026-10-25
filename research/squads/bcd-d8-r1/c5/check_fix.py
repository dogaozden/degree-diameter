"""Obstruction check: fixed points / fixed lines of every element of A = <tau, F> on H(5)."""
import sys; sys.path.insert(0, '/home/user/degree-diameter/research/squads/bcd-d8-r1/c5')
import numpy as np, group as G
from collections import Counter
N = G.N
res = Counter()
for e, (i, j) in enumerate(G.ELEM):
    if e == 0: continue
    fp = int((G.EP[e] == np.arange(N)).sum()); fl = int((G.EL[e] == np.arange(N)).sum())
    res[(j, fp, fl)] += 1
print("(F-exponent j, fixed points, fixed lines) -> number of elements:")
for k, v in sorted(res.items()): print(k, v)
print("points in orbits of size 31:", sum(1 for o in range(len(G.preps)) if len(set(G.EP[:, G.preps[o]])) == 31) * 31)
print("line orbits: sizes", Counter(len(set(G.EL[:, l])) for l in G.lreps))
