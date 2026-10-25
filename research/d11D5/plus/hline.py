"""For hyperbolic PG(3,8)-lines h, L_j = delta(R) (R in h): count PG-line transversals of the 9 lines L_j.
Writes candidates (h, transversals) to hcand.json."""
import json, sys, itertools
sys.path.insert(0, "/home/user/degree-diameter/research/d11D5")
from w8 import field
from dcover import load
import os; os.chdir("/home/user/degree-diameter/research/d11D5")
W = json.load(open("w8.json")); pts = [tuple(v) for v in W["points"]]; idx = {v: i for i, v in enumerate(pts)}
n, L, d_pt, d_ln, inv = load(8)
mul, finv = field(8)
def norm(v):
    for c in v:
        if c: s = finv[c]; return tuple(mul[s][x] for x in v)
def span(i, j):
    x, y = pts[i], pts[j]; s = {i, j}
    for a in range(8):
        v = tuple(x[k] ^ mul[a][y[k]] for k in range(4)); s.add(idx[norm(v)])
    return frozenset(s)
def B(x, y): return mul[x[0]][y[1]] ^ mul[x[1]][y[0]] ^ mul[x[2]][y[3]] ^ mul[x[3]][y[2]]
pglines = set()
for i in range(n):
    for j in range(i + 1, n):
        pglines.add(span(i, j))
pglines = list(pglines); print("PG lines", len(pglines))
lineset = [frozenset(s) for s in L]
out = []
for h in pglines:
    a, b = sorted(h)[:2]
    if B(pts[a], pts[b]) == 0: continue   # totally isotropic: skip
    Ls = [lineset[d_pt[R]] for R in h]
    if any(Ls[i] & Ls[j] for i in range(9) for j in range(i + 1, 9)): continue
    L1, L2 = Ls[0], Ls[1]
    trans = []
    for u in L1:
        for w in L2:
            t = span(u, w)
            if all(t & Lj for Lj in Ls): trans.append(sorted(t))
    trans = [list(x) for x in set(tuple(t) for t in trans)]
    if trans: out.append({"h": sorted(h), "L": [d_pt[R] for R in sorted(h)], "trans": trans})
print("hyperbolic h with disjoint images:", "candidates with transversals:", len(out))
if out: print("example: transversals", len(out[0]["trans"]))
json.dump(out, open("plus/hcand.json", "w"))
