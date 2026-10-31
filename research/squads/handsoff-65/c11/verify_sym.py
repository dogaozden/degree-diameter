#!/usr/bin/env python3
# usage: verify_sym.py SOLFILE GROUP SIGMA(4 ints, e.g. 3,2,1,0) : checks (v,h)->(sigma v, theta h) is an automorphism
# with theta = identity; prints OK or the first failing edge. Edge set built as in export_lift.py.
import sys
sol, grp, sig = sys.argv[1], sys.argv[2], list(map(int, sys.argv[3].split(',')))
tok = open(grp).read().split(); m = int(tok[0])
mul = [list(map(int, tok[1 + i*m:1 + (i+1)*m])) for i in range(m)]
L = [l for l in open(sol) if l.strip() and not l.startswith('#')]
b, E = map(int, L[0].split()); side = list(map(int, L[1].split()))
ed = [tuple(map(int, l.split()[:3])) for l in L[2:2+E]]
S = set()
for (a, c, g) in ed:
    for h in range(m):
        x, y = a*m+h, c*m+mul[h][g]; S.add((min(x,y), max(x,y)))
bad = 0
for (x, y) in S:
    u, h = divmod(x, m); v, k = divmod(y, m)
    p, q = sig[u]*m + h, sig[v]*m + k
    if (min(p,q), max(p,q)) not in S: bad += 1
print("edges", len(S), "not mapped", bad, "OK" if bad == 0 else "FAIL")
