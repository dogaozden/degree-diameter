"""3-regular controllers: exhaustive Haar (|S| = 3, S = {e, x, y}) over small groups, and annealed general graphs.
Exact-NB-4: every same-side ordered pair joined by a nonbacktracking walk of length exactly 4 (24 walks per vertex)."""
import sys, itertools, subprocess
import numpy as np
import controller as ct
W3 = [w for w in itertools.product(range(3), repeat=4) if w[0] != w[1] and w[1] != w[2] and w[2] != w[3]]
assert len(W3) == 24

def best_haar3(T):
    G = ct.Group(T); m = G.m; inv = G.inv
    best = (10 ** 9, None)
    for x in range(m):
        for y in range(x + 1, m):
            if G.e in (x, y): continue
            S = [G.e, x, y]; Si = [int(inv[s]) for s in S]
            cA = set(); cB = set()
            for (i1, i2, i3, i4) in W3:
                cA.add(int(T[Si[i4], T[S[i3], T[Si[i2], S[i1]]]]))
                cB.add(int(T[S[i4], T[Si[i3], T[S[i2], Si[i1]]]]))
            c = 2 * m - len(cA) - len(cB)
            if c < best[0]:
                best = (c, S)
    return best

from math import gcd
for m in range(8, 25):
    res = []
    for a in range(1, m + 1):
        if m % a: continue
        b = m // a
        for r in range(1, max(a, 2)):
            if a > 1 and (gcd(r, a) != 1 or pow(r, b, a) != 1 % a): continue
            T = ct.meta(a, b, r)
            c, S = best_haar3(T)
            res.append((c, f'meta {a} {b} {r}', S))
    res.sort()
    print(m, res[0], flush=True)
