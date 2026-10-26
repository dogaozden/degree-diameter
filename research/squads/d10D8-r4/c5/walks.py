"""c5: walk counts in the base graph B = H(q) + matchings, by base distance (numpy, exact int64)."""
import sys
import numpy as np
sys.path.insert(0, "/home/user/degree-diameter/research/squads/d10D8-r4/c5")
from rule import *
from geo import *
q = int(sys.argv[1]) if len(sys.argv) > 1 else 3
G = geometry(q); N = G["N"]; Q1 = G["Q1"]; pl = G["pl"]
s1, s2 = geo_sigmas(G)
V = 2 * N
A = np.zeros((V, V), dtype=np.int64)
for l in range(N):
    for k in range(Q1):
        p = pl[l * Q1 + k]; A[p, N + l] += 1; A[N + l, p] += 1
for s in (s1, s2):
    for p in range(N):
        A[p, N + s[p]] += 1; A[N + s[p], p] += 1
# base distances
D = np.full((V, V), -1); 
R = np.eye(V, dtype=np.int64); seen = np.eye(V, dtype=bool)
for d in range(0, 12):
    newly = (R > 0) & (~seen)
    D[newly] = d; seen |= newly
    R = (R @ A > 0).astype(np.int64)
    if seen.all(): break
print("base diameter", D.max(), "degree", A.sum(axis=1)[0], "multi-edges", int((A > 1).sum()))
P = np.eye(V, dtype=np.int64)
walks = {}
for k in range(1, 9):
    P = P @ A
    walks[k] = P
for dist in range(1, 7):
    for typ, sel in (("pt-ln", "odd"), ("pt-pt", "even")):
        rows = np.arange(N)  # sources: points
        cols = np.arange(N, V) if typ == "pt-ln" else np.arange(N)
        mask = (D[np.ix_(rows, cols)] == dist)
        if not mask.any(): continue
        out = []
        for k in range(dist, 9):
            if (k - dist) % 2: continue
            M = walks[k][np.ix_(rows, cols)]
            out.append((k, int(M[mask].min()), int(M[mask].mean() * 10) / 10))
        print(typ, "dist", dist, "pairs", int(mask.sum()), "(length, min, mean) walks:", out)
