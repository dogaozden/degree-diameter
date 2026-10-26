# Exhaustive voltage generator for a 3+3 cubic base over meta:m:k:r (flift left-mult convention).
# Tree edges (BFS from vertex 0, as flift does) get voltage 0. The first free (cotree) edge ranges over
# conjugacy-class representatives; the other free edges range over all of G. Simultaneous conjugation
# preserves the cost, so this covers every assignment up to conjugacy.
# usage: gen.py BASE m k r [SLICE i/n]  -> lines of m volts on stdout
import sys
import numpy as np

base_path, m_, k_, r_ = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
sl = sys.argv[5] if len(sys.argv) > 5 else "0/1"
si, sn = map(int, sl.split("/"))
N = m_ * k_
rp = [pow(r_, j, m_) for j in range(k_)]
# element index a + m*j ; (a,j)(b,l) = (a + r^j b, j+l)
M = np.zeros((N, N), dtype=np.int64)
for j in range(k_):
    for a in range(m_):
        for l in range(k_):
            for b in range(m_):
                M[a + m_ * j, b + m_ * l] = (a + rp[j] * b) % m_ + m_ * ((j + l) % k_)
assert M[0].tolist() == list(range(N)), "identity must be 0"
INV = np.array([int(np.where(M[g] == 0)[0][0]) for g in range(N)])
# conjugacy classes
cls = -np.ones(N, dtype=np.int64); reps = []
for g in range(N):
    if cls[g] >= 0: continue
    reps.append(g)
    conj = {int(M[M[h, g], INV[h]]) for h in range(N)}
    for x in conj: cls[x] = len(reps) - 1

# base
lines = open(base_path).read().split("\n")
b, m = map(int, lines[0].split())
E = [tuple(map(int, lines[1 + i].split()[:2])) for i in range(m)]
# BFS tree as flift: darts in edge order
dart = {u: [] for u in range(b)}
for i, (u, v) in enumerate(E):
    dart[u].append((v, i)); dart[v].append((u, i))
seen = {0}; q = [0]; intree = set()
h = 0
while h < len(q):
    u = q[h]; h += 1
    for v, e in dart[u]:
        if v not in seen:
            seen.add(v); intree.add(e); q.append(v)
free = [i for i in range(m) if i not in intree]
assert len(free) == m - (b - 1)
f0 = free[0]
sys.stderr.write(f"N={N} classes={len(reps)} free={free} tree={sorted(intree)}\n")
out = sys.stdout
from itertools import product
ks = list(range(N))
total = 0
for ci, c in enumerate(reps):
    if ci % sn != si: continue
    # centraliser of c, and its orbits on G under conjugation (reduces the second voltage further)
    C = [h for h in range(N) if M[h, c] == M[c, h]]
    orb_seen = set(); orbs = []
    for g in range(N):
        if g in orb_seen: continue
        orbs.append(g)
        for h in C: orb_seen.add(int(M[M[h, g], INV[h]]))
    base_line = [0] * m
    base_line[f0] = c
    for g2 in orbs:
        for g3, g4 in product(ks, repeat=len(free) - 2):
            vals = base_line[:]
            vals[free[1]] = g2
            vals[free[2]] = g3
            vals[free[3]] = g4
            out.write(" ".join(map(str, vals)) + "\n")
        total += 1
sys.stderr.write(f"slice {si}/{sn}: rows of g2 orbits {total}\n")
