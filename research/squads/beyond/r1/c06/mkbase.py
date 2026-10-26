#!/usr/bin/env python3
# W(q) incidence graph (symplectic GQ, q prime) as a base multigraph with 3 extra matchings.
# usage: mkbase.py q seed OUT   -> OUT: "NP NL", then lines "p l" for flags, "p l 1" style handled by caller
import sys, random, itertools
q = int(sys.argv[1]); seed = int(sys.argv[2]); out = sys.argv[3]
assert all(q % d for d in range(2, int(q**0.5) + 1))
def normalize(v):
    for x in v:
        if x % q:
            inv = pow(x, q - 2, q)
            return tuple((inv * y) % q for y in v)
    return None
pts = sorted({normalize(v) for v in itertools.product(range(q), repeat=4) if any(v)})
N = len(pts); assert N == (q+1)*(q*q+1), N
idx = {p: i for i, p in enumerate(pts)}
def B(x, y): return (x[0]*y[1] - x[1]*y[0] + x[2]*y[3] - x[3]*y[2]) % q
lines = set()
for i, x in enumerate(pts):
    perp = [j for j, y in enumerate(pts) if B(x, y) == 0 and j != i]
    for j in perp:
        y = pts[j]
        # full line spanned by x,y: all normalized combinations a*x+b*y
        L = set()
        for a in range(q):
            for b in range(q):
                if a or b:
                    L.add(idx[normalize(tuple((a*x[k]+b*y[k]) % q for k in range(4)))])
        lines.add(tuple(sorted(L)))
lines = sorted(lines)
assert len(lines) == N and all(len(L) == q+1 for L in lines), (len(lines))
rnd = random.Random(seed)
inc = set()
flags = []
for li, L in enumerate(lines):
    for p in L:
        flags.append((p, li))
inc = set(flags)
# three extra perfect matchings points->lines, disjoint from incidences and from each other
def random_matching(forbid):
    while True:
        perm = list(range(N)); rnd.shuffle(perm)
        if all((p, perm[p]) not in forbid for p in range(N)):
            return perm
mats = []
used = set(inc)
for k in range(3):
    m = random_matching(used)
    mats.append(m)
    for p in range(N): used.add((p, m[p]))
with open(out, 'w') as f:
    f.write(f"{N} {N} {len(flags)}\n")
    for p, l in flags: f.write(f"{p} {l}\n")
    for m in mats: f.write("M " + " ".join(map(str, m)) + "\n")
print("points", N, "lines", len(lines), "flags", len(flags))
