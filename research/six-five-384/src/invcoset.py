#!/usr/bin/env python3
"""invcoset.py: inverse-pair refinement of the quotient counting test on Q = G/G'G^2 = C2^r (job six-five-384).
The side-A words come in pairs (w, reversed inverse of w) with values x, x^-1 (no word is its own partner except e).
Every coset of N = G'G^2 is closed under inversion, so a pair covers at most one inverse class {x, x^-1} of its coset,
and a coset containing v_y involutions has (|N| + v_y)/2 inverse classes (the identity word covers e in N). Hence
H(G,S) of diameter <= 5 needs an image 6-tuple in C2^r with c(y) >= |N| + v_y for every coset y (side B gives the
same counts in an abelian quotient). Images may coincide; q_1 = 0 by translation; no automorphism reduction (v is not
Aut(Q)-invariant). Input: lines "id r v_0 .. v_{2^r-1}" from invcoset.g. Output: "id r PASS|FAIL best_margin".
usage: invcoset.py FILE..."""
import sys, itertools
from functools import lru_cache

@lru_cache(None)
def vectors(r):
    n = 1 << r
    out = []
    for t in itertools.combinations_with_replacement(range(n), 5):
        q = (0,) + t
        c = [0] * n
        c[0] += 1
        for a in range(6):
            for b in range(6):
                if a != b: c[q[a] ^ q[b]] += 1
        for a in range(6):
            for b in range(6):
                if a == b: continue
                ab = q[a] ^ q[b]
                for cc in range(6):
                    if cc == b: continue
                    for d in range(6):
                        if d != cc: c[ab ^ q[cc] ^ q[d]] += 1
        out.append(tuple(c))
    return sorted(set(out))

for path in sys.argv[1:]:
    for line in open(path):
        t = line.split()
        if len(t) < 3: continue
        gid, r = int(t[0]), int(t[1]); v = [int(x) for x in t[2:]]
        T = 384 >> r
        best = max(min(c[y] - T - v[y] for y in range(1 << r)) for c in vectors(r))
        print(gid, r, "PASS" if best >= 0 else "FAIL", best)
