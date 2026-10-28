#!/usr/bin/env python3
"""Random S in SL(2,q) WITHOUT symmetry (no alpha-closure, no fixed letters).
Usage: gen_random_nosym.py q Delta seed
Draws Delta distinct elements of SL(2,q) uniformly at random (rejection sampling), seeded by (q, Delta, seed).
Identity is NOT included (I is excluded). Distinctness is checked in PSL (X and -X count as the same element),
so the output has Delta distinct PSL classes. Prints lines "a b c d 0" (m = 1)."""
import sys, random
q, Delta, seed = map(int, sys.argv[1:4])
R = random.Random(seed * 1000003 + q * 101 + Delta)
def rand_sl():
    while True:
        a, b, c = R.randrange(q), R.randrange(q), R.randrange(q)
        if a:
            return (a, b, c, (1 + b * c) * pow(a, q - 2, q) % q)
def key(X):  # PSL key: canonical representative of {X, -X}
    a, b, c, d = X
    lead = a if a else b
    return X if lead <= (q - 1) // 2 else tuple((-t) % q for t in X)
I_KEY = key((1, 0, 0, 1))
S, seen = [], {I_KEY}
while len(S) < Delta:
    X = rand_sl(); k = key(X)
    if k in seen: continue
    seen.add(k); S.append(X)
for X in S: print(*X, 0)
