"""Find linear automorphisms of H(q) in hexgen coordinates: test diagonal torus maps and coordinate permutations."""
import sys, itertools, numpy as np
from hexlib import load_hex
q = int(sys.argv[1]) if len(sys.argv) > 1 else 9
n, lines = load_hex(q)
raw = np.fromfile(f'../hex/hex_q{q}.bin', dtype=np.uint8)
off = 12 + 4 * n * (q + 1)
coords = raw[off:off + 7 * n].reshape(n, 7).astype(int)
# field arithmetic (same as hexgen): q = p or p^2
p = 2
while q % p: p += 1
e = 1 if q == p else 2
if e == 2:
    nr = next(t for t in range(2, p) if all((u * u) % p != t for u in range(1, p)))
def mul(x, y):
    if e == 1: return (x * y) % p
    a, b, c, d = x % p, x // p, y % p, y // p
    return ((a * c + b * d * nr) % p) + p * ((a * d + b * c) % p)
INV = {x: next(y for y in range(1, q) if mul(x, y) == 1) for x in range(1, q)}
key = {tuple(c): i for i, c in enumerate(coords)}
def normalize(v):
    for x in v:
        if x: s = INV[x]; return tuple(mul(s, y) for y in v)
lineset = set(tuple(sorted(int(x) for x in L)) for L in lines)
def apply(f):
    """f maps a coordinate vector to a coordinate vector; returns point permutation or None"""
    perm = np.empty(n, int)
    for i in range(n):
        w = normalize(f(coords[i]))
        j = key.get(w)
        if j is None: return None
        perm[i] = j
    return perm
def is_auto(perm):
    for L in lines[:2000]:
        if tuple(sorted(perm[L])) not in lineset: return False
    return all(tuple(sorted(perm[L])) in lineset for L in lines)
# torus: diag(t1,t2,t3,1,1/t1,1/t2,1/t3) with t1 t2 t3 = 1
units = list(range(1, q))
found = 0
for t1 in units[:4]:
    for t2 in units[:4]:
        t3 = INV[mul(t1, t2)]
        d = [t1, t2, t3, 1, INV[t1], INV[t2], INV[t3]]
        perm = apply(lambda v: [mul(d[k], v[k]) for k in range(7)])
        ok = perm is not None and is_auto(perm)
        print('torus', (t1, t2, t3), 'auto' if ok else 'no'); found += ok
# cyclic coordinate permutation (0 1 2)(4 5 6)
perm = apply(lambda v: [v[1], v[2], v[0], v[3], v[5], v[6], v[4]])
print('perm (012)(456):', 'auto' if perm is not None and is_auto(perm) else 'no')
perm = apply(lambda v: [v[2], v[0], v[1], v[3], v[6], v[4], v[5]])
print('perm (021)(465):', 'auto' if perm is not None and is_auto(perm) else 'no')
# elementary SL(3) element on (x0,x1,x2) with dual action on (x4,x5,x6): A = I + c*E_{01}, A^{-T} = I - c*E_{54}?
# For v -> A v on W=(x0,x1,x2): x0' = x0 + c x1. Dual on W*=(x4,x5,x6) must preserve x0x4+x1x5+x2x6: x5' = x5 - c x4.
def neg(x):
    if e == 1: return (-x) % p
    return ((-(x % p)) % p) + p * ((-(x // p)) % p)
def add(x, y):
    if e == 1: return (x + y) % p
    return ((x % p + y % p) % p) + p * ((x // p + y // p) % p)
for c in [1, 2]:
    f = lambda v, c=c: [add(v[0], mul(c, v[1])), v[1], v[2], v[3], v[4], add(v[5], neg(mul(c, v[4]))), v[6]]
    perm = apply(f)
    print('elementary c=%d:' % c, 'auto' if perm is not None and is_auto(perm) else 'no')
