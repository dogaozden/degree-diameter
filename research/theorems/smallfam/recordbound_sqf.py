"""Fibre bound for a squarefree modulus m: the ring is Z[x]/(prod of the distinct Phi_{o_i}), o_i = ord of r mod the
i-th prime of m; x has period L = lcm(o_i).  Reuses cyclobound.ball_bound with the companion matrix of that product.
Usage: python3 recordbound_sqf.py DELTA D m k r j1 j2 ... [--N N]"""
import sys
from math import gcd
import numpy as np
import cyclobound
cyclobound.FIBER = True
a = sys.argv[1:]
N = None
if '--N' in a:
    i = a.index('--N'); N = int(a[i + 1]); a = a[:i] + a[i + 2:]
Delta, D, m, k, r = map(int, a[:5])
j = tuple([0] + list(map(int, a[5:])))
primes = [q for q in range(2, m + 1) if m % q == 0 and all(q % d for d in range(2, int(q ** 0.5) + 1))]
assert all(m % (q * q) for q in primes), 'm must be squarefree'
ords = sorted({next(e for e in range(1, q) if pow(r, e, q) == 1) for q in primes})
poly = [1]
for o in ords:
    c = cyclobound.cyclotomic(o)
    out = [0] * (len(poly) + len(c) - 1)
    for i1, x in enumerate(poly):
        for i2, y in enumerate(c):
            out[i1 + i2] += x * y
    poly = out
L = 1
for o in ords:
    L = L * o // gcd(L, o)
f = len(poly) - 1
C = np.zeros((f, f), dtype=np.int64)
for i in range(f - 1):
    C[i + 1, i] = 1
for i in range(f):
    C[i, f - 1] = -poly[i]
Ms = [np.eye(f, dtype=np.int64)]
for t in range(1, L):
    Ms.append(C @ Ms[-1])
assert (C @ Ms[-1] == np.eye(f, dtype=np.int64)).all(), 'x^L != 1 in the ring'
cyclobound.zeta_powers = lambda o: (Ms, f)
B = cyclobound.ball_bound(Delta, D, k, L, j)
print(f'Delta={Delta} D={D} Z{m} x|_{r} Z{k}: orders of r mod primes {dict(zip(primes, [next(e for e in range(1, q) if pow(r, e, q) == 1) for q in primes]))}, '
      f'ring Z[x]/(prod Phi_o, o in {ords}) of rank {f}, period {L}; j={j}: B_j = {B}' + (f'; N = {N}, N/B_j = {N / B:.3f}' if N else ''))
