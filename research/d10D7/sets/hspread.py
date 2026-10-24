"""Hermitian-type spread of H(q), q = p^e: the lines of H(q) contained in a hyperplane f(x) = 0 of PG(6,q) whose
section of Q(6,q) is elliptic contain q^3+1 pairwise opposite lines. Tries random hyperplanes, keeps a set of lines
lying in the hyperplane if it is pairwise opposite (checked by the caller with setcheck).
   python3 hspread.py HEXBIN q p e seed out"""
import sys, struct, random
import numpy as np
fn, q, p, e, seed, out = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]), sys.argv[6]
raw = open(fn, 'rb').read(); qq, N, L = struct.unpack('3i', raw[:12])
LP = np.frombuffer(raw[12:12 + 4 * L * (q + 1)], dtype=np.int32).reshape(L, q + 1)
coord = np.frombuffer(raw[12 + 4 * L * (q + 1):], dtype=np.uint8).reshape(N, 7).astype(np.int64)
# GF(p^e) arithmetic with the same irreducible polynomials as hexgen2.c
polys = {4: [1, 1], 8: [1, 1, 0], 9: [1, 0], 16: [1, 1, 0, 0], 25: [2, 0], 27: [1, 2, 0], 32: [1, 0, 1, 0, 0]}
def tovec(a): return [(a // p ** i) % p for i in range(e)]
def toint(v): return sum(c * p ** i for i, c in enumerate(v))
def mul(a, b):
    if e == 1: return (a * b) % p
    va, vb = tovec(a), tovec(b); prod = [0] * (2 * e - 1)
    for i in range(e):
        for j in range(e): prod[i + j] = (prod[i + j] + va[i] * vb[j]) % p
    c = polys[q]
    for k in range(2 * e - 2, e - 1, -1):   # x^e = -(c0 + c1 x + ...)
        t = prod[k]; prod[k] = 0
        for i in range(e): prod[k - e + i] = (prod[k - e + i] - t * c[i]) % p
    return toint(prod[:e])
def add(a, b): return toint([(x + y) % p for x, y in zip(tovec(a), tovec(b))]) if e > 1 else (a + b) % p
MUL = np.array([[mul(a, b) for b in range(q)] for a in range(q)]); ADD = np.array([[add(a, b) for b in range(q)] for a in range(q)])
rng = random.Random(seed); best = []
for tr in range(200):
    f = [rng.randrange(q) for _ in range(7)]
    if not any(f): continue
    val = np.zeros(N, dtype=np.int64)
    for i in range(7): val = ADD[val, MUL[f[i], coord[:, i]]]
    inpl = (val == 0)
    lines = [l for l in range(L) if inpl[LP[l]].all()]
    if len(lines) == q ** 3 + 1:
        best = lines; break
    if tr < 5 or len(lines) > len(best): print('try', tr, 'lines in hyperplane', len(lines))
open(out, 'w').write(' '.join(map(str, best)) + '\n')
print('kept', len(best), 'lines')
