#!/usr/bin/env python3
"""The q^2+1 points of an elliptic quadric section Q^-(3,q) of Q(6,q), q even, as point indices of a hexgen2 .bin: the
3-space spanned by e0, e4, e1 + e5, e5 + d e3 with d^2 = delta, Tr(delta) = 1, on which Q(a e0 + b e4 + s(e1+e5) +
t(e5 + d e3)) = ab + s^2 + st + delta t^2 is elliptic. Pairwise opposite in H(q) (D7_HEXAGON.md Lemma 1.2(a)); the
builder re-checks this with balls of radius 4.  usage: elliptic_even.py HEXBIN OUT"""
import sys, itertools
import numpy as np
sys.path.insert(0, __import__('os').path.dirname(__file__))
from typed_build import F, tr

hexfn, out = sys.argv[1:3]
b = open(hexfn, 'rb').read()
q, N, Lc = (int(t) for t in np.frombuffer(b[:12], dtype=np.int32))
X = np.frombuffer(b[12 + 4 * Lc * (q + 1):], dtype=np.uint8).reshape(N, 7).astype(np.int64)
Fq = F(q); assert Fq.p == 2
delta = next(x for x in range(1, q) if tr(Fq, x) == 1)
d = next(x for x in range(q) if Fq.M[x, x] == delta)
code = X @ (q ** np.arange(7, dtype=np.int64))
assert (np.diff(code) > 0).all()
pts = set()
for a, bb, s, t in itertools.product(range(q), repeat=4):
    v = [a, s, 0, int(Fq.M[t, d]), bb, int(Fq.A[s, t]), 0]                  # coordinates X0..X6
    if not any(v):
        continue
    Qv = Fq.add(Fq.mul(v[0], v[4]), Fq.mul(v[1], v[5]), Fq.mul(v[2], v[6]), Fq.mul(v[3], v[3]))
    if Qv:
        continue
    lead = next(x for x in v if x)
    v = [int(Fq.M[Fq.INV[lead], x]) for x in v]
    pts.add(int(np.searchsorted(code, sum(x * q ** i for i, x in enumerate(v)))))
pts = sorted(pts)
assert len(pts) == q * q + 1 and all(code[i] == sum(x * q ** k for k, x in enumerate(X[i])) for i in pts)
open(out, 'w').write(' '.join(map(str, pts)) + '\n')
print(f'q = {q}, delta = {delta}: {len(pts)} points of an elliptic quadric section -> {out}')
