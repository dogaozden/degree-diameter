#!/usr/bin/env python3
"""mk_asl.py OUT p s : cay_mg group file for Q = {g in GL(2,p): det g in mu_s} (SL(2,p).mu_s), identity first.
G = F_p^2 x| Q has order p^3 (p^2-1) s."""
import sys, struct, numpy as np
out, p, s = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
assert (p - 1) % s == 0
g = next(x for x in range(2, p) if all(pow(x, (p - 1) // q, p) != 1 for q in range(2, p) if (p - 1) % q == 0 and all(q % r for r in range(2, q))))
dets = np.zeros(p, bool); h = pow(g, (p - 1) // s, p); x = 1
for _ in range(s): dets[x] = True; x = x * h % p
a, b = np.meshgrid(np.arange(p), np.arange(p), indexing='ij'); a = a.ravel(); b = b.ravel()
rows = []
for c in range(p):
    for d in range(p):
        det = (a * d - b * c) % p
        m = dets[det]
        if m.any(): rows.append(np.stack([a[m], b[m], np.full(m.sum(), c), np.full(m.sum(), d)], 1))
M = np.concatenate(rows).astype(np.int32)
I = np.array([1, 0, 0, 1], np.int32)
k = np.where((M == I).all(1))[0][0]; M[[0, k]] = M[[k, 0]]
assert len(M) == p * (p * p - 1) * s, (len(M), p * (p * p - 1) * s)
with open(out, 'wb') as f: f.write(struct.pack('ii', p, len(M))); f.write(M.tobytes())
print(out, 'L', len(M), 'N', len(M) * p * p)
