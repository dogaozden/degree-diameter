#!/usr/bin/env python3
"""mkbin.py m k r OUT.bin [c]: multiplication table of (Z_m x|_r Z_k) x Z_c for exh3.c (int32 N, then N*N uint16,
row g = left factor), index ((a*k + j)*c + z), identity 0. Same element order as gtab.py."""
import sys
import numpy as np
m, k, r = map(int, sys.argv[1:4]); out = sys.argv[4]; c = int(sys.argv[5]) if len(sys.argv) > 5 else 1
N = m * k * c; assert N < 65536
idx = np.arange(N); a = idx // c // k; j = (idx // c) % k; z = idx % c
rp = np.array([pow(r, t, m) for t in range(k)], dtype=np.int64)
A = (a[:, None] + rp[j][:, None] * a[None, :]) % m
J = (j[:, None] + j[None, :]) % k
Z = (z[:, None] + z[None, :]) % c
T = ((A * k + J) * c + Z).astype(np.uint16)
with open(out, 'wb') as f:
    f.write(np.array([N], dtype=np.int32).tobytes()); f.write(T.tobytes())
