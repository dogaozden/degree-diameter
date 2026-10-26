#!/usr/bin/env python3
"""Multiplication table of (Z_m x|_r Z_k) x Z_n in haar_fast's numbering (index (a*k + j)*n + z):
metatab.py m k r OUT.bin [n]   (a,j,z)(b,l,y) = (a + r^j b mod m, j + l mod k, z + y mod n).
Same .bin format as gapgroup.py (int32 N, N*N uint16, identity 0)."""
import sys, struct, array
m, k, r, out = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
n = int(sys.argv[5]) if len(sys.argv) > 5 else 1
assert pow(r, k, m) == 1 % m
N = m * k * n; rp = [pow(r, j, m) for j in range(k)]
T = array.array('H', [0]) * (N * N)
for a in range(m):
    for j in range(k):
        for z in range(n):
            x = (a * k + j) * n + z; base = x * N
            for b in range(m):
                rb = (a + rp[j] * b) % m * k
                for l in range(k):
                    for y in range(n): T[base + ((b * k + l) * n + y)] = (rb + (j + l) % k) * n + (z + y) % n
with open(out, 'wb') as f: f.write(struct.pack('<i', N)); T.tofile(f)
