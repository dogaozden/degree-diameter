#!/usr/bin/env python3
"""Multiplication table of Z_m x|_r Z_k in haar_fast's numbering (index a*k + j): metatab.py m k r OUT.bin
(a,j)(b,l) = (a + r^j b mod m, j + l mod k). Same .bin format as gapgroup.py (int32 N, N*N uint16, identity 0)."""
import sys, struct, array
m, k, r, out = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
assert pow(r, k, m) == 1 % m
N = m * k; rp = [pow(r, j, m) for j in range(k)]
T = array.array('H', [0]) * (N * N)
for a in range(m):
    for j in range(k):
        x = a * k + j; base = x * N
        for b in range(m):
            rb = (a + rp[j] * b) % m * k
            for l in range(k): T[base + b * k + l] = rb + (j + l) % k
with open(out, 'wb') as f: f.write(struct.pack('<i', N)); T.tofile(f)
