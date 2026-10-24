#!/usr/bin/env python3
"""Offsets C (|C| = d) in Z_m with 3(C - C) = Z_m, so that the circulant hub graph v_j ~ u_{j+c} puts every two v's
(and every two u's) within distance 6.  usage: huboffsets.py m d [seed]"""
import sys, random
m, d = int(sys.argv[1]), int(sys.argv[2]); rng = random.Random(int(sys.argv[3]) if len(sys.argv) > 3 else 1)
for trial in range(2000):
    C = rng.sample(range(m), d)
    D = {(a - b) % m for a in C for b in C}
    D2 = {(x + y) % m for x in D for y in D}
    D3 = {(x + y) % m for x in D2 for y in D}
    if len(D3) == m:
        print(' '.join(map(str, C))); sys.stderr.write(f'trial {trial}: |C-C| = {len(D)}, |2(C-C)| = {len(D2)}, 3(C-C) = Z_{m}\n'); break
else:
    sys.exit('no offsets found')
