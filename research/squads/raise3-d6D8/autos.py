#!/usr/bin/env python3
"""Write the permutation alpha(h) = x h x^-1 (an inner automorphism of H) for an element x of order k.
usage: autos.py GROUP.bin k seed outfile   (writes H integers, one per line; index 0 = identity)
"""
import sys, random
import numpy as np
sys.path.insert(0, '.')
from verify import load_group

h, MH, INV = load_group(sys.argv[1])
k, seed, out = int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
def order(x):
    o, y = 1, x
    while y != 0:
        y = MH[y, x]; o += 1
    return o
cands = [x for x in range(1, h) if order(x) == k]
rnd = random.Random(seed)
x = rnd.choice(cands)
alpha = MH[MH[x, :], INV[x]]          # alpha[h] = (x h) x^-1
assert len(set(alpha.tolist())) == h
with open(out, 'w') as fh:
    fh.write('\n'.join(str(int(v)) for v in alpha) + '\n')
print(f"x={x} order={k} written {out}")
