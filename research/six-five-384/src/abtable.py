#!/usr/bin/env python3
"""abtable.py: multiplication table of the abelian group C_m1 x ... x C_mk in qfeas/haarex format (identity = 0),
with k = 0 automorphisms (qfeas then enumerates every q_2). usage: abtable.py 2,2,2,2 > c2_4.txt"""
import sys, itertools
ms = [int(x) for x in sys.argv[1].split(",")]
els = list(itertools.product(*[range(m) for m in ms]))
idx = {e: i for i, e in enumerate(els)}
print(len(els))
for a in els:
    print(" ".join(str(idx[tuple((x + y) % m for x, y, m in zip(a, b, ms))]) for b in els))
print(0)
