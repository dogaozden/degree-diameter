"""q=4: verify and write the 273-class line partition (frozen point set q4_points273.npy, produced by ILS + 2 points,
see build273.py / final_points.py history). Checks: 273 distinct points, every line contains exactly one of them,
then writes q4_lines273_pencils.bin (int32 per line: its pencil index). Usage: verify273.py"""
import numpy as np
from common import *
H = load(4)
P = np.load('q4_points273.npy').tolist()
assert len(set(P)) == 273
cnt = np.zeros(H.L, int)
for p in P:
    cnt[H.PL[p]] += 1
assert (cnt == 1).all(), 'some line has 0 or >1 chosen points'
col = np.full(H.L, -1, dtype=np.int32)
for i, p in enumerate(P):
    col[H.PL[p]] = i
col.tofile('q4_lines273_pencils.bin')
print('ok: 273 pairwise non-collinear points, each line exactly one; colouring written')
