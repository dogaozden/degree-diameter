"""q=4: the 273 pairwise non-collinear points (a set of points meeting every line exactly once) = the 271 ILS points
plus the two points on the uncovered lines {140..144} (point 30) and {123,471,561,634,720}. Independent check that
every line contains exactly one chosen point, then writes q4_points273.npy and the matching line colouring."""
import numpy as np
from common import *
H = load(4)
S = np.load('q4_pencil_mis_s1.npy').tolist()
def common(ls):
    c = set(H.lines[ls[0]].tolist())
    for l in ls[1:]:
        c &= set(H.lines[l].tolist())
    return sorted(c)
z1 = common([140, 141, 142, 143, 144]); z2 = common([123, 471, 561, 634, 720])
print('common point of 140..144:', z1, ' of 123,471,561,634,720:', z2)
P = S + [z1[0], z2[0]]
assert len(set(P)) == 273
cnt = np.zeros(H.L, int)
for p in P:
    cnt[H.PL[p]] += 1
print('lines with exactly one chosen point:', int((cnt == 1).sum()), 'of', H.L, '; max count', int(cnt.max()))
# pairwise non-collinear: no two chosen points on a common line (equivalently cnt==1 everywhere given 273*5 = 1365)
np.save('q4_points273.npy', np.array(P, dtype=np.int64))
col = np.full(H.L, -1, dtype=np.int32)
for i, p in enumerate(P):
    col[H.PL[p]] = i
col.tofile('q4_lines273_pencils.bin')
print('pencil colouring written, classes', len(P), 'coloured', int((col >= 0).sum()))
