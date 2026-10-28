"""Build 273 disjoint 4-dominating line classes at q=4 (the bound N/(q+1)): the 271 pencils of the pencil set, plus
two classes made of the 10 lines it leaves uncovered: {140..144} and {123,471,561,634,720} (the first is checked to be
a pencil, the second is not). Writes the colouring (int32 per line, -1 never occurs) and prints the structure."""
import numpy as np
from common import *
H = load(4)
S = np.load('q4_pencil_mis_s1.npy').tolist()
col = np.full(H.L, -1, dtype=np.int32)
for i, p in enumerate(S):
    for l in H.PL[p]:
        assert col[l] < 0, 'pencils overlap'
        col[l] = i
extra1 = [140, 141, 142, 143, 144]
extra2 = [123, 471, 561, 634, 720]
pts_common = set(H.lines[extra1[0]].tolist())
for l in extra1[1:]:
    pts_common &= set(H.lines[l].tolist())
print('lines 140..144 share a point:', sorted(pts_common))
for l in extra1 + extra2:
    assert col[l] < 0
for l in extra1:
    col[l] = len(S)
for l in extra2:
    col[l] = len(S) + 1
col.tofile('q4_lines273.bin')
print('classes', len(S) + 2, 'lines coloured', int((col >= 0).sum()), 'of', H.L)
print('class sizes', np.bincount(col, minlength=len(S) + 2).min(), np.bincount(col, minlength=len(S) + 2).max())
B = ball_matrix_cached(H, 4)
print('extra2 pairwise distances <=4 all?', bool(B[np.ix_(extra2, extra2)].all()), 'extra2 is pencil?',
      len(set.intersection(*[set(H.lines[l].tolist()) for l in extra2])) > 0)
