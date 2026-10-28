"""Independent check of the two sets against the incidence structure of H(7) (not the edge files).
Reads set files (one id per line), checks pairwise disjointness of lines / non-collinearity of points."""
import sys
import itertools
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/polylev')
from hexlib import Hex

H = Hex('/home/user/degree-diameter/research/theorems/polylev/hex/hex_q7.bin')
C = '/home/user/degree-diameter/research/squads/polylev/r1/c11/'


def load(path):
    with open(path) as f:
        return [int(x) for x in f.read().split()]


lines = load(C + 'set_lines.txt')
pts = load(C + 'set_points.txt')
assert len(set(lines)) == len(lines) and all(0 <= l < H.L for l in lines)
assert len(set(pts)) == len(pts) and all(0 <= p < H.N for p in pts)

# (a) pairwise disjoint lines: no common point
lp = {l: set(H.lines[l].tolist()) for l in lines}
bad_a = sum(1 for a, b in itertools.combinations(lines, 2) if lp[a] & lp[b])
# (b) pairwise non-collinear points: no common line
pl = {p: set(H.PL[p].tolist()) for p in pts}
bad_b = sum(1 for a, b in itertools.combinations(pts, 2) if pl[a] & pl[b])
print('lines', len(lines), 'pairs meeting', bad_a)
print('points', len(pts), 'pairs collinear', bad_b)
print('K = min =', min(len(lines), len(pts)) if bad_a == 0 and bad_b == 0 else 'INVALID')
