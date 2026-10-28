"""c13 part 2: K pairwise disjoint lines + K pairwise non-collinear points in H(2), colour files for the D = 11 lift.
Usage: python3 h2_build.py K  -> writes pc2_K.bin (point colours), lc2_K.bin (line colours), prints the sets."""
import sys
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/polylev')
from hexlib import Hex

HEX = '/home/user/degree-diameter/research/theorems/polylev/hex/hex_q2.bin'
H = Hex(HEX)
N, q = H.N, H.q
assert N == 63 and q == 2
LP = [list(map(int, H.lines[l])) for l in range(N)]          # points on each line
PL = [list(map(int, H.PL[p])) for p in range(N)]              # lines through each point


def mis(n, nbr, cliques, seconds_nodes=10**7):
    """exact maximum independent set (bitmask branch and bound); cliques bound: each clique holds at most one vertex."""
    best = [0, 0]
    nodes = [0]
    cl = [c for c in cliques]

    def bound(cand):
        return sum(1 for c in cl if c & cand)

    def rec(cand, cur, size):
        nodes[0] += 1
        if nodes[0] > seconds_nodes:
            raise RuntimeError('node limit')
        if cand == 0:
            if size > best[0]:
                best[0], best[1] = size, cur
            return
        if size + bound(cand) <= best[0]:
            return
        v = (cand & -cand).bit_length() - 1
        rec(cand & ~nbr[v] & ~(1 << v), cur | (1 << v), size + 1)
        rec(cand & ~(1 << v), cur, size)

    rec((1 << n) - 1, 0, 0)
    return best[0], [i for i in range(n) if best[1] >> i & 1], nodes[0]


# lines: adjacent when they share a point; cliques = pencils
nbr_l = [0] * N
for a in range(N):
    for b in range(N):
        if a != b and set(LP[a]) & set(LP[b]):
            nbr_l[a] |= 1 << b
cliq_l = [sum(1 << l for l in PL[p]) for p in range(N)]
# points: adjacent when collinear; cliques = lines
nbr_p = [0] * N
for a in range(N):
    for b in range(N):
        if a != b and set(PL[a]) & set(PL[b]):
            nbr_p[a] |= 1 << b
cliq_p = [sum(1 << p for p in LP[l]) for l in range(N)]

if __name__ == '__main__':
    K = int(sys.argv[1])
    ml, sl, nl = mis(N, nbr_l, cliq_l)
    mp, sp, np_ = mis(N, nbr_p, cliq_p)
    print(f'max pairwise disjoint lines (partial spread) = {ml} (nodes {nl}); '
          f'max pairwise non-collinear points = {mp} (nodes {np_})')
    assert K <= ml and K <= mp, 'K too large for exact maximum'
    lines_sel = sl[:K]
    pts_sel = sp[:K]
    # verify
    assert all(not (set(LP[a]) & set(LP[b])) for a in lines_sel for b in lines_sel if a < b)
    assert all(not (set(PL[a]) & set(PL[b])) for a in pts_sel for b in pts_sel if a < b)
    cp = -np.ones(N, dtype=np.int32)
    cl = -np.ones(N, dtype=np.int32)
    for i, l in enumerate(lines_sel):
        for p in LP[l]:
            cp[p] = i
    for i, p in enumerate(pts_sel):
        for l in PL[p]:
            cl[l] = i
    cp.tofile(f'pc2_{K}.bin')
    cl.tofile(f'lc2_{K}.bin')
    print('K =', K, 'line set', lines_sel, 'point set', pts_sel)
    print('point colour counts', np.bincount(cp[cp >= 0]).tolist(), 'line colour counts', np.bincount(cl[cl >= 0]).tolist())
