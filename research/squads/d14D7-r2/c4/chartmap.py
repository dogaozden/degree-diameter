# chartmap.py (card c4): map chart points (a,b,c,d,e) of GF(11)^5 to hexagon point indices of gh_11.txt.
# Point of H(11) with x0=1: vector (1,a,b,c,x4,d,e), x4 = c^2 - a*d - b*e (mod 11)  [quadric x0x4+x1x5+x2x6=x3^2].
# gh_build enumerates normalized singular vectors in lexicographic order of (x0..x6) (x0 most significant), so the
# 16105 points with x0 = 0 come first and the chart points follow in the order of the key (a,b,c,x4,d,e).
# Usage: python3 chartmap.py GHTXT CHARTFILE OUTPTS [--check]
import sys, numpy as np
Q = 11
def load_gh(path):
    with open(path) as f:
        P, q = map(int, f.readline().split())
        LP = np.loadtxt(f, dtype=np.int32, ndmin=2)
    assert LP.shape == (P, q + 1), LP.shape
    flat = LP.ravel(); lines_of = np.repeat(np.arange(P, dtype=np.int32), q + 1)
    order = np.argsort(flat, kind='stable')
    PL = lines_of[order].reshape(P, q + 1)
    return P, q, LP, PL
def chart_map():
    A = np.arange(Q ** 5, dtype=np.int64)
    a = A % Q; b = (A // Q) % Q; c = (A // Q**2) % Q; d = (A // Q**3) % Q; e = (A // Q**4) % Q
    x4 = (c * c - a * d - b * e) % Q
    order = np.lexsort((e, d, x4, c, b, a))   # lexsort: last key is primary -> a most significant
    rank = np.empty_like(order); rank[order] = np.arange(len(order))
    return A, a, b, c, d, e, x4, 16105 + rank
if __name__ == '__main__':
    gh, chartf, outf = sys.argv[1], sys.argv[2], sys.argv[3]
    P, q, LP, PL = load_gh(gh)
    assert P == 177156 and q == 11
    A, a, b, c, d, e, x4, MAP = chart_map()
    S = np.loadtxt(chartf, dtype=np.int64, ndmin=2)
    Aidx = S[:, 0] + Q * S[:, 1] + Q**2 * S[:, 2] + Q**3 * S[:, 3] + Q**4 * S[:, 4]
    hexidx = MAP[Aidx]
    if '--check' in sys.argv:
        rng = np.random.default_rng(1)
        for trial in range(3):
            ui_pos = 0 if trial == 0 else int(rng.integers(len(hexidx)))
            u = int(hexidx[ui_pos])
            pts2 = np.unique(LP[PL[u]]); L3 = np.unique(PL[pts2]); pts4 = np.unique(LP[L3])
            ui = int(Aidx[ui_pos])
            ua, ub, uc, ud, ue = ui % Q, (ui // Q) % Q, (ui // Q**2) % Q, (ui // Q**3) % Q, (ui // Q**4) % Q
            qz = ((uc - c) ** 2 - (ua - a) * (ud - d) - (ub - b) * (ue - e)) % Q
            zero = MAP[qz == 0]
            inchart = pts4[pts4 >= 16105]
            print('u', u, 'BFS<=4 count', len(pts4), '(expect 16105)', 'chart part equals Q-zero set:',
                  np.array_equal(np.sort(inchart), np.sort(zero)), len(inchart), len(zero))
    np.savetxt(outf, hexidx, fmt='%d')
    print('mapped', len(hexidx), 'points to', outf)
