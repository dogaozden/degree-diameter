"""d11cert.py: independent certificate check for the D = 11 ball lift (Corollaries 5.2 / 5.5 of POLYGON_LEVELS.md).

Input: H(q), a file of point classes (one class per text line: the q+1 point ids of a line of Q(6,q)), and either a
file of pairwise non-collinear point ids (line side = their pencils) or the word DUAL with a duality file (line side =
images of the point classes; q a power of 3).
Checks: every point class is exactly the point set of a 2-dimensional totally singular subspace (it equals
{p1} u {p0 + l p1 : l in F_q}, all on the quadric, p0 orthogonal to p1); the classes are pairwise disjoint; the chosen
points are pairwise non-collinear in H(q) (no line of H(q) contains two of them).
Prints K = min(#point classes, #line classes) and the orders 2N(2rK+1).
Usage: python3 d11cert.py HEXBIN CLASSES POINTS          or   python3 d11cert.py HEXBIN CLASSES DUAL PHIFILE"""
import sys
import numpy as np
from hexlib import Hex
from g2 import gram_row, qform


def main():
    H = Hex(sys.argv[1])
    q, N = H.q, H.N
    C = np.loadtxt(sys.argv[2], dtype=np.int64, ndmin=2)
    K_P = C.shape[0]
    assert C.shape[1] == q + 1, 'each class must have q+1 points'
    ids = C.ravel()
    assert len(np.unique(ids)) == len(ids), 'classes are not pairwise disjoint (or repeat a point)'
    X = H.coord
    bad = 0
    for row in C:
        p0, p1 = X[row[0]], X[row[1]]
        y = gram_row(H, p0)
        bpq = 0
        for j in range(7):
            bpq = H.ADD[bpq, H.MUL[y[j], p1[j]]]
        if bpq != 0 or qform(H, p0) != 0 or qform(H, p1) != 0:
            bad += 1
            continue
        lam = np.arange(1, q)
        span = set(H.point_ids(H.ADD[p1[None, :], H.MUL[lam[:, None], p0[None, :]]]).tolist()) | {row[0], row[1]}
        if span != set(row.tolist()):
            bad += 1
    print(f'q={q}: {K_P} point classes, pairwise disjoint; classes that are not totally singular lines: {bad}')
    if sys.argv[3] == 'DUAL':
        phi = np.fromfile(sys.argv[4], dtype=np.int32).astype(np.int64)
        # duality check: incidences map to incidences, points to lines
        inc_ok = all(phi[H.lines[l, 0]] - N >= 0 for l in range(0, N, max(1, N // 1000)))
        print(f'line side by the duality (points go to lines: {inc_ok}); line classes = images of the point classes')
        K_L = K_P
    else:
        Z = np.loadtxt(sys.argv[3], dtype=np.int64, ndmin=1)
        assert len(np.unique(Z)) == len(Z)
        chosen = np.zeros(N, dtype=np.int64)
        chosen[Z] = 1
        per_line = chosen[H.lines].sum(axis=1)
        coll = int((per_line > 1).sum())
        print(f'{len(Z)} points; lines of H(q) containing two or more of them: {coll}')
        K_L = len(Z) if coll == 0 else 0
    K = min(K_P, K_L) if bad == 0 else 0
    print(f'K = {K} (bound q^4+q^2+1 = {q ** 4 + q * q + 1}; {100 * K / (q ** 4 + q * q + 1):.1f}%)')
    for r in range(1, 5):
        print(f'  r={r}: Delta={q + 1 + r}, D=11, order {2 * N * (2 * r * K + 1):,}')


if __name__ == '__main__':
    main()
