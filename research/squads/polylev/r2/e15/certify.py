"""certify.py: independent check of a set of lines of Q(6,q) (q prime) given as point ids of the hexagon file.
Checks, from the coordinates alone (no search code, no group):
  - the point file has N = (q^6-1)/(q-1) distinct normalised points, all on Q(x) = x0x4+x1x5+x2x6-x3^2 = 0;
  - every line has q+1 distinct point ids; the q+1 points have rank 2 (they span a projective line);
  - all points of a line are pairwise orthogonal for b(x,y) = x0y4+x4y0+x1y5+x5y1+x2y6+x6y2-2x3y3 (so the line is
    totally singular: it lies on Q since its points are singular and pairwise orthogonal);
  - the lines are pairwise disjoint: all K(q+1) point ids are distinct.
Usage: python3 certify.py HEXBIN q LINES.i32
"""
import sys, struct
import numpy as np


def main():
    hexpath, q, path = sys.argv[1], int(sys.argv[2]), sys.argv[3]
    assert all(q % d for d in range(2, q)), 'prime q only'
    with open(hexpath, 'rb') as f:
        qh, N, L = struct.unpack('3i', f.read(12))
        assert qh == q
        f.seek(12 + 4 * L * (q + 1))
        X = np.frombuffer(f.read(N * 7), dtype=np.uint8).reshape(N, 7).astype(np.int64)
    ok = True
    if N != (q ** 6 - 1) // (q - 1):
        print('hex file: wrong number of points'); ok = False
    if (X < 0).any() or (X >= q).any():
        print('hex file: coordinate out of range'); ok = False
    Qx = (X[:, 0] * X[:, 4] + X[:, 1] * X[:, 5] + X[:, 2] * X[:, 6] - X[:, 3] ** 2) % q
    if (Qx != 0).any():
        print('hex file: non-singular point'); ok = False
    first = np.argmax(X != 0, axis=1)
    lead = X[np.arange(N), first]
    if not (lead == 1).all():
        print('hex file: points not normalised'); ok = False
    if len(np.unique(X @ (q ** np.arange(7, dtype=np.int64)))) != N:
        print('hex file: repeated points'); ok = False
    print(f'point set: N={N} points of Q(6,{q}) checked: {"ok" if ok else "FAILED"}')

    E = np.fromfile(path, dtype=np.int32).astype(np.int64).reshape(-1, q + 1)
    K = len(E)
    if E.min() < 0 or E.max() >= N:
        print('line file: id out of range'); print(f'CERTIFIED q={q} K=0 valid=False'); return
    P = X[E]                                   # K x (q+1) x 7
    srt = np.sort(E, axis=1)
    if (np.diff(srt, axis=1) == 0).any():
        print('some line repeats a point'); ok = False
    QP = (P[..., 0] * P[..., 4] + P[..., 1] * P[..., 5] + P[..., 2] * P[..., 6] - P[..., 3] ** 2) % q
    if (QP != 0).any():
        print('some line point is not singular'); ok = False
    G = np.zeros((7, 7), dtype=np.int64)
    for i, j in ((0, 4), (4, 0), (1, 5), (5, 1), (2, 6), (6, 2)):
        G[i, j] = 1
    G[3, 3] = -2
    PG = np.einsum('kpi,ij->kpj', P, G) % q
    Gram = np.einsum('kpj,krj->kpr', PG, P) % q
    idx = np.arange(q + 1)
    Gram[:, idx, idx] = 0
    if (Gram != 0).any():
        print('some two points of a line are not orthogonal'); ok = False
    # rank 2: every 3x3 minor of [point0; point1; point t] vanishes (point 0 and 1 are distinct points, hence
    # independent vectors)
    a, b = P[:, 0, :], P[:, 1, :]
    rank_bad = False
    for t in range(2, q + 1):
        c = P[:, t, :]
        for i in range(7):
            for j in range(i + 1, 7):
                for k in range(j + 1, 7):
                    M = np.stack([a[:, [i, j, k]], b[:, [i, j, k]], c[:, [i, j, k]]], axis=1)
                    d = (M[:, 0, 0] * (M[:, 1, 1] * M[:, 2, 2] - M[:, 1, 2] * M[:, 2, 1])
                         - M[:, 0, 1] * (M[:, 1, 0] * M[:, 2, 2] - M[:, 1, 2] * M[:, 2, 0])
                         + M[:, 0, 2] * (M[:, 1, 0] * M[:, 2, 1] - M[:, 1, 1] * M[:, 2, 0])) % q
                    if (d != 0).any():
                        rank_bad = True
    if rank_bad:
        print('some line does not have rank 2'); ok = False
    flat = E.ravel()
    ndist = len(np.unique(flat))
    if ndist != flat.size:
        print(f'lines NOT pairwise disjoint: {flat.size - ndist} repeated point incidences'); ok = False
    print(f'line file: K={K} lines of {q + 1} points, totally singular and pairwise disjoint: '
          f'{"ok" if ok else "FAILED"}')
    print(f'CERTIFIED q={q} K={K if ok else 0} valid={ok}')


if __name__ == '__main__':
    main()
