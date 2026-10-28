"""qspread.py: pairwise disjoint totally singular lines of Q(6,q) (not necessarily lines of H(q)), by randomized
greedy. Any totally singular line of Q(6,q) meets every point 4-ball of H(q) (Lemma 5.4 of POLYGON_LEVELS.md), so
K disjoint such lines give K disjoint 4-dominating point classes for the D = 11 ball lift.

For q = 3^h, a duality phi of H(q) maps each class to a set of q+1 lines of H(q) that meets every line 4-ball, so
the same K serves the line side (balanced).
Writes OUT.pcol (int32 point colour: index of the line, -1 if uncovered); with a duality file (dualfind .phi), also
OUT.lcol (line colours: line phi(x) gets the colour of the point x).
Usage: python3 qspread.py HEXBIN SEED OUT [PHIFILE]"""
import sys
import numpy as np
from hexlib import Hex
from g2 import gram_row


def main():
    H = Hex(sys.argv[1])
    rng = np.random.default_rng(int(sys.argv[2]))
    out = sys.argv[3]
    q, N = H.q, H.N
    X = H.coord
    covered = np.zeros(N, dtype=bool)
    col = -np.ones(N, dtype=np.int64)
    K = 0
    lam = np.arange(1, q)
    for p in rng.permutation(N):
        if covered[p]:
            continue
        y = gram_row(H, X[p])
        val = np.zeros(N, dtype=np.int64)
        for j in range(7):
            val = H.ADD[val, H.MUL[y[j], X[:, j]]]
        cand = np.where((val == 0) & ~covered)[0]
        cand = cand[cand != p]
        rng.shuffle(cand)
        for x in cand[:60]:
            # points p + l x (l != 0) and x
            P = H.ADD[X[p][None, :], H.MUL[lam[:, None], X[x][None, :]]]
            ids = np.concatenate([H.point_ids(P), [x, p]])
            if len(set(ids.tolist())) != q + 1 or covered[ids].any():
                continue
            covered[ids] = True
            col[ids] = K
            K += 1
            break
    print(f'q={q}: {K} pairwise disjoint singular lines covering {covered.sum()} of {N} points '
          f'(bound N/(q+1) = {N // (q + 1)}; {100 * K * (q + 1) / N:.1f}%)')
    col.astype(np.int32).tofile(out + '.pcol')
    if len(sys.argv) > 4:
        phi = np.fromfile(sys.argv[4], dtype=np.int32).astype(np.int64)
        lcol = -np.ones(N, dtype=np.int64)
        for x in range(N):
            if col[x] >= 0:
                lcol[phi[x] - N] = col[x]
        lcol.astype(np.int32).tofile(out + '.lcol')
        print('line colours written via the duality')


if __name__ == '__main__':
    main()
