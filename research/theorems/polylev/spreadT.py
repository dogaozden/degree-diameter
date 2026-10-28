"""spreadT.py: Hermitian spreads S_v (lines of H(q) in the hyperplane v^perp) that are disjoint from all their
translates under the semiregular group T = <h> (order k). Such an S_v is a partial transversal of the T-orbits on
lines, so a T-transversal containing it is a dominating line class whose k translates are disjoint.
Scans v over representatives of T-orbits on PG(6,q) points (random sample), reports the distribution of
max_i |S_v cap h^i S_v|, and writes the first fully disjoint one.
Usage: python3 spreadT.py HEXBIN HMAT LPERM samples seed OUT"""
import sys
import numpy as np
from hexlib import Hex
from g2 import gram_row


def main():
    H = Hex(sys.argv[1])
    h = np.loadtxt(sys.argv[2], dtype=np.int64)
    lperm = np.fromfile(sys.argv[3], dtype=np.int32).astype(np.int64)
    samples, seed, out = int(sys.argv[4]), int(sys.argv[5]), sys.argv[6]
    rng = np.random.default_rng(seed)
    q, N = H.q, H.N
    k = 1
    x = lperm[0]
    while x != 0:
        x = lperm[x]
        k += 1
    # powers of the line permutation
    pw = [np.arange(N)]
    for i in range(1, k):
        pw.append(lperm[pw[-1]])
    X0 = H.coord[H.lines[:, 0]]
    X1 = H.coord[H.lines[:, 1]]
    hist = {}
    for t in range(samples):
        v = rng.integers(0, q, size=7)
        if not v.any():
            continue
        y = gram_row(H, v)
        d0 = np.zeros(N, dtype=np.int64)
        d1 = np.zeros(N, dtype=np.int64)
        for j in range(7):
            d0 = H.ADD[d0, H.MUL[y[j], X0[:, j]]]
            d1 = H.ADD[d1, H.MUL[y[j], X1[:, j]]]
        S = np.where((d0 == 0) & (d1 == 0))[0]
        if len(S) != q ** 3 + 1:
            continue
        inS = np.zeros(N, dtype=bool)
        inS[S] = True
        mx = max(int(inS[pw[i][S]].sum()) for i in range(1, k))
        hist[mx] = hist.get(mx, 0) + 1
        if mx == 0:
            print('disjoint from all translates: v =', v.tolist(), flush=True)
            np.save(out, S)
            break
    print('max overlap histogram (overlap: count):', dict(sorted(hist.items())))


if __name__ == '__main__':
    main()
