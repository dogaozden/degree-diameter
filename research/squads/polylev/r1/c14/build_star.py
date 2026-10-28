"""c14: the D = 10 'spread star' lift of H(q) (card c14 of squad polylev r1, test of the director's theorem).

Usage: python3 -I build_star.py HEXBIN SPREADFILE ROW SEED OUT.edges

Graph: vertices (v, g), v a point (0..N-1) or a line (N..2N-1), g in Z_m, m = 2K+1, vertex id g*2N + v.
Edges:
  (p,g)-(l,g) for p on l;
  for each point z:  (z,g)-(sig1(z), g + i(sig1(z)) + 1)  and  (z,g)-(sig2(z), g - i(sig2(z)) - 1)  (mod m),
where sig1, sig2 are seeded random bijections points -> lines and i(l) in {0..K-1} is the index in S of the unique
spread line s(l) equal to or meeting l. Degree q+3, 2N(2K+1) vertices, bipartite (points vs lines).
"""
import sys
import numpy as np

sys.path.insert(0, '/home/user/degree-diameter/research/theorems/polylev')
from hexlib import Hex  # noqa: E402


def main():
    hexbin, spfile, row, seed, out = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
    H = Hex(hexbin)
    q, N, L = H.q, H.N, H.L
    assert N == L
    rows = [r for r in open(spfile).read().split('\n') if r.strip()]
    S = [int(x) for x in rows[row].split()]
    K = len(S)
    assert K == q ** 3 + 1 and len(set(S)) == K, (K, q)

    # check 1: every line is equal to or meets exactly one spread line; i(l) = that index
    cnt = np.zeros(L, dtype=np.int64)
    idx = np.full(L, -1, dtype=np.int64)
    for i, s in enumerate(S):
        onS = np.zeros(N, dtype=bool)
        onS[H.lines[s]] = True
        meets = onS[H.lines].any(axis=1)
        cnt += meets
        idx[meets] = i
    hist = np.bincount(cnt, minlength=2)
    assert (cnt == 1).all(), f'not a perfect code: histogram of meeting counts {hist}'
    # check 2: spread lines pairwise opposite (distance 6 in the incidence graph)
    dmin = 99
    for s in S:
        d = H.bfs(N + s)
        for t in S:
            if t != s:
                dmin = min(dmin, int(d[N + t]))
    print(f'q={q} row={row} K={K} spread lines pairwise min distance={dmin}; each line meets exactly one S-line',
          flush=True)
    assert dmin == 6

    m = 2 * K + 1
    n2 = 2 * N
    rng = np.random.default_rng(seed)
    sig1 = rng.permutation(N)
    sig2 = rng.permutation(N)
    g = np.arange(m, dtype=np.int64)

    # incidence edges in every layer
    P = H.lines.ravel().astype(np.int64)
    Lid = np.repeat(np.arange(L, dtype=np.int64), q + 1)
    U_inc = (g[:, None] * n2 + P[None, :]).ravel()
    V_inc = (g[:, None] * n2 + N + Lid[None, :]).ravel()

    # the two cross matchings
    z = np.arange(N, dtype=np.int64)
    U_c = (g[:, None] * n2 + z[None, :]).ravel()
    h1 = (g[:, None] + idx[sig1][None, :] + 1) % m
    V1 = (h1 * n2 + N + sig1[None, :]).ravel()
    h2 = (g[:, None] - idx[sig2][None, :] - 1) % m
    V2 = (h2 * n2 + N + sig2[None, :]).ravel()

    U = np.concatenate([U_inc, U_c, U_c])
    V = np.concatenate([V_inc, V1, V2])
    nv = m * n2

    # sanity: simple and (q+3)-regular
    lo, hi = np.minimum(U, V), np.maximum(U, V)
    assert len(np.unique(lo * nv + hi)) == len(U), 'multi-edge'
    assert (U != V).all()
    deg = np.bincount(np.concatenate([U, V]), minlength=nv)
    assert (deg == q + 3).all(), np.unique(deg, return_counts=True)

    with open(out, 'w') as f:
        f.write(f'{nv}\n')
        np.savetxt(f, np.stack([U, V], axis=1), fmt='%d')
    print(f'q={q} K={K} m={m} seed={seed}: {nv} vertices, degree {q + 3}, {len(U)} edges -> {out}', flush=True)


if __name__ == '__main__':
    main()
