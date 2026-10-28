"""d11graph.py: the D = 11 ball lift of Corollary 5.5 (POLYGON_LEVELS.md) as an implicit graph, from a certificate
(K pairwise disjoint t.s. lines of Q(6,q) as rows of q+1 point ids, and pairwise non-collinear point ids; ids are those
of the lab's hexagon files written by research/d10D7/hexgen2.c).

Fixed choices (any choice works by Theorem 2.3; these make the graph explicit):
  * the line classes are the pencils of the K smallest chosen point ids; class i of either side is the i-th row of the
    lines file and the pencil of the i-th smallest point;
  * the points not on a chosen line, in increasing id order, go to classes 0, 1, ..., K-1, 0, 1, ... (the j-th one to
    class j mod K); the lines not in a chosen pencil likewise; so |A_i| = |B_i| for every i;
  * sigma_1 maps the j-th smallest point of A_i to the j-th smallest line of B_i (for r > 1, sigma_t = sigma_1);
  * vertex (x, g), x in P u L, g in Z_m, m = 2rK+1, has id g*2N + x (points 0..N-1, lines N + line id).
Neighbours: (p, g) ~ (l, g) for p on l; (z, g) ~ (sigma_t(z), g + (t-1)K + i + 1) for z in A_i, t = 1..r.

Modes:  nbr HEX LINES POINTS r VERTEX           print the neighbours of one vertex
        sample HEX LINES POINTS r PAIRS SEED     check d(u, v) <= 11 for random pairs, by B_5(u) meeting B_6(v)"""
import sys
import numpy as np
sys.path.insert(0, __file__.rsplit('/', 2)[0])
from hexlib import Hex


class Lift:
    def __init__(self, hexbin, linesf, pointsf, r):
        H = self.H = Hex(hexbin); N = self.N = H.N; q = H.q
        C = np.loadtxt(linesf, dtype=np.int64, ndmin=2)
        Z = np.sort(np.loadtxt(pointsf, dtype=np.int64, ndmin=1))
        K = self.K = min(len(C), len(Z)); C, Z = C[:K], Z[:K]
        self.r, self.m = r, 2 * r * K + 1
        pc = -np.ones(N, dtype=np.int64); lc = -np.ones(N, dtype=np.int64)
        for i in range(K):
            assert (pc[C[i]] < 0).all(); pc[C[i]] = i
            assert (lc[H.PL[Z[i]]] < 0).all(); lc[H.PL[Z[i]]] = i
        rest_p = np.where(pc < 0)[0]; rest_l = np.where(lc < 0)[0]
        assert len(rest_p) == len(rest_l)
        pc[rest_p] = np.arange(len(rest_p)) % K; lc[rest_l] = np.arange(len(rest_l)) % K
        self.pc, self.lc = pc, lc
        sig = np.empty(N, dtype=np.int64)
        op = np.lexsort((np.arange(N), pc)); ol = np.lexsort((np.arange(N), lc))
        assert (pc[op] == lc[ol]).all()                 # same class sizes, so the sorted lists align
        sig[op] = ol; self.sig = sig; inv = np.empty(N, dtype=np.int64); inv[sig] = np.arange(N); self.inv = inv

    def nbrs(self, V):
        """neighbours of an array of vertex ids (flattened, with repetitions)"""
        H, N, m = self.H, self.N, self.m
        g, x = V // (2 * N), V % (2 * N)
        out = []
        P = x < N
        gp, p = g[P], x[P]
        out.append((gp[:, None] * 2 * N + N + H.PL[p]).ravel())
        for t in range(self.r):
            out.append(((gp + t * self.K + self.pc[p] + 1) % m) * 2 * N + N + self.sig[p])
        gl, l = g[~P], x[~P] - N
        out.append((gl[:, None] * 2 * N + H.lines[l]).ravel())
        for t in range(self.r):
            out.append(((gl - t * self.K - self.lc[l] - 1) % m) * 2 * N + self.inv[l])
        return np.concatenate(out)

    def ball(self, v, rad):
        seen = np.array([v]); fr = seen
        for _ in range(rad):
            nb = np.unique(self.nbrs(fr)); fr = np.setdiff1d(nb, seen, assume_unique=True)
            seen = np.union1d(seen, fr)
        return seen


def main():
    mode = sys.argv[1]
    G = Lift(sys.argv[2], sys.argv[3], sys.argv[4], int(sys.argv[5]))
    print(f'q={G.H.q} N={G.N} K={G.K} r={G.r} m={G.m}: {2 * G.N * G.m:,} vertices, degree {G.H.q + 1 + G.r}')
    if mode == 'nbr':
        v = int(sys.argv[6]); print(v, '->', sorted(G.nbrs(np.array([v])).tolist()))
        return
    pairs, rng = int(sys.argv[6]), np.random.default_rng(int(sys.argv[7]))
    n = 2 * G.N * G.m; worst = 0; bad = 0
    for k in range(pairs):
        u = int(rng.integers(n))
        v = int(rng.integers(n)) if k % 2 else int((u + 2 * G.N * int(rng.integers(1, G.m))) % n)   # half: same element, other layer
        B5, B6 = G.ball(u, 5), G.ball(v, 6)
        ok = np.intersect1d(B5, B6).size > 0
        bad += not ok
        worst += np.intersect1d(B5, G.ball(v, 5)).size == 0          # distance > 10 (control: should happen)
        w = G.nbrs(np.array([u]))                                     # degree and symmetry of the adjacency
        assert len(np.unique(w)) == G.H.q + 1 + G.r and all(u in G.nbrs(np.array([x])) for x in w)
    print(f'{pairs} random pairs: {pairs - bad} at distance <= 11, {bad} farther; {worst} at distance > 10; '
          f'sampled vertices have {G.H.q + 1 + G.r} distinct neighbours and the adjacency is symmetric')


if __name__ == '__main__':
    main()
