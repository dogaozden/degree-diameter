"""hexkit: small Python toolkit for the d10D7 round-3 squad (generalized hexagon H(q), freed flags, joint covers).

  from hexkit import *
  H = Hex(8)                        # loads research/d10D7/hex/hex_q8.bin (points 0..N-1, lines 0..N-1)
  d = H.bfs(p, isline=False)        # numpy int array: d[0:N] distances to points, d[N:2N] to lines
  F = H.random_opposite_flags(K, seed)   # list of (p, l), p on l, pairwise opposite
  H.mismatch(F)                     # sum over membership vectors of |#points - #lines| (0 = exact joint cover exists)
  M = H.joint_cover(F, seed)        # bijection points -> lines (numpy array), same-vector matching + leftovers
  H.uncovered(F, M)                 # per pair: (side A, side B) opposite targets with no type-4/type-2 route

Definitions (research/squads/exp2/hexd7/README.md and research/d10D7/d7hex.c):
  freed flag (p, l = M(p)), p on l.  S'(p) = points u with d(p,u) = 4, d(l,u) = 5 (q^4 of them);
  S(l) = lines L with d(l,L) = 4, d(p,L) = 5 (q^4).  Bit k of point u is set iff u in S'(p_k); of line L iff L in S(l_k).
  Side A of pair k: points x opposite p_k (d = 6) need a route: u with d(p_k,u) = 4, d(p_k,M(u)) = 5, x on M(u) [type 4]
  or d(p_k,u) = 2 and d(M(u), x) <= 3 [type 2].  Side B: lines t opposite l_k, dually (u = M^-1(L)).
  Flags (p,l), (p',l') are opposite iff d(p,p') = d(l,l') = 6 and d(p,l') = d(p',l) = 5.
CLI:  python3 hexkit.py mismatch Q K SEED      (random opposite flags)
"""
import os, struct, sys
import numpy as np

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..', '..', '..'))
HEXDIR = os.path.join(ROOT, 'research', 'd10D7', 'hex')

class Hex:
    def __init__(self, q):
        fn = os.path.join(HEXDIR, 'hex_q%d.bin' % q)
        with open(fn, 'rb') as f:
            qq, N, L = struct.unpack('3i', f.read(12))
            self.LP = np.frombuffer(f.read(4 * L * (qq + 1)), dtype=np.int32).reshape(L, qq + 1).copy()
        self.q, self.N = qq, N
        PL = np.zeros((N, qq + 1), dtype=np.int32); cnt = np.zeros(N, dtype=np.int32)
        for l in range(L):
            for p in self.LP[l]:
                PL[p, cnt[p]] = l; cnt[p] += 1
        self.PL = PL
        self._cache = {}

    def bfs(self, x, isline=False):
        key = (x, isline)
        if key in self._cache: return self._cache[key]
        N = self.N; d = np.full(2 * N, 255, dtype=np.int32)
        typ = 'L' if isline else 'P'; fr = np.array([x])
        d[N + x if isline else x] = 0; k = 0
        while True:
            k += 1
            if typ == 'P':
                nb = np.unique(self.PL[fr].ravel()); nb = nb[d[N + nb] == 255]
                if len(nb) == 0: break
                d[N + nb] = k; typ, fr = 'L', nb
            else:
                nb = np.unique(self.LP[fr].ravel()); nb = nb[d[nb] == 255]
                if len(nb) == 0: break
                d[nb] = k; typ, fr = 'P', nb
        if len(self._cache) < 4000: self._cache[key] = d
        return d

    def opposite(self, f1, f2):
        (p, l), (p2, l2) = f1, f2
        dp, dl = self.bfs(p), self.bfs(l, True)
        return dp[p2] == 6 and dl[self.N + l2] == 6 and dp[self.N + l2] == 5 and dl[p2] == 5

    def random_opposite_flags(self, K, seed=1, tries=10 ** 6):
        rng = np.random.default_rng(seed); F = []
        for _ in range(tries):
            if len(F) >= K: break
            p = int(rng.integers(self.N)); l = int(self.PL[p, rng.integers(self.q + 1)])
            if all(self.opposite((p, l), f) for f in F): F.append((p, l))
        return F

    def sets(self, p, l):
        N = self.N; dp, dl = self.bfs(p), self.bfs(l, True)
        Sp = (dp[:N] == 4) & (dl[:N] == 5)
        Sl = (dl[N:] == 4) & (dp[N:] == 5)
        return Sp, Sl

    def vectors(self, F):
        """membership vectors as python ints (arbitrary K)"""
        vp = [0] * self.N; vl = [0] * self.N
        for k, (p, l) in enumerate(F):
            Sp, Sl = self.sets(p, l)
            for u in np.nonzero(Sp)[0]: vp[u] |= 1 << k
            for L in np.nonzero(Sl)[0]: vl[L] |= 1 << k
        return vp, vl

    def mismatch(self, F):
        from collections import Counter
        vp, vl = self.vectors(F)
        freedP = {p for p, l in F}; freedL = {l for p, l in F}
        cp = Counter(v for u, v in enumerate(vp) if u not in freedP)
        cl = Counter(v for L, v in enumerate(vl) if L not in freedL)
        return sum(abs(cp[v] - cl[v]) for v in set(cp) | set(cl))

    def joint_cover(self, F, seed=1):
        """M: points -> lines; M[p_k] = l_k; same-vector matching, leftovers zipped by (popcount, vector)"""
        rng = np.random.default_rng(seed)
        vp, vl = self.vectors(F)
        freedP = {p for p, l in F}; freedL = {l for p, l in F}
        M = np.full(self.N, -1, dtype=np.int64)
        for p, l in F: M[p] = l
        from collections import defaultdict
        bp, bl = defaultdict(list), defaultdict(list)
        for u in rng.permutation(self.N):
            if int(u) not in freedP: bp[vp[u]].append(int(u))
        for L in rng.permutation(self.N):
            if int(L) not in freedL: bl[vl[L]].append(int(L))
        lp, ll = [], []
        for v in set(bp) | set(bl):
            a, b = bp.get(v, []), bl.get(v, [])
            m = min(len(a), len(b))
            for i in range(m): M[a[i]] = b[i]
            lp += [(bin(v).count('1'), v, u) for u in a[m:]]; ll += [(bin(v).count('1'), v, L) for L in b[m:]]
        lp.sort(); ll.sort()
        for (x, y) in zip(lp, ll): M[x[2]] = y[2]
        return M

    def ball3_points_of_line(self, L):
        pts = set(self.LP[L].tolist())
        for y in self.LP[L]:
            for L2 in self.PL[y]:
                if L2 != L: pts.update(self.LP[L2].tolist())
        return pts

    def ball3_lines_of_point(self, x):
        ls = set(self.PL[x].tolist())
        for L in self.PL[x]:
            for y in self.LP[L]:
                if y != x: ls.update(self.PL[y].tolist())
        return ls

    def uncovered(self, F, M, hub_edges=()):
        """per pair (side A, side B) uncovered opposite targets using type-4, type-2 routes (and hub-graph static
        coverage: hub edge (j,k) = line-side hub of pair j ~ point-side hub of pair k)."""
        N = self.N; M = np.asarray(M); Minv = np.empty(N, dtype=np.int64); Minv[M] = np.arange(N)
        freedP = np.zeros(N, bool); freedP[[p for p, l in F]] = True
        out = []
        for k, (p, l) in enumerate(F):
            dp, dl = self.bfs(p), self.bfs(l, True)
            covA = np.zeros(N, bool); covB = np.zeros(N, bool)
            for u in np.nonzero((dp[:N] == 4) & ~freedP)[0]:
                L = M[u]
                if dp[N + L] == 5: covA[self.LP[L]] = True
            for u in np.nonzero((dp[:N] == 2) & ~freedP)[0]:
                covA[list(self.ball3_points_of_line(M[u]))] = True
            for L in np.nonzero(dl[N:] == 4)[0]:
                y = Minv[L]
                if not freedP[y] and dl[y] == 5: covB[self.PL[y]] = True
            for L in np.nonzero(dl[N:] == 2)[0]:
                y = Minv[L]
                if not freedP[y]: covB[list(self.ball3_lines_of_point(y))] = True
            for (j, kk) in hub_edges:
                if j == k: covA[list(self.ball3_points_of_line(F[kk][1]))] = True
                if kk == k: covB[list(self.ball3_lines_of_point(F[j][0]))] = True
            oppA = dp[:N] == 6; oppB = dl[N:] == 6
            out.append((int((oppA & ~covA).sum()), int((oppB & ~covB).sum())))
        return out

if __name__ == '__main__':
    if sys.argv[1] == 'mismatch':
        q, K, seed = map(int, sys.argv[2:5]); H = Hex(q); F = H.random_opposite_flags(K, seed)
        print('flags', F); print('mismatch', H.mismatch(F))
