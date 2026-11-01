#!/usr/bin/env python3
"""Weyl-distance graphs of finite thick buildings (job beat-16-5-squad).

A spherical building of Coxeter type (W, S) with node parameters q_s (each s-panel has q_s + 1 chambers).
Side A: residues of type I.  Side B: residues of type J (two separate copies, so the graph is bipartite).
Adjacency: R ~ R' iff delta(R, R') (a (W_I, W_J)-double coset) lies in X, a chosen union of double cosets.

  degrees   d_A = N_X / P_J,  d_B = N_X / P_I,  N_X = sum_{x in X} q_x,  P_K = sum_{v in W_K} q_v
  orders    |A| = P_W / P_I,  |B| = P_W / P_J
  diameter  walks compose by the BN-pair set product  BxB.BsB = BxsB if l(xs) > l(x), else BxB u BxsB
            (any group with a BN-pair).  R_0 = W_I, R_{k+1} = R_k * X (k even) or R_k * X^-1 (k odd);
            the I-vertex reaches every J-vertex within odd k and every I-vertex within even k once the union of the
            R_j of that parity is all of W.  Same for the J side.

The flag graph of PG(4,3) is type A4, q = 3, I = {2,4}, J = {1,3}, X = W_I W_J (the identity double coset):
16-regular, 31,460 vertices, diameter 5 (selftest below).
usage: python3 weyl_graphs.py selftest | scan [maxorder]
"""
import itertools, sys
import numpy as np


def cartan(t, n):
    C = np.zeros((n, n), dtype=int)
    for i in range(n):
        C[i, i] = 2
    if t == 'A':
        for i in range(n - 1):
            C[i, i + 1] = C[i + 1, i] = -1
    elif t in 'BC':
        for i in range(n - 1):
            C[i, i + 1] = C[i + 1, i] = -1
        if t == 'B':
            C[n - 2, n - 1] = -2   # alpha_n short
        else:
            C[n - 1, n - 2] = -2
    elif t == 'D':
        for i in range(n - 2):
            C[i, i + 1] = C[i + 1, i] = -1
        C[n - 3, n - 1] = C[n - 1, n - 3] = -1
    elif t == 'E':   # Bourbaki: 1-3-4-5-6(-7-8), 2 attached to 4 (0-based: 0-2-3-4-5.., 1 attached to 3)
        chain = [0, 2, 3] + list(range(4, n))
        for a, b in zip(chain, chain[1:]):
            C[a, b] = C[b, a] = -1
        C[1, 3] = C[3, 1] = -1
    elif t == 'F':   # 1-2=>3-4
        C[0, 1] = C[1, 0] = -1
        C[1, 2] = -2; C[2, 1] = -1
        C[2, 3] = C[3, 2] = -1
    elif t == 'G':
        C[0, 1] = -3; C[1, 0] = -1
    else:
        raise ValueError(t)
    return C


class Coxeter:
    def __init__(self, t, n):
        self.t, self.n = t, n
        C = cartan(t, n)
        roots = [tuple(int(i == j) for j in range(n)) for i in range(n)]
        idx = {r: k for k, r in enumerate(roots)}
        k = 0
        while k < len(roots):
            b = roots[k]
            for i in range(n):
                c = sum(b[j] * C[i, j] for j in range(n))
                nb = list(b); nb[i] -= c; nb = tuple(nb)
                if nb not in idx:
                    idx[nb] = len(roots); roots.append(nb)
            k += 1
        self.roots = roots
        m = len(roots)
        pos = np.array([all(x >= 0 for x in r) for r in roots])
        assert pos.sum() * 2 == m
        sperm = []
        for i in range(n):
            p = np.empty(m, dtype=np.int32)
            for kk, b in enumerate(roots):
                c = sum(b[j] * C[i, j] for j in range(n))
                nb = list(b); nb[i] -= c
                p[kk] = idx[tuple(nb)]
            sperm.append(p)
        posidx = np.nonzero(pos)[0]
        ident = np.arange(m, dtype=np.int32)
        elems = [ident]; eidx = {ident.tobytes(): 0}
        word = [()]
        R = []   # right multiplication table, filled lazily
        k = 0
        while k < len(elems):
            w = elems[k]
            row = []
            for i in range(n):
                ws = w[sperm[i]]          # (w s)(a) = w(s(a))
                key = ws.tobytes()
                if key not in eidx:
                    eidx[key] = len(elems); elems.append(ws); word.append(word[k] + (i,))
                row.append(eidx[key])
            R.append(row)
            k += 1
        N = len(elems)
        self.N = N
        self.R = np.array(R, dtype=np.int32)              # R[w, s] = index of w s
        L = np.empty((N, n), dtype=np.int32)
        for k2, w in enumerate(elems):
            for i in range(n):
                L[k2, i] = eidx[sperm[i][w].tobytes()]   # (s w)(a) = s(w(a))
        self.L = L
        neg = ~pos
        self.len = np.array([int(neg[w[posidx]].sum()) for w in elems], dtype=np.int32)
        self.word = word                                  # BFS words are reduced (BFS by length)
        assert all(len(word[k2]) == self.len[k2] for k2 in range(N))
        self.UP = self.len[self.R] > self.len[:, None]
        inv = np.empty(N, dtype=np.int32)
        for k2, w in enumerate(elems):
            wi = np.empty(m, dtype=np.int32); wi[w] = np.arange(m, dtype=np.int32)
            inv[k2] = eidx[wi.tobytes()]
        self.inv = inv

    def qw(self, params):
        q = np.zeros(self.N, dtype=object)
        q[0] = 1
        order = np.argsort(self.len, kind='stable')
        for w in order:
            for i in range(self.n):
                if self.UP[w, i]:
                    q[self.R[w, i]] = q[w] * params[i]
        return q

    def parabolic(self, K):
        S = np.zeros(self.N, dtype=bool); S[0] = True
        return self.rclose(S, K)

    def rclose(self, U, K):
        U = U.copy()
        while True:
            V = U.copy()
            for i in K:
                V[self.R[U, i]] = True
            if V.sum() == U.sum():
                return V
            U = V

    def lclose(self, U, K):
        U = U.copy()
        while True:
            V = U.copy()
            for i in K:
                V[self.L[U, i]] = True
            if V.sum() == U.sum():
                return V
            U = V

    def double_cosets(self, I, J):
        seen = np.zeros(self.N, dtype=bool)
        out = []
        for w in np.argsort(self.len, kind='stable'):
            if seen[w]:
                continue
            S = np.zeros(self.N, dtype=bool); S[w] = True
            while True:
                T = self.lclose(self.rclose(S, J), I)
                if T.sum() == S.sum():
                    break
                S = T
            seen |= S
            out.append((int(w), S))   # w is of minimal length in its double coset
        return out

    def times_elem(self, U, y):
        """BN set product U * y (y applied as its reduced word, letter by letter on the right)."""
        for i in self.word[y]:
            up = U & self.UP[:, i]
            dn = U & ~self.UP[:, i]
            V = np.zeros(self.N, dtype=bool)
            V[self.R[up, i]] = True
            V[dn] = True
            V[self.R[dn, i]] = True
            U = V
        return U


def ecc_side(C, I_close, X_reps, Xi_reps, Kfirst, Ksecond, maxsteps=12):
    """Return (same-side radius, opposite radius) for a vertex of the side whose residues have type Kfirst... .
    X_reps: minimal reps of the double cosets in the relation from this side to the other (right closure by Ksecond),
    Xi_reps: reps of the inverse relation (right closure by Kfirst)."""
    R = I_close.copy()
    same = R.copy(); opp = np.zeros(C.N, dtype=bool)
    rs = ro = None
    for k in range(1, maxsteps + 1):
        reps, Kc = (X_reps, Ksecond) if k % 2 == 1 else (Xi_reps, Kfirst)
        V = np.zeros(C.N, dtype=bool)
        for y in reps:
            V |= C.times_elem(R, y)
        V = C.rclose(V, Kc)
        R = V
        if k % 2 == 1:
            opp |= R
            if ro is None and opp.all():
                ro = k
        else:
            same |= R
            if rs is None and same.all():
                rs = k
        if rs is not None and ro is not None:
            return rs, ro
    return rs, ro


def graph_data(C, params, I, J, Xidx, dcs, q):
    """Xidx: indices into dcs (list of (rep, mask)) for the relation."""
    NX = sum(sum(q[np.nonzero(dcs[i][1])[0]]) for i in Xidx)
    PI = sum(q[np.nonzero(C.parabolic(I))[0]])
    PJ = sum(q[np.nonzero(C.parabolic(J))[0]])
    PW = sum(q)
    return NX, PI, PJ, PW


def selftest():
    C = Coxeter('A', 4)
    assert C.N == 120
    params = [3, 3, 3, 3]
    q = C.qw(params)
    I, J = (1, 3), (0, 2)          # 0-based: types {2,4} and {1,3}
    dcs = C.double_cosets(I, J)
    X = [k for k, (w, S) in enumerate(dcs) if w == 0]
    NX, PI, PJ, PW = graph_data(C, params, I, J, X, dcs, q)
    print('A4(3): |W| =', C.N, 'P_W =', PW, 'P_I =', PI, 'P_J =', PJ, 'N_X =', NX,
          'deg', NX // PJ, NX // PI, 'order', PW // PI + PW // PJ)
    reps = [dcs[k][0] for k in X]
    inv = [int(C.inv[y]) for y in reps]
    eA = ecc_side(C, C.parabolic(I), reps, inv, I, J)
    eB = ecc_side(C, C.parabolic(J), inv, reps, J, I)
    print('  side A (same, opp) radii', eA, ' side B', eB)
    # G2(4) hexagon, chambers, X = {s1 s2}: degree 16, 13,650 vertices
    G = Coxeter('G', 2)
    q2 = G.qw([4, 4])
    dc = G.double_cosets((), ())
    w12 = [k for k in range(G.N) if G.word[k] == (0, 1)][0]
    eA = ecc_side(G, G.parabolic(()), [w12], [int(G.inv[w12])], (), ())
    print('G2(4) chambers, X={s1s2}: P_W =', sum(q2), 'radii', eA)


if __name__ == '__main__':
    if sys.argv[1] == 'selftest':
        selftest()


def moore_side(dA, dB):
    return 1 + dA * (dB - 1) + dA * (dB - 1) * (dA - 1) * (dB - 1)


def buildings():
    out = []
    for n in range(2, 7):
        for qq in (2, 3, 4, 5, 7, 8, 9, 11, 13, 16):
            out.append((f'A{n}({qq})', 'A', n, [qq] * n))
    for n in range(2, 6):
        for qq in (2, 3, 4, 5, 7, 8, 9, 11, 13):
            for name, t in ((f'B{n}/C{n}({qq})', qq), (f'2D{n+1}({qq}) Q-(2n+1)', qq * qq)):
                out.append((name, 'B', n, [qq] * (n - 1) + [t]))
        for qq in (2, 3, 4):
            out.append((f'2A{2*n-1}({qq}) H(2n-1,q^2)', 'B', n, [qq * qq] * (n - 1) + [qq]))
            out.append((f'2A{2*n}({qq}) H(2n,q^2)', 'B', n, [qq * qq] * (n - 1) + [qq ** 3]))
    for n in (4, 5):
        for qq in (2, 3, 4, 5):
            out.append((f'D{n}({qq})', 'D', n, [qq] * n))
    for qq in (2, 3):
        out.append((f'E6({qq})', 'E', 6, [qq] * 6))
        out.append((f'F4({qq})', 'F', 4, [qq] * 4))
        out.append((f'2E6({qq})', 'F', 4, [qq, qq, qq * qq, qq * qq]))
    for qq in (2, 3, 4, 5, 7, 8, 9, 11, 13, 16):
        out.append((f'G2({qq})', 'G', 2, [qq, qq]))
    for qq in (2, 3, 4):
        out.append((f'3D4({qq})', 'G', 2, [qq, qq ** 3]))
    return out


def scan(maxdeg=16, minorder=31461, maxD=5, show_near=6, maxX=200000):
    cache = {}
    results = []
    for name, t, n, params in buildings():
        key = (t, n)
        if key not in cache:
            cache[key] = Coxeter(t, n)
        C = cache[key]
        q = C.qw(params)
        PW = int(sum(q))
        subsets = [K for r in range(n) for K in itertools.combinations(range(n), r)]
        PK = {K: int(sum(q[np.nonzero(C.parabolic(K))[0]])) for K in subsets}
        side = {K: PW // PK[K] for K in subsets}
        good = [K for K in subsets if side[K] <= moore_side(maxdeg, maxdeg)]
        for I in good:
            for J in good:
                if side[I] + side[J] < minorder:
                    continue
                if (J, I) < (I, J) and side[I] == side[J]:
                    pass
                dcs = C.double_cosets(I, J)
                ND = [int(sum(q[np.nonzero(S)[0]])) for (w, S) in dcs]
                budget = maxdeg * min(PK[I], PK[J])
                cand = sorted([k for k in range(len(dcs)) if ND[k] <= budget], key=lambda k: ND[k])
                # enumerate unions with N_X <= budget (dA, dB <= maxdeg)
                count = 0
                stack = [((), 0, 0)]
                while stack:
                    X, NX, start = stack.pop()
                    if X:
                        dA, dB = NX // PK[J], NX // PK[I]
                        if dA <= maxdeg and dB <= maxdeg and side[I] <= moore_side(dA, dB) and \
                                side[J] <= moore_side(dB, dA):
                            count += 1
                            if count > maxX:
                                break
                            reps = [dcs[k][0] for k in X]
                            inv = [int(C.inv[y]) for y in reps]
                            eA = ecc_side(C, C.parabolic(I), reps, inv, I, J, maxsteps=2 * show_near)
                            eB = ecc_side(C, C.parabolic(J), inv, reps, J, I, maxsteps=2 * show_near)
                            vals = [v for v in (eA + eB)]
                            if all(v is not None for v in vals):
                                D = max(vals)
                                if D <= show_near:
                                    words = [''.join(str(i + 1) for i in C.word[y]) or 'e' for y in reps]
                                    rec = (D, side[I] + side[J], name, I, J, words, dA, dB, side[I], side[J])
                                    results.append(rec)
                                    if D <= maxD:
                                        print('HIT', rec, flush=True)
                    for k in range(start, len(cand)):
                        kk = cand[k]
                        if NX + ND[kk] > budget:
                            break
                        stack.append((X + (kk,), NX + ND[kk], k + 1))
                if count > maxX:
                    print('  truncated', name, I, J, flush=True)
        print('done', name, 'P_W', PW, flush=True)
    results.sort(key=lambda r: (r[0], -r[1]))
    print('\n== best by diameter (D, order, building, I, J, X words, dA, dB, |A|, |B|) ==')
    for r in results[:60]:
        print(r)
    return results


if __name__ == '__main__' and sys.argv[1] == 'scan':
    scan()
