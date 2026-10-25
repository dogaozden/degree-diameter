"""Typed level covers of the incidence graph I of H(q), freed sets, hubs, and the sets used by the tests.

Levels j = 0..L-1, each a copy of I with a type tau_j in {H, D}. A-class of level j: points if H, lines if D; B-class: the
other one. Vertex (e, j) has id j*2N + e (e = element id from hexq: points 0..N-1, lines N..2N-1); hubs follow.
A transition is (j, j2, M, R): M is an int array of length 2N with M[a] = the B-element of level j2 matched to the
A-element a of level j (-1 off the A-class); the edges (a, j) ~ (M[a], j2) for a in R are deleted.
"""
import os, subprocess, re
import numpy as np
from hexq import Hex, write_edges, HERE

APSP = os.path.join(HERE, 'apsp_mt')
FAR = os.path.join(HERE, 'farcount')


def aclass(H, t):
    return np.arange(H.N) if t == 'H' else H.N + np.arange(H.N)


def bclass(H, t):
    return aclass(H, 'D' if t == 'H' else 'H')


def identity_map(H, t1, t2):
    """friendly transition (t1 != t2): identity on the common element set"""
    assert t1 != t2
    M = -np.ones(2 * H.N, dtype=np.int64)
    A = aclass(H, t1)
    M[A] = A
    return M


def random_map(H, t1, t2, rng):
    M = -np.ones(2 * H.N, dtype=np.int64)
    M[aclass(H, t1)] = rng.permutation(bclass(H, t2))
    return M


def cyclic_transitions(types, r):
    L = len(types)
    return [(j, (j + k) % L) for j in range(L) for k in range(1, r + 1)]


class Cover:
    def __init__(self, H, types, transitions):
        """transitions: list of (j, j2, M, R)"""
        self.H, self.types, self.tr = H, list(types), transitions
        self.L = len(types)

    def vid(self, e, j):
        return j * 2 * self.H.N + e

    def main_edges(self):
        H, N = self.H, self.H.N
        E = []
        inc = [(p, l) for l in range(N, 2 * N) for p in H.lines[l - N]]
        for j in range(self.L):
            E += [(self.vid(p, j), self.vid(l, j)) for p, l in inc]
        for (j, j2, M, R) in self.tr:
            A = aclass(H, self.types[j])
            assert (M[A] >= 0).all()
            assert sorted(M[A]) == sorted(bclass(H, self.types[j2])), 'M is not a bijection A_j -> B_j2'
            Rs = set(int(x) for x in R)
            assert Rs <= set(int(a) for a in A)
            E += [(self.vid(a, j), self.vid(M[a], j2)) for a in A if int(a) not in Rs]
        return E

    def n_main(self):
        return self.L * 2 * self.H.N

    def slots(self):
        """free A-slots and B-slots per level (lists of vertex ids, with multiplicity)"""
        sa = [[] for _ in range(self.L)]
        sb = [[] for _ in range(self.L)]
        for (j, j2, M, R) in self.tr:
            for a in R:
                sa[j].append(self.vid(a, j))
                sb[j2].append(self.vid(M[a], j2))
        return sa, sb

    def with_hubs(self, KB, KA, hubdeg, rng, hub_edges=None):
        """KB B-hubs (one free A-slot per level), KA A-hubs (one free B-slot per level), hub graph = hub_edges or a random
        bipartite graph with all degrees <= hubdeg (union of random matchings)."""
        sa, sb = self.slots()
        assert KB <= min(map(len, sa)) and KA <= min(map(len, sb))
        n0 = self.n_main()
        E = self.main_edges()
        for j in range(self.L):
            pa = rng.permutation(sa[j])[:KB]
            pb = rng.permutation(sb[j])[:KA]
            E += [(n0 + i, int(pa[i])) for i in range(KB)]
            E += [(n0 + KB + i, int(pb[i])) for i in range(KA)]
        if hub_edges is None:
            hub_edges = set()
            K = min(KA, KB)
            for _ in range(hubdeg):
                pb_ = rng.permutation(KB)[:K]
                pa_ = rng.permutation(KA)[:K]
                for x, y in zip(pb_, pa_):
                    hub_edges.add((int(x), int(y)))
            # degree check (a pair repeated across matchings just gives a lower degree)
        E += [(n0 + x, n0 + KB + y) for x, y in hub_edges]
        return n0 + KB + KA, E, sorted(hub_edges)


def run_apsp(path, d, D, T=4):
    out = subprocess.run([APSP, path, str(d), str(D), str(T)], capture_output=True, text=True).stdout.strip()
    return out


def run_far(path, D, srcfile=None):
    args = [FAR, path, str(D)] + ([srcfile] if srcfile else [])
    out = subprocess.run(args, capture_output=True, text=True).stdout.strip()
    m = re.search(r'far_ordered_pairs=(\d+)', out)
    return int(m.group(1)), out


# ---------------------------------------------------------------- sets

def g1_ok(H, S):
    """(G1): for every s in S, the elements of S at distance 2 from s all lie on one element adjacent to s"""
    S = np.array(sorted(set(int(x) for x in S)))
    D = H.dist[np.ix_(S, S)]
    for i, s in enumerate(S):
        nb = S[D[i] == 2]
        if len(nb) >= 2:
            c = {H.common(s, int(y)) for y in nb}
            if len(c) > 1:
                return False
    return True


def g1_greedy(H, cand, rng, start=()):
    """random greedy maximal (G1) set among the elements cand (all of one type), containing start (assumed (G1))"""
    seg = {}
    S = []
    def try_add(e):
        nb = [y for y in S if H.dist[e, y] == 2]
        cs = {H.common(e, y) for y in nb}
        if len(cs) > 1:
            return False
        if cs:
            c = cs.pop()
            if any(seg[y] is not None and seg[y] != c for y in nb):
                return False
            for y in nb:
                seg[y] = c
            seg[e] = c
        else:
            seg[e] = None
        S.append(e)
        return True
    for e in start:
        assert try_add(int(e))
    for e in rng.permutation(cand):
        e = int(e)
        if e in seg:
            continue
        try_add(e)
    return np.array(sorted(S))


def r1_greedy(H, cand, rng, pairs_only=False):
    """every element has at most one partner (element of the set at distance 2); pairs_only: exactly one partner"""
    S, partner = [], {}
    inS = np.zeros(2 * H.N, dtype=bool)
    if pairs_only:
        for e in rng.permutation(cand):
            e = int(e)
            if inS[e] or (H.dist[e, inS] <= 2).any():
                continue
            # a partner y collinear with e, y with no element of S at distance <= 2
            nbr2 = [int(y) for y in np.where(H.dist[e] == 2)[0] if inS[int(y)] == False and (H.dist[int(y)][int(cand[0])] % 2 == 0)]
            rng.shuffle(nbr2)
            for y in nbr2:
                if not (H.dist[y, inS] <= 2).any():
                    S += [e, y]; inS[e] = inS[y] = True; partner[e] = y; partner[y] = e
                    break
        return np.array(sorted(S))
    for e in rng.permutation(cand):
        e = int(e)
        nb = [y for y in S if H.dist[e, y] == 2]
        if len(nb) > 1 or (nb and nb[0] in partner):
            continue
        S.append(e); inS[e] = True
        if nb:
            partner[e] = nb[0]; partner[nb[0]] = e
    return np.array(sorted(S))


def opposite_greedy(H, cand, rng, start=()):
    """pairwise opposite (distance 6) elements"""
    S = list(int(x) for x in start)
    for e in rng.permutation(cand):
        e = int(e)
        if all(H.dist[e, y] == 6 for y in S):
            S.append(e)
    return np.array(S)


def gamma2(H, e):
    return np.where(H.dist[e] == 2)[0]


def local_duality_map(H, R, fR, rng):
    """a bijection M: points -> lines with M[R] = fR and M(Gamma_2(r)) = Gamma_2(M(r)) for r in R, under (M1)-(M3):
    R non-collinear, fR non-concurrent, every point collinear with <= 2 points of R, every line concurrent with <= 2
    lines of fR, and d(x, y) = 4 iff d(f(x), f(y)) = 4. Shared points mid(x, y) go to mid(f(x), f(y)); the rest of
    each Gamma_2(r) goes to the rest of Gamma_2(f(r)) at random; everything else at random."""
    N = H.N
    R, fR = [int(x) for x in R], [int(x) for x in fR]
    f = dict(zip(R, fR))
    for i, x in enumerate(R):
        for y in R[i + 1:]:
            assert H.dist[x, y] in (4, 6) and H.dist[f[x], f[y]] in (4, 6)
            assert (H.dist[x, y] == 4) == (H.dist[f[x], f[y]] == 4), 'distance-4 pattern not mirrored'
    M = -np.ones(2 * N, dtype=np.int64)
    usedP = np.zeros(2 * N, dtype=bool)
    usedL = np.zeros(2 * N, dtype=bool)
    for x in R:
        M[x] = f[x]; usedP[x] = True; usedL[f[x]] = True
    Ra = np.array(R); fRa = np.array(fR)
    for i, x in enumerate(R):
        for y in R[i + 1:]:
            if H.dist[x, y] == 4:
                m, l = H.mid(x, y), H.mid(f[x], f[y])
                assert (H.dist[m, Ra] == 2).sum() == 2 and (H.dist[l, fRa] == 2).sum() == 2, 'star of size >= 3'
                M[m] = l; usedP[m] = True; usedL[l] = True
    for x in R:
        P = [int(m) for m in gamma2(H, x) if not usedP[m]]
        Lq = [int(l) for l in gamma2(H, f[x]) if not usedL[l]]
        assert len(P) == len(Lq)
        Lq = list(rng.permutation(Lq))
        for m, l in zip(P, Lq):
            M[m] = l; usedP[m] = True; usedL[l] = True
    P = [p for p in range(N) if not usedP[p]]
    Lq = [l for l in range(N, 2 * N) if not usedL[l]]
    for m, l in zip(P, rng.permutation(Lq)):
        M[m] = l
    assert sorted(M[:N]) == list(range(N, 2 * N))
    for x in R:
        assert set(M[gamma2(H, x)]) == set(gamma2(H, f[x])), '(H3) fails'
    return M


def check_H123(H, M, R):
    """(H1) R has no two elements at distance 2, (H2) M(R) likewise, (H3) M(Gamma_2(r)) = Gamma_2(M(r))"""
    R = np.array(sorted(int(x) for x in R))
    h1 = not (H.dist[np.ix_(R, R)] == 2).any()
    MR = M[R]
    h2 = not (H.dist[np.ix_(MR, MR)] == 2).any()
    h3 = all(set(M[gamma2(H, int(x))]) == set(gamma2(H, int(M[x]))) for x in R)
    return h1, h2, h3


def mirrored_greedy(H, rng, n0, extra_tries, spread):
    """R0: n0 pairwise opposite points mapped to spread lines; then extra points x with lines L_x (any lines) such that
    (M1)-(M3) hold; prefers extra points at distance 4 from some point already in R."""
    N = H.N
    R = list(opposite_greedy(H, np.arange(N), rng)[:n0])
    fR = [int(l) for l in rng.permutation(spread)[:len(R)]]
    allL = np.arange(N, 2 * N)
    added = 0
    for x in rng.permutation(N)[:extra_tries]:
        x = int(x)
        Ra, fRa = np.array(R), np.array(fR)
        dx = H.dist[x, Ra]
        if (dx < 4).any():
            continue
        pat = dx == 4
        if not pat.any():
            continue
        # (M2) for the new midpoints
        ok = True
        for r in Ra[pat]:
            m = H.mid(x, int(r))
            if (H.dist[m, Ra] == 2).sum() != 1:
                ok = False; break
        if not ok:
            continue
        DL = H.dist[np.ix_(allL, fRa)]
        good = (DL >= 4).all(axis=1) & ((DL == 4) == pat[None, :]).all(axis=1)
        cands = allL[good]
        for l in rng.permutation(cands):
            l = int(l)
            ok = True
            for r in fRa[pat]:
                ml = H.mid(l, int(r))
                if (H.dist[ml, fRa] == 2).sum() != 1:
                    ok = False; break
            if ok:
                R.append(x); fR.append(l); added += 1
                break
    return np.array(R), np.array(fR), added
