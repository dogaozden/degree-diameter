import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Projective-plane arc construction (D = 3 baseline, parent's construction)
# ----------------------------------------------------------------------------

def _pg_incidence(q):
    """Return (m, edges, point_lines, line_points) for PG(2, q); points 0..m-1, lines indexed 0..m-1."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    return m, edges, point_lines, line_points


def _loads_ok(S, s, m, point_lines, line_points):
    """True if every line holds <= s points of S and every point lies on <= s lines indexed by S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
    """Randomized greedy set S with all loads <= s; returns the largest found."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        cl = [0] * m
        cp = [0] * m
        S = []
        for P in order:
            if all(cl[L] < s for L in point_lines[P]) and all(cp[Q] < s for Q in line_points[P]):
                S.append(P)
                for L in point_lines[P]:
                    cl[L] += 1
                for Q in line_points[P]:
                    cp[Q] += 1
        if len(S) > len(best):
            best = S
    return best


def _conic_set(q, index):
    """Conic (plus nucleus for even q): an arc with no three collinear."""
    F = lib.GF(q)
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """Incidence graph of PG(2,q) plus, per element of S, an A-vertex and a B-vertex."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        a = 2 * m + t
        for L in point_lines[P]:
            E.append((a, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_candidates(d, deadline, rng):
    """For each prime power q with q + 1 <= d, build the best arc-extended PG(2,q) graph."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points = _pg_incidence(q)
        pts = lib.projective_points(q)
        index = {p: i for i, p in enumerate(pts)}
        cands = [[]]
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 60, deadline))
        if s >= 2:
            cs = _conic_set(q, index)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len)
        if not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# Cayley-type bipartite graphs over groups (D = 3)
#
# For a group G of order N and a k-set S, the graph with parts A = G, B = G,
# a_g ~ b_{g s} (s in S) is k-regular and bipartite. A-A pairs are at distance
# <= 2 iff every x != e in G is s t^{-1} for some s != t in S. Mixed pairs are
# then within distance 3 automatically. So we need a "difference cover" of G
# by k elements, with N <= k(k-1)+1. Cyclic and semidirect groups Z_m x| Z_kk
# are searched by simulated annealing that minimises the number of uncovered
# elements. A success with N >= best_n/2 + 1 beats the current record.
# ----------------------------------------------------------------------------

def _cyclic_table(N):
    X = np.arange(N)
    MT = ((X[:, None] + X[None, :]) % N).tolist()
    INV = ((-X) % N).tolist()
    return MT, INV


def _semidirect_table(m, kk, r):
    """Z_m x|_r Z_kk, element (a, b) coded as a*kk + b, product (a,b)(c,d) = (a + r^b c, b + d)."""
    N = m * kk
    X = np.arange(N)
    A = X // kk
    B = X % kk
    pw = np.array([pow(r, b, m) for b in range(kk)], dtype=np.int64)
    MA = (A[:, None] + pw[B][:, None] * A[None, :]) % m
    MB = (B[:, None] + B[None, :]) % kk
    MT = (MA * kk + MB).tolist()
    nb = (-B) % kk
    INV = (((-pw[nb] * A) % m) * kk + nb).tolist()
    return MT, INV


def _semidirect_params(N):
    """All (m, kk, r) with m * kk = N, m, kk >= 2 and r^kk = 1 mod m, gcd(r, m) = 1, nontrivial."""
    out = []
    for kk in range(2, N + 1):
        if N % kk:
            continue
        m = N // kk
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) != 1 or pow(r, kk, m) != 1 % m:
                continue
            if r == 1 and math.gcd(m, kk) == 1:
                continue  # that is just the cyclic group
            out.append((m, kk, r))
    return out


class _Anneal:
    """Annealing state: a k-subset S of a group of order N, minimising uncovered elements."""

    def __init__(self, N, k, MT, INV, rng):
        self.N = N
        self.k = k
        self.MT = MT
        self.INV = INV
        self.rng = rng
        self.S = rng.sample(range(N), k)
        self.inS = [False] * N
        for s in self.S:
            self.inS[s] = True
        self.cnt = [0] * N
        for s in self.S:
            for t in self.S:
                if s != t:
                    self.cnt[MT[s][INV[t]]] += 1
        self.unc = sum(1 for g in range(1, N) if self.cnt[g] == 0)
        self.T = 0.6
        self.best = self.unc
        self.stall = 0

    def step(self, moves):
        """Run up to `moves` annealing moves. Returns True once every non-identity element is covered."""
        MT, INV, cnt, S, inS = self.MT, self.INV, self.cnt, self.S, self.inS
        k, N, rng = self.k, self.N, self.rng
        for _ in range(moves):
            if self.unc == 0:
                return True
            i = rng.randrange(k)
            y = rng.randrange(N)
            if inS[y]:
                continue
            x = S[i]
            Mx, ix = MT[x], INV[x]
            My, iy = MT[y], INV[y]
            delta = 0
            # Remove x's pairs.
            for j in range(k):
                if j == i:
                    continue
                s = S[j]
                a = Mx[INV[s]]
                cnt[a] -= 1
                if cnt[a] == 0:
                    delta += 1
                b = MT[s][ix]
                cnt[b] -= 1
                if cnt[b] == 0:
                    delta += 1
            # Add y's pairs.
            for j in range(k):
                if j == i:
                    continue
                s = S[j]
                a = My[INV[s]]
                if cnt[a] == 0:
                    delta -= 1
                cnt[a] += 1
                b = MT[s][iy]
                if cnt[b] == 0:
                    delta -= 1
                cnt[b] += 1
            if delta <= 0 or rng.random() < math.exp(-delta / self.T):
                S[i] = y
                inS[x] = False
                inS[y] = True
                self.unc += delta
            else:
                # Revert the addition, then the removal.
                for j in range(k):
                    if j == i:
                        continue
                    s = S[j]
                    cnt[My[INV[s]]] -= 1
                    cnt[MT[s][iy]] -= 1
                for j in range(k):
                    if j == i:
                        continue
                    s = S[j]
                    cnt[Mx[INV[s]]] += 1
                    cnt[MT[s][ix]] += 1
            if self.unc < self.best:
                self.best = self.unc
                self.stall = 0
            else:
                self.stall += 1
                if self.stall > 40000:  # reheat when stuck
                    self.T = 0.6
                    self.best = self.unc
                    self.stall = 0
        self.T = max(0.2, self.T * 0.995)
        return self.unc == 0


def _search_cover(k, best_n, rng, deadline, consider):
    """Look for a difference cover of size k in groups of order N > best_n / 2, largest N first."""
    M = k * (k - 1) + 1
    lo = best_n // 2 + 1
    hi = min(M, lo + 9)
    if lo > hi or k < 2:
        return
    specs = [(N, None) for N in range(lo, hi + 1)]
    extras = []
    for N in range(lo, hi + 1):
        for m, kk, r in _semidirect_params(N):
            extras.append((N, (m, kk, r)))
    rng.shuffle(extras)
    cap = 30
    specs += extras[:max(0, cap - len(specs))]

    states = []
    for N, params in specs:
        if params is None:
            MT, INV = _cyclic_table(N)
        else:
            m, kk, r = params
            MT, INV = _semidirect_table(m, kk, r)
        states.append(_Anneal(N, k, MT, INV, rng))

    CHUNK = 1500
    results = []
    active = sorted(states, key=lambda s: -s.N)
    while active and time.monotonic() < deadline:
        solved = None
        for st in list(active):
            if time.monotonic() >= deadline:
                break
            if st.step(CHUNK):
                solved = st
                break
        if solved is not None:
            results.append(solved)
            # Only larger groups can improve on this solution now.
            active = [s for s in active if s.N > solved.N]

    if not results:
        return
    st = max(results, key=lambda s: s.N)
    N, MT, S = st.N, st.MT, st.S
    E = []
    for g in range(N):
        row = MT[g]
        for s in S:
            E.append((g, N + row[s]))
    consider(2 * N, E)


# ----------------------------------------------------------------------------
# Generalized quadrangle baseline (D = 4)
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Entry point
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = min(0.8 * float(time_limit), 48.0)
    deadline = start + budget
    rng = random.Random(seed * 1000003 + 17 * d + D)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best_n, best_E = lib.haar_graph(d, range(d))

    def consider(n, E):
        nonlocal best_n, best_E
        if n > best_n and lib.is_valid(n, E, d, D):
            best_n, best_E = n, list(E)

    if D == 3:
        # Baseline: arc-extended projective plane (order 394 at d = 16).
        if d >= 2:
            cands = _arc_candidates(d, start + 0.25 * budget, random.Random(seed * 7919 + d))
            cands.sort(key=lambda t: -t[0])
            for n_c, E_c in cands[:1]:
                consider(n_c, E_c)
        # Main search: Cayley-type diameter-3 graphs beating the current order.
        if d >= 3:
            _search_cover(d, best_n, rng, deadline, consider)

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, list(best_E)
