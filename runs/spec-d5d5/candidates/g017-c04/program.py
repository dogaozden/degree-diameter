import itertools
import math
import random
import time

import lib

ITERS = 600          # annealing steps per (group, base pattern) try
T_HOT = 1.5          # initial temperature (unreached-pair units)
T_COLD = 0.15        # final temperature
MAX_GROUPS = 12      # groups tried per (s, N) attempt
MAX_S = 4            # maximum number of vertices per side in the base graph


# ----------------------------------------------------------------------------
# Baseline families (used for small or record-matching cases).
# ----------------------------------------------------------------------------

def _best_pg(d):
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


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
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Multi-orbit bi-Cayley (group lift) search.
#
# Base graph: s vertices A_0..A_{s-1} and s vertices B_0..B_{s-1}.
# The base is d "layers"; layer l is a permutation P[l] of range(s) and a
# label G[l][i] in a group H of order N. The lift has vertices A_{i,x} and
# B_{j,y} (x, y in H) with edges A_{i,x} -- B_{P[l][i], x * G[l][i]}.
# Every A and B vertex has degree d. Left multiplication by H is an
# automorphism, so eccentricities from A_{i,e} and B_{j,e} decide the diameter.
# Vertex count is n = 2 * s * N.
#
# This generalises the single-orbit (s = 1) bi-Cayley search to several
# orbits per side, which reaches vertex counts the single orbit cannot.
# ----------------------------------------------------------------------------

def _groups(N):
    """Semidirect parameters (m, k, r) giving groups Z_m x|_r Z_k of order N."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _tables(N, m, k, r):
    _, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(N)] for x in range(N)]
    invs = [inv(g) for g in range(N)]
    return T, invs


class _Lift:
    def __init__(self, s, N, d, D, T, invs, P):
        self.s, self.N, self.d, self.D = s, N, d, D
        self.T, self.invs, self.P = T, invs, P
        self.Pinv = []
        for perm in P:
            inv = [0] * s
            for i, j in enumerate(perm):
                inv[j] = i
            self.Pinv.append(inv)
        self.n = 2 * s * N
        self.sources = [i * N for i in range(s)] + [s * N + j * N for j in range(s)]

    def adj(self, G):
        s, N, d = self.s, self.N, self.d
        T, invs, P, Pinv = self.T, self.invs, self.P, self.Pinv
        out = [None] * self.n
        for i in range(s):
            for x in range(N):
                row = T[x]
                out[i * N + x] = [s * N + P[l][i] * N + row[G[l][i]] for l in range(d)]
        for j in range(s):
            for y in range(N):
                row = T[y]
                out[s * N + j * N + y] = [
                    Pinv[l][j] * N + row[invs[G[l][Pinv[l][j]]]] for l in range(d)
                ]
        return out

    def cost(self, G):
        """Number of (source, vertex) pairs not within distance D, over all orbit sources."""
        adj = self.adj(G)
        n, D = self.n, self.D
        total = 0
        for src in self.sources:
            seen = bytearray(n)
            seen[src] = 1
            frontier = [src]
            cnt = 1
            for _ in range(D):
                nxt = []
                for u in frontier:
                    for v in adj[u]:
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                if not nxt:
                    break
                cnt += len(nxt)
                frontier = nxt
            total += n - cnt
        return total

    def ok(self, G, l, i, g):
        """Setting G[l][i] = g keeps the darts out of row i distinct (no multi-edges)."""
        P, d = self.P, self.d
        pl = P[l][i]
        for m in range(d):
            if m != l and P[m][i] == pl and G[m][i] == g:
                return False
        return True

    def init(self, rng):
        s, N, d = self.s, self.N, self.d
        G = [[-1] * s for _ in range(d)]
        for i in range(s):
            for l in range(d):
                for _ in range(100):
                    g = rng.randrange(N)
                    if self.ok(G, l, i, g):
                        G[l][i] = g
                        break
                else:
                    return None
        return G


def _anneal(lift, rng, deadline):
    G = lift.init(rng)
    if G is None:
        return None
    s, N, d = lift.s, lift.N, lift.d
    cur = lift.cost(G)
    for it in range(ITERS):
        if cur == 0:
            return G
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / ITERS)
        l = rng.randrange(d)
        i = rng.randrange(s)
        g = rng.randrange(N)
        old = G[l][i]
        if g == old or not lift.ok(G, l, i, g):
            continue
        G[l][i] = g
        v = lift.cost(G)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            G[l][i] = old
    return G if cur == 0 else None


def _attempt(s, N, d, D, rng, deadline):
    """Try groups of order N with s orbits per side; return (lift, G) on success."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        T, invs = _tables(N, m, k, r)
        P = []
        for _ in range(d):
            perm = list(range(s))
            rng.shuffle(perm)
            P.append(perm)
        lift = _Lift(s, N, d, D, T, invs, P)
        G = _anneal(lift, rng, deadline)
        if G is not None:
            return lift, G
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = (1, [])

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Record-matching case: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best

    if D >= 2:
        consider(*lib.haar_graph(d, range(d)))
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if d < 2 or D < 2:
        return best

    # Candidate (n, s, N) with n = 2*s*N in a window just below the cap.
    moore = lib._moore_bound(d, D)
    n_cap = min(moore, moore // 2 + 12)
    lo = int(0.85 * n_cap)
    cands = []
    for s in range(1, MAX_S + 1):
        for N in range(d, n_cap // (2 * s) + 1):
            n = 2 * s * N
            if lo < n <= n_cap:
                cands.append((n, s, N))
    cands.sort()

    budget = 0.5
    while time.monotonic() < deadline:
        if not any(n > best[0] for n, _, _ in cands):
            break
        for n, s, N in cands:
            if n <= best[0]:
                continue
            now = time.monotonic()
            if now >= deadline:
                break
            att = min(deadline, now + budget)
            res = _attempt(s, N, d, D, rng, att)
            if res is None:
                continue
            lift, G = res
            adj = lift.adj(G)
            edges = [(a, b) for a in range(lift.n // 2) for b in adj[a]]
            consider(lift.n, edges)
        budget *= 2

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
