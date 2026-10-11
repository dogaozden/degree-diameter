import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe baseline families (exact constructions, kept from the parent).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# NEW (bold) family: Haar graphs H(G, S) over metacyclic groups G = Z_m x| Z_k.
#
# H(G, S) has vertices A_g and B_h (g, h in G), with A_g ~ B_{g s} for s in S.
# It is d-regular (|S| = d) and bipartite. Left multiplication is an automorphism,
# so the diameter test only needs BFS from A_1 and B_1. The search is simulated
# annealing over the connection set S, and the group order is found by binary
# search. Each success gives a Haar graph of order 2|G| > parent's order.
# ----------------------------------------------------------------------------

def _metacyclic_groups(G):
    """All (m, k, r) with m*k = G, m >= 2, gcd(r, m) = 1, r^k = 1 mod m (semidirect Z_m x| Z_k)."""
    out = []
    for k in range(1, G + 1):
        if G % k:
            continue
        m = G // k
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) != 1 or pow(r, k, m) != 1 % m:
                continue
            out.append((m, k, r))
    return out


class _Grp:
    """Vectorised semidirect product Z_m x| Z_k; element (a, b) is coded as a*k + b, identity is 0."""

    def __init__(self, m, k, r):
        self.m, self.k = m, k
        self.G = m * k
        self.pw = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
        self.X = np.arange(self.G, dtype=np.int64)
        self.a = self.X // k
        self.b = self.X % k

    def mul_right(self, s):
        """Array t with t[x] = x * s for every x."""
        c, e = s // self.k, s % self.k
        return ((self.a + self.pw[self.b] * c) % self.m) * self.k + (self.b + e) % self.k

    def inv(self, s):
        """Index of the inverse of s."""
        c, e = s // self.k, s % self.k
        left = ((c + self.pw[e] * self.a) % self.m) * self.k + (e + self.b) % self.k
        return int(np.nonzero(left == 0)[0][0])


def _haar_restart(d, D, grp, rng, iters, deadline):
    """Annealing over a set S of d distinct group elements. Returns S with diameter <= D, or None."""
    G = grp.G
    N2 = 2 * G
    S = rng.sample(range(G), d)
    Sinv = [grp.inv(s) for s in S]
    Rf = [grp.mul_right(s) for s in S]      # A_g -> B_{g s}
    Ri = [grp.mul_right(t) for t in Sinv]   # B_h -> A_{h s^-1}

    def reach(side0):
        """Number of vertices within distance D of A_1 (side0 = 0) or of B_1 (side0 = 1)."""
        vis = [np.zeros(G, dtype=bool), np.zeros(G, dtype=bool)]
        vis[side0][0] = True
        front = np.zeros(1, dtype=np.int64)
        side = side0
        total = 1
        for _ in range(D):
            M = Rf if side == 0 else Ri
            cand = np.unique(np.concatenate([mp[front] for mp in M]))
            other = 1 - side
            new = cand[~vis[other][cand]]
            if new.size == 0:
                break
            vis[other][new] = True
            total += int(new.size)
            front = new
            side = other
        return total

    def cost():
        return (N2 - reach(0)) + (N2 - reach(1))

    cur = cost()
    for t in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(d)
        x = rng.randrange(G)
        if x in S:
            continue
        old = (S[i], Sinv[i], Rf[i], Ri[i])
        S[i] = x
        Sinv[i] = grp.inv(x)
        Rf[i] = grp.mul_right(x)
        Ri[i] = grp.mul_right(Sinv[i])
        c2 = cost()
        temp = 1.5 * (1.0 - t / iters) + 0.05
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / temp):
            cur = c2
        else:
            S[i], Sinv[i], Rf[i], Ri[i] = old
    if cur == 0:
        return list(S)
    return None


def _haar_attempt(d, D, G, rng, deadline):
    """Try to find a valid Haar graph over a group of order G before the deadline. Returns (grp, S) or None."""
    groups = _metacyclic_groups(G)
    if not groups:
        return None
    nonab = [g for g in groups if g[1] >= 2 and g[2] != 1]
    while time.monotonic() < deadline:
        pool = nonab if (nonab and rng.random() < 0.8) else groups
        m, k, r = rng.choice(pool)
        grp = _Grp(m, k, r)
        S = _haar_restart(d, D, grp, rng, 3000, deadline)
        if S is not None:
            return grp, S
    return None


def _haar_graph_from(grp, S):
    """Return (n, edges) of H(G, S): A_g = g, B_h = G + h, A_g ~ B_{g s}."""
    G = grp.G
    E = []
    for s in S:
        R = grp.mul_right(s).tolist()
        for g in range(G):
            E.append((g, G + R[g]))
    return 2 * G, E


# ----------------------------------------------------------------------------
# Parent's bi-Cayley lift search over semidirect products (kept as a secondary family).
# ----------------------------------------------------------------------------

_PENALTY = 1000


def _sample_group(target, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order near target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, target // k2)
        if k2 == 1:
            r = 1
        else:
            r = None
            for _ in range(60):
                c = rng.randrange(2, m) if m > 2 else 1
                if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                    r = c
                    break
            if r is None:
                continue
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _search(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over the voltages of a base with k vertices per side."""
    N = 2 * k * G
    ar = np.arange(G, dtype=np.int64)
    layers = [rng.sample(range(k), k) for _ in range(d)]
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    nb = np.zeros((N, d), dtype=np.int64)

    def assign(l, i, s):
        j = layers[l][i]
        pm = np.fromiter((mul(g, s) for g in range(G)), dtype=np.int64, count=G)
        nb[i * G:(i + 1) * G, l] = (k + j) * G + pm
        inv = np.empty(G, dtype=np.int64)
        inv[pm] = ar
        nb[(k + j) * G:(k + j + 1) * G, l] = i * G + inv

    for l in range(d):
        for i in range(k):
            assign(l, i, S[l][i])

    base = np.zeros(N, dtype=np.int64)
    for r in range(k):
        base[r * G] = 1 << r
    for j in range(k):
        base[(k + j) * G] = 1 << (k + j)
    nreps = 2 * k

    def dup_count():
        seen = set()
        dup = 0
        for l in range(d):
            for i in range(k):
                key = (i, layers[l][i], S[l][i])
                if key in seen:
                    dup += 1
                else:
                    seen.add(key)
        return dup

    def cost():
        reach = base
        for _ in range(D):
            reach = reach | np.bitwise_or.reduce(reach[nb], axis=1)
        reached = 0
        for r in range(nreps):
            reached += int(np.count_nonzero(reach & (1 << r)))
        return N * nreps - reached + _PENALTY * dup_count()

    cur = cost()
    for t in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        l = rng.randrange(d)
        i = rng.randrange(k)
        old_s = S[l][i]
        new_s = rng.randrange(G)
        assign(l, i, new_s)
        S[l][i] = new_s
        c2 = cost()
        temp = 2.0 * (1.0 - t / iters) + 0.05
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / temp):
            cur = c2
        else:
            assign(l, i, old_s)
            S[l][i] = old_s

    if cur != 0:
        return None
    E = set()
    for x in range(N):
        for y in nb[x].tolist():
            if x != y:
                E.add((x, y) if x < y else (y, x))
    return N, sorted(E)


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.9 * time_limit, time_limit - 4.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n <= best_n:
            return False
        if not lib.is_valid(n, e, d, D):
            return False
        best = (n, e)
        best_n = n
        return True

    # Exact constructions: return immediately (calibration-style cases).
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # NEW family: binary search on the group order for Haar graphs H(G, S).
    # Only orders giving 2|G| > best_n are useful, so search G in (best_n/2, ~1.3 * best_n/2].
    if D >= 3 and time.monotonic() < deadline:
        moore = lib._moore_bound(d, D)
        L = max(best_n // 2 + 1, d)
        H = min(moore // 2, (best_n // 2) * 13 // 10 + 1)
        new_deadline = start + 0.7 * budget
        while L <= H and time.monotonic() < new_deadline:
            mid = (L + H) // 2
            steps = max(1, math.ceil(math.log2(H - L + 2)))
            now = time.monotonic()
            att_deadline = min(new_deadline, now + max(0.5, (new_deadline - now) / steps))
            found = _haar_attempt(d, D, mid, rng, att_deadline)
            if found is not None:
                grp, S = found
                n, e = _haar_graph_from(grp, S)
                if consider(n, e):
                    L = mid + 1
                else:
                    H = mid - 1
            else:
                H = mid - 1

    # Secondary family: parent's bi-Cayley lift search, with the remaining time.
    while time.monotonic() < deadline:
        k = rng.choice([1, 2, 2, 3, 4])
        base = best_n // (2 * k)
        target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
        g = _sample_group(target, rng)
        if g is None:
            continue
        order, mul = g
        res = _search(d, D, k, order, mul, rng, deadline, 6000)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
