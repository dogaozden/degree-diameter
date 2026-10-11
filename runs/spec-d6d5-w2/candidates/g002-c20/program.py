import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe classical fallbacks.
# ----------------------------------------------------------------------------

def _classical_candidates(d, D):
    """Known valid constructions for this (d, D). K_{d,d} is always valid for D >= 2."""
    out = [lib.haar_graph(d, range(d))]
    if D >= 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                try:
                    out.append(lib.projective_plane_incidence(q))
                except Exception:
                    pass
                break
        q = d - 2
        if q >= 3 and lib.is_prime_power(q):
            try:
                out.append(lib.araujo_lopez_graph(q))
            except Exception:
                pass
    return out


# ----------------------------------------------------------------------------
# New family: bi-Cayley graphs over non-abelian groups (one A-orbit, one B-orbit).
#
# Group G (elements coded 0..G-1, identity = 0), connection set S with 0 in S,
# |S| = d. Vertices A_g = g and B_y = G + y. Edge A_g -- B_{g s} for s in S.
# Left multiplication is an automorphism, so the graph has diameter <= D iff
# every vertex is within distance D of A_e and of B_e. WLOG 0 in S, since
# right-translating S gives an isomorphic graph.
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Random group of order G as (mul, inv): cyclic or Z_m x| Z_k. None if impossible."""
    opts = [k for k in range(1, G + 1) if G % k == 0 and G // k >= 2]
    if not opts:
        return None
    nonab = [k for k in opts if k >= 2]
    if nonab and rng.random() < 0.8:
        k = rng.choice(nonab)
    else:
        k = 1
    m = G // k
    if k == 1:
        r = 1
    else:
        cands = [r for r in range(1, m)
                 if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if not cands:
            return None
        r = rng.choice(cands)
    try:
        order, mul, inv = lib.semidirect_group(m, k, r)
    except ValueError:
        return None
    return order, mul, inv


def _reach(N, adj, src, D):
    """Number of vertices within distance D of src."""
    seen = bytearray(N)
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
    return cnt


class _Group:
    """Cached right-multiplication permutations for one group."""

    def __init__(self, G, mul, inv):
        self.G = G
        self.mul = mul
        self.inv = inv
        self.cache = {}

    def rp(self, s):
        p = self.cache.get(s)
        if p is None:
            mul = self.mul
            p = [mul(g, s) for g in range(self.G)]
            self.cache[s] = p
        return p


def _cost(grp, S, D):
    """Unreached (vertex, source) pairs from A_e and B_e. Zero iff valid."""
    G = grp.G
    N = 2 * G
    pS = [grp.rp(s) for s in S]
    pI = [grp.rp(grp.inv(s)) for s in S]
    adj = [None] * N
    for g in range(G):
        adj[g] = [G + p[g] for p in pS]
    for y in range(G):
        adj[G + y] = [p[y] for p in pI]
    return (N - _reach(N, adj, 0, D)) + (N - _reach(N, adj, G, D))


def _anneal_group(grp, d, D, rng, deadline, iters):
    """Simulated annealing over connection sets S with 0 in S. Returns S or None."""
    G = grp.G
    if G < d:
        return None
    S = [0] + rng.sample(range(1, G), d - 1)
    cost = _cost(grp, S, D)
    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.999)
        i = rng.randrange(1, d)
        x = rng.randrange(1, G)
        if x in S:
            continue
        S2 = S[:]
        S2[i] = x
        c2 = _cost(grp, S2, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            S, cost = S2, c2
    return S if cost == 0 else None


def _edges_of(grp, S):
    G = grp.G
    E = []
    for s in S:
        p = grp.rp(s)
        for g in range(G):
            E.append((g, G + p[g]))
    return E


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.80 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} (valid for D >= 2), upgraded by classical families.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    for n_c, e_c in _classical_candidates(d, D)[1:]:
        consider(n_c, e_c)

    # Calibration cases already at the Moore bound return immediately.
    if best_n >= lib.moore_bound(d, D):
        return best

    try:
        while time.monotonic() < deadline:
            # Climb a ladder: aim for group orders just above the current best half.
            lo = max(best_n // 2 + 1, d)
            hi = lo + max(2, lo // 10)
            G = rng.randint(lo, hi)

            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul, inv = g
            grp = _Group(order, mul, inv)

            slice_end = min(deadline, time.monotonic() + max(2.0, 0.06 * time_limit))
            S = _anneal_group(grp, d, D, rng, slice_end, 3000)
            if S is None:
                continue
            n_c = 2 * order
            e_c = _edges_of(grp, S)
            consider(n_c, e_c)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
