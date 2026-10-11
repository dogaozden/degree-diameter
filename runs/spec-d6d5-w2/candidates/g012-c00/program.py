import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bi-Cayley graphs over small non-abelian groups.
#
# Group G of order N with a generating set S of d distinct elements gives a
# bipartite graph on A = G x {0} and B = G x {1}, with A_g adjacent to B_{g s}
# for each s in S. Left multiplication is an automorphism that is transitive on
# each side, so the diameter is at most D exactly when BFS from A_e and from B_e
# reaches every vertex within D steps. The search anneals over S directly.
# ----------------------------------------------------------------------------

def _units_with_order(m, k):
    """Units r mod m with r^k = 1 (mod m), so Z_m x| Z_k is a valid semidirect product."""
    return [r for r in range(1, m)
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]


def _group_candidates(G):
    """(k, m, r) triples describing semidirect products Z_m x| Z_k of order G."""
    res = []
    for k in range(1, 13):
        if G % k:
            continue
        m = G // k
        if m < 2:
            continue
        if k == 1:
            res.append((1, m, 1))
        else:
            for r in _units_with_order(m, k):
                res.append((k, m, r))
    return res


def _reach(G, fw, bw, src, D):
    """Number of vertices NOT within distance D of src in the bi-Cayley graph (0 = all reached)."""
    seen = bytearray(2 * G)
    seen[src] = 1
    frontier = [src]
    cnt = 1
    for _ in range(D):
        nxt = []
        for u in frontier:
            if u < G:
                for p in fw:
                    v = G + p[u]
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            else:
                h = u - G
                for q in bw:
                    v = q[h]
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
        cnt += len(nxt)
        frontier = nxt
        if not frontier:
            break
    return 2 * G - cnt


def _anneal(G, mul, inv, d, D, rng, deadline, iters):
    """Search a generating set S (|S| = d) with zero cost; returns S or None."""
    cache = {}

    def perms(s):
        if s not in cache:
            cache[s] = ([mul(g, s) for g in range(G)],
                        [mul(h, inv(s)) for h in range(G)])
        return cache[s]

    def cost_of(S):
        pl = [perms(s) for s in S]
        fw = [p[0] for p in pl]
        bw = [p[1] for p in pl]
        return _reach(G, fw, bw, 0, D) + _reach(G, fw, bw, G, D)

    if d > G:
        return None
    S = rng.sample(range(G), d)
    c = cost_of(S)
    T = 2.0
    for _ in range(iters):
        if c == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(d)
        x = rng.randrange(G)
        if x in S:
            continue
        T2 = S[:]
        T2[i] = x
        c2 = cost_of(T2)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / max(T, 1e-3)):
            S, c = T2, c2
        T = max(0.1, T * 0.999)
    return S if c == 0 else None


def _bicayley_edges(G, mul, S):
    """Edge list of the bi-Cayley graph: A_g -- B_{g s} for s in S."""
    E = []
    for s in S:
        for g in range(G):
            E.append((g, G + mul(g, s)))
    return 2 * G, E


# ----------------------------------------------------------------------------
# Known constructions used as secondary candidates.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez graph for d = q + 2 with q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is optimal for D = 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    if D == 2 or d == 1:
        return best_n, best_e

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    # Main search: bi-Cayley graphs over semidirect products, one random order
    # per round, with the target order always just above the current best / 2.
    while time.monotonic() < deadline:
        lo = best_n // 2 + 1
        span = max(6, lo // 25)
        G = rng.randint(lo, lo + span)
        cands = _group_candidates(G)
        if not cands:
            continue
        k, m, r = rng.choice(cands)
        try:
            order, mul, inv = lib.semidirect_group(m, k, r)
        except ValueError:
            continue
        S = _anneal(order, mul, inv, d, D, rng, deadline, 2500)
        if S is None:
            continue
        n, e = _bicayley_edges(order, mul, S)
        consider(n, e)

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, best_e
