import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe baselines: projective plane incidence graph and Araujo-Pardo-Lopez graph.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return q, lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez record graph for d = q + 2 with q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# New family: k = 1 bi-Cayley (Haar-type) graphs over metacyclic groups
# G = Z_m x| Z_k. Vertices A_g and B_h (g, h in G), with A_g adjacent to B_{g s}
# for every s in S, |S| = d. Left multiplication by G acts transitively on each
# side and preserves edges, so the diameter check reduces to two BFS runs,
# from A_1 and from B_1. This makes each candidate check very cheap.
# ----------------------------------------------------------------------------

class _Group:
    """Group with a lazily cached right-multiplication table R_s[g] = g * s."""

    def __init__(self, order, mul, inv):
        self.G = order
        self.mul = mul
        self.inv = inv
        self.cache = {}

    def right(self, s):
        r = self.cache.get(s)
        if r is None:
            mul = self.mul
            r = [mul(g, s) for g in range(self.G)]
            self.cache[s] = r
        return r


def _metacyclic_groups(G, rng, count):
    """Return up to `count` random groups Z_m x| Z_k of order G (identity is code 0)."""
    cands = []
    for k in range(1, G + 1):
        if G % k:
            continue
        m = G // k
        if m < 2:
            continue
        if k == 1:
            cands.append((m, 1, 1))
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                cands.append((m, k, r))
    rng.shuffle(cands)
    out = []
    for m, k, r in cands:
        if len(out) >= count:
            break
        try:
            order, mul, inv = lib.semidirect_group(m, k, r)
        except ValueError:
            continue
        out.append(_Group(order, mul, inv))
    return out


def _bicayley_ok(G, S, grp, D):
    """True iff the bi-Cayley graph with connection set S (containing identity 0) has diameter <= D.

    Only BFS from A_identity (index 0) and B_identity (index G) is needed, by transitivity.
    """
    Rs = [grp.right(s) for s in S]
    Ris = [grp.right(grp.inv(s)) for s in S]
    N = 2 * G
    for src in (0, G):
        seen = bytearray(N)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for x in frontier:
                if x < G:
                    for R in Rs:
                        y = G + R[x]
                        if not seen[y]:
                            seen[y] = 1
                            nxt.append(y)
                else:
                    h = x - G
                    for Ri in Ris:
                        y = Ri[h]
                        if not seen[y]:
                            seen[y] = 1
                            nxt.append(y)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        if count != N:
            return False
    return True


def _edges_from(G, S, grp):
    """Full edge list of the bi-Cayley graph (A_g = g, B_h = G + h)."""
    Rs = [grp.right(s) for s in S]
    E = []
    for g in range(G):
        for R in Rs:
            E.append((g, G + R[g]))
    return 2 * G, E


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.0, min(0.8 * time_limit, time_limit - 6.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    skip = False
    try:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[1][0], pg[1][1])
            if D == 3 and pg[0] == d - 1:
                skip = True  # PG(2, d-1) meets the Moore-type bound here
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])
    except Exception:
        pass

    # Bi-Cayley search: grow the order G of the group; each success gives 2G vertices.
    cap = lib.moore_bound(d, D) // 2
    Gbest = best_n // 2
    trials = 400
    try:
        while not skip and time.monotonic() < deadline and Gbest + 1 <= cap:
            span = max(3, Gbest // 25)
            G = Gbest + 1 + rng.randrange(span)
            if G > cap:
                G = Gbest + 1
            G = max(G, d)
            if G > cap:
                break
            found = None
            for grp in _metacyclic_groups(G, rng, 4):
                if time.monotonic() >= deadline:
                    break
                for _ in range(trials):
                    if time.monotonic() >= deadline:
                        break
                    S = [0] + rng.sample(range(1, G), d - 1)
                    if _bicayley_ok(G, S, grp, D):
                        found = _edges_from(G, S, grp)
                        break
                if found is not None:
                    break
            if found is not None:
                consider(found[0], found[1])
                Gbest = max(Gbest, best_n // 2)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
