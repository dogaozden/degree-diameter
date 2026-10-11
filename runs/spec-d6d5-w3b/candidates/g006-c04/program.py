import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Strategy: bipartite Cayley-type graphs ("Haar lifts") over finite groups.
# Vertices A_g and B_g for g in G, with A_g adjacent to B_{g s} for s in S, |S| = d.
# Left multiplication is an automorphism, so the diameter is decided by BFS from
# A_e and B_e alone. The groups are semidirect products Z_m x| Z_k, which include
# non-abelian groups such as AGL(1,19) of order 342. Connection sets are found by
# simulated annealing, and the order is grown outward from a PG(2,q) fallback.
# ----------------------------------------------------------------------------


class _Group:
    """Z_m x| Z_k of order G, with cached right-multiplication permutations."""

    def __init__(self, m, k, r):
        self.order, self._mul, self._inv = lib.semidirect_group(m, k, r)
        self._cache = {}

    def perms(self, s):
        """(R, Ri) with R[g] = g*s and Ri[g] = g*s^-1."""
        p = self._cache.get(s)
        if p is None:
            G = self.order
            mul = self._mul
            si = self._inv(s)
            p = ([mul(g, s) for g in range(G)], [mul(g, si) for g in range(G)])
            self._cache[s] = p
        return p


def _group_candidates(G):
    """All (m, k, r) with m >= 2 and m * k = G giving a semidirect product Z_m x| Z_k."""
    out = []
    for k in range(1, G + 1):
        if G % k:
            continue
        m = G // k
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _cost(G, D, pairs):
    """Vertices not reached within D from A_e and from B_e. Zero iff the lift has diameter <= D."""
    N = 2 * G
    total = 0
    for src in (0, G):
        seen = bytearray(N)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < G:
                    for R, _unused in pairs:
                        v = G + R[u]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    h = u - G
                    for _unused, Ri in pairs:
                        v = Ri[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            if not nxt:
                break
            cnt += len(nxt)
            frontier = nxt
        total += N - cnt
    return total


def _search(grp, d, D, deadline, rng):
    """Anneal a connection set S (0 in S, |S| = d) until the lift has diameter <= D."""
    G = grp.order
    T = 0.6
    while time.monotonic() < deadline:
        S = [0] + rng.sample(range(1, G), d - 1)
        perms = [grp.perms(s) for s in S]
        cur = _cost(G, D, perms)
        best_c = cur
        stall = 0
        while cur > 0 and stall < 300:
            if time.monotonic() >= deadline:
                return None
            i = rng.randrange(1, d)
            c = rng.randrange(1, G)
            if c in S:
                stall += 1
                continue
            old_s, old_p = S[i], perms[i]
            S[i] = c
            perms[i] = grp.perms(c)
            c2 = _cost(G, D, perms)
            if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
                cur = c2
                if cur < best_c:
                    best_c = cur
                    stall = 0
                else:
                    stall += 1
            else:
                S[i], perms[i] = old_s, old_p
                stall += 1
        if cur == 0:
            return S
    return None


def _emit(grp, S):
    """Edge list of the bipartite Cayley graph: A_g = g, B_h = G + h, A_g ~ B_{g s}."""
    G = grp.order
    edges = []
    for s in S:
        R = grp.perms(s)[0]
        for g in range(G):
            edges.append((g, G + R[g]))
    return 2 * G, edges


def _try_order(G, d, D, deadline, rng):
    """Try several groups of order G until one admits a valid connection set."""
    if G < d:
        return None
    cands = _group_candidates(G)
    if not cands:
        return None
    rng.shuffle(cands)
    i = 0
    while time.monotonic() < deadline:
        m, k, r = cands[i % len(cands)]
        i += 1
        now = time.monotonic()
        sub = min(deadline, now + max(0.3, (deadline - now) / 3.0))
        grp = _Group(m, k, r)
        S = _search(grp, d, D, sub, rng)
        if S is not None:
            return _emit(grp, S)
    return None


def _pg_fallback(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, min(0.85 * time_limit, time_limit - 5.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D  # even cycle C_{2D} has diameter D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = (2 * d, [(i, d + j) for i in range(d) for j in range(d)])
    if D == 2:
        return best

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    pg = _pg_fallback(d)
    if pg is not None:
        consider(pg[0], pg[1])

    # Grow the Cayley order G (graph has 2G vertices) above the current best.
    cap = lib.moore_bound(d, D) // 2
    lo = best[0] // 2
    step = max(1, lo // 8)
    fails = 0
    total = max(1e-6, deadline - start)
    while time.monotonic() < deadline and fails < 8:
        G = min(lo + step, cap)
        if G <= lo:
            break
        now = time.monotonic()
        slice_end = min(deadline, now + max(0.5, 0.06 * total))
        res = _try_order(G, d, D, slice_end, rng)
        if res is not None and lib.is_valid(res[0], res[1], d, D):
            best = res
            lo = G
            step *= 2
            fails = 0
        else:
            if step == 1:
                fails += 1
            else:
                step //= 2

    if not lib.is_valid(best[0], best[1], d, D):
        best = (2 * d, [(i, d + j) for i in range(d) for j in range(d)])
    return best
