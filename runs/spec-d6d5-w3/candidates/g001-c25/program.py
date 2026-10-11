import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe baselines: projective plane incidence graphs and the Araujo-Pardo-Lopez
# record graph for D = 3.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
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
# New family: bi-Cayley (group Haar) graphs over non-abelian groups.
#
# For a finite group G and a connection set S of size d, the Haar graph
# H(G, S) has parts A = {A_g} and B = {B_h}, with A_g ~ B_{g s} for s in S.
# It is d-regular, bipartite, and has 2|G| vertices. Left translations
# are automorphisms, so the diameter is at most D iff every vertex is within
# distance D of A_e and of B_e. Two BFS runs on 2|G| vertices decide validity.
#
# Unlike voltage-lift annealing, this searches over the group itself
# (semidirect products Z_m x| Z_k) and the connection set S, with a
# hill-climb on the number of unreached vertices.
# ----------------------------------------------------------------------------

_group_cache = {}


class _Grp:
    """A finite group given by its multiplication, with lazily cached right-multiplication columns."""

    def __init__(self, G, mul, inv):
        self.G = G
        self.mul = mul
        self.inv = [inv(x) for x in range(G)]
        self.cols = {}

    def col(self, s):
        """Column c with c[g] = g * s."""
        c = self.cols.get(s)
        if c is None:
            mul = self.mul
            c = [mul(g, s) for g in range(self.G)]
            self.cols[s] = c
        return c


def _get_grp(key):
    grp = _group_cache.get(key)
    if grp is None:
        if len(_group_cache) > 60:
            _group_cache.clear()
        m, k, r = key
        order, mul, inv = lib.semidirect_group(m, k, r)
        grp = _Grp(order, mul, inv)
        _group_cache[key] = grp
    return grp


def _groups_of_order(G, rng):
    """List of keys (m, k, r) with Z_m x|_r Z_k of order G (m >= 2)."""
    out = []
    for k in range(1, G + 1):
        if G % k:
            continue
        m = G // k
        if m < 2:
            continue
        if k == 1:
            rs = [1]
        else:
            cands = [r for r in range(1, m)
                     if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
            if not cands:
                cands = [1]
            rs = cands if len(cands) <= 8 else rng.sample(cands, 8)
        for r in rs:
            out.append((m, k, r))
    return out


def _haar_cost(grp, S, D):
    """Number of (source, vertex) pairs not reached within distance D from A_e and from B_e."""
    G = grp.G
    N = 2 * G
    cols = [grp.col(s) for s in S]
    icols = [grp.col(grp.inv[s]) for s in S]
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
                    for c in cols:
                        v = G + c[u]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    h = u - G
                    for c in icols:
                        v = c[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            cnt += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - cnt
    return total


def _climb(grp, d, D, rng, end, iters):
    """Hill-climb a connection set S of size d in the group; returns S with zero cost or None."""
    G = grp.G
    S = rng.sample(range(G), d)
    c = _haar_cost(grp, S, D)
    for _ in range(iters):
        if c == 0 or time.monotonic() >= end:
            break
        i = rng.randrange(d)
        x = rng.randrange(G)
        if x in S:
            continue
        T = S[:]
        T[i] = x
        ct = _haar_cost(grp, T, D)
        if ct <= c:
            S, c = T, ct
    return S if c == 0 else None


def _haar_edges(grp, S):
    G = grp.G
    E = []
    for s in S:
        c = grp.col(s)
        E.extend((g, G + c[g]) for g in range(G))
    return 2 * G, E


def _group_haar_search(d, D, G, deadline, rng):
    """Scan group orders upward from G; return the largest-order valid Haar graph found (or None)."""
    best = None
    fails = 0
    while time.monotonic() < deadline and fails < 6:
        slice_end = min(deadline, time.monotonic() + 2.0)
        groups = _groups_of_order(G, rng)
        found = None
        while time.monotonic() < slice_end and found is None and groups:
            key = groups[rng.randrange(len(groups))]
            grp = _get_grp(key)
            S = _climb(grp, d, D, rng, slice_end, 300)
            if S is not None:
                found = _haar_edges(grp, S)
        if found is not None:
            best = found
            fails = 0
        else:
            fails += 1
        G += 1
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, min(0.75 * time_limit, time_limit - 8.0))
    rng = random.Random(seed)
    _group_cache.clear()

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    # Bold family: group Haar graphs. Skip when the Moore bound already matches
    # the current best (calibration cases such as d = 3, D = 3).
    if D >= 3 and d >= 2 and lib.moore_bound(d, D) > best[0] and time.monotonic() < deadline:
        res = _group_haar_search(d, D, best[0] // 2 + 1, deadline, rng)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
