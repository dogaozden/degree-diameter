import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Small safe families (used as fallbacks and for D = 3).
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


def _kdd(d):
    """K_{d,d}: diameter 2, degree d, valid for every D >= 2."""
    return lib.haar_graph(d, range(d))


# ----------------------------------------------------------------------------
# New family: unstructured bipartite regular graphs grown one block at a time.
#
# State: h vertices per side. A-vertex a has global id a; B-vertex b has id h+b.
# E is a list of (a, b) pairs, every vertex has degree exactly d.
#
# Growth step (s new vertices per side): remove a matching of d*s edges. Each
# freed A endpoint and B endpoint receives exactly one new edge to a new vertex
# on the other side, so all degrees return to d and the graph stays bipartite.
# The new graph is then repaired by edge switches that minimise the number of
# ordered pairs at distance greater than D.
# ----------------------------------------------------------------------------

def _cost(h, E, D):
    """Number of ordered vertex pairs at distance > D (0 means diameter <= D and connected)."""
    N = 2 * h
    adj = [[] for _ in range(N)]
    for a, b in E:
        adj[a].append(h + b)
        adj[h + b].append(a)
    ball = [1 << v for v in range(N)]
    for _ in range(D):
        new = [0] * N
        for v in range(N):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new[v] = x
        if new == ball:
            break
        ball = new
    return sum(N - x.bit_count() for x in ball)


def _ls(h, E, Eset, D, deadline, rng):
    """Edge-switch local search (degree preserving). Returns True if diameter <= D was reached."""
    cur = _cost(h, E, D)
    it = 0
    while cur > 0 and time.monotonic() < deadline:
        it += 1
        m = len(E)
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in Eset or (a2, b1) in Eset:
            continue
        # Apply the switch (a1,b1),(a2,b2) -> (a1,b2),(a2,b1).
        E[i] = (a1, b2)
        E[j] = (a2, b1)
        Eset.discard((a1, b1))
        Eset.discard((a2, b2))
        Eset.add((a1, b2))
        Eset.add((a2, b1))
        new = _cost(h, E, D)
        T = max(0.2, 3.0 * (0.998 ** it))
        if new <= cur or rng.random() < math.exp(-(new - cur) / T):
            cur = new
        else:
            # Revert.
            E[i] = (a1, b1)
            E[j] = (a2, b2)
            Eset.discard((a1, b2))
            Eset.discard((a2, b1))
            Eset.add((a1, b1))
            Eset.add((a2, b2))
    return cur == 0


def _grow(h, E, d, s, rng):
    """Add s vertices per side, keeping all degrees at d. Returns (h_new, E_new) or None."""
    need = d * s
    idx = list(range(len(E)))
    rng.shuffle(idx)
    usedA, usedB, chosen = set(), set(), []
    for k in idx:
        a, b = E[k]
        if a in usedA or b in usedB:
            continue
        usedA.add(a)
        usedB.add(b)
        chosen.append(k)
        if len(chosen) == need:
            break
    if len(chosen) < need:
        return None
    fa = [E[k][0] for k in chosen]
    fb = [E[k][1] for k in chosen]
    rem = set(chosen)
    E2 = [E[k] for k in range(len(E)) if k not in rem]
    rng.shuffle(fa)
    rng.shuffle(fb)
    for j in range(s):
        for b in fb[j * d:(j + 1) * d]:
            E2.append((h + j, b))      # new A-vertex h+j joins freed B-endpoints
        for a in fa[j * d:(j + 1) * d]:
            E2.append((a, h + j))      # new B-vertex h+j joins freed A-endpoints
    return h + s, E2


def _growth_search(d, D, deadline, rng, moore_cap):
    """Grow a d-regular bipartite graph while keeping diameter <= D. Returns (h, E) of the best state."""
    h = d
    E = [(a, b) for a in range(d) for b in range(d)]   # K_{d,d}
    s = max(1, h // 10)
    while time.monotonic() < deadline and 2 * h < moore_cap:
        cand = _grow(h, E, d, s, rng)
        if cand is None:
            s = max(1, s // 2)
            continue
        nh, nE = cand
        nEset = set(nE)
        remaining = deadline - time.monotonic()
        slice_end = min(deadline, time.monotonic() + max(1.0, 0.25 * remaining))
        if _ls(nh, nE, nEset, D, slice_end, rng):
            h, E = nh, nE
            s = max(1, h // 10)
        else:
            s = max(1, s // 2)
    return h, E


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.8 * time_limit)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        # Even cycle of length 2D has diameter D and is bipartite.
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d} (diameter 2).
    best_n, best_e = _kdd(d)[0], _kdd(d)[1]
    best = (best_n, best_e)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    # Moore bound for bipartite graphs: 2 * sum_{i<D} (d-1)^i.
    moore = 2 * sum((d - 1) ** i for i in range(D))
    if best_n >= moore:
        return best

    # Main search: unstructured growth with edge-switch repair.
    h, E = _growth_search(d, D, deadline, rng, moore)
    if h > 0 and 2 * h > best_n:
        n = 2 * h
        edges = [(a, h + b) for a, b in E]
        consider(n, edges)

    if not lib.is_valid(best[0], best[1], d, D):
        best = _kdd(d)
    return best
