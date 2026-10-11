import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bold change: no structured lift. Start from a small dense base (projective
# plane or K_{d,d}) and grow the bipartite graph one vertex pair at a time.
# Each new pair is wired into the existing graph by edge-splitting, which keeps
# every degree at most d. Then simulated annealing with degree-preserving
# double-edge switches removes all pairs at distance > D. The state is kept
# only when the diameter bound holds, so the output is always valid.
# ----------------------------------------------------------------------------


class _State:
    """Bipartite graph stored as oriented edges (left, right) with adjacency sets."""

    def __init__(self, n, edges):
        self.n = n
        self.E = [(a, b) for a, b in edges]
        self.Eset = set(self.E)
        self.adj = [set() for _ in range(n)]
        for a, b in self.E:
            self.adj[a].add(b)
            self.adj[b].add(a)


def _pg(d):
    """Incidence graph of PG(2, d-1) if d-1 is a prime power, else None."""
    q = d - 1
    if q >= 2 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)
    return None


def _cost(st, D):
    """Ordered vertex pairs at distance > D (zero means diameter <= D and connected)."""
    n = st.n
    adj = [list(s) for s in st.adj]
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        if new == reach:
            break
        reach = new
    return sum(n - r.bit_count() for r in reach)


def _apply(st, i, j, a1, b1, a2, b2):
    """Replace edges (a1,b1) at index i and (a2,b2) at index j by (a1,b2) and (a2,b1)."""
    st.Eset.discard((a1, b1))
    st.Eset.discard((a2, b2))
    st.adj[a1].discard(b1)
    st.adj[b1].discard(a1)
    st.adj[a2].discard(b2)
    st.adj[b2].discard(a2)
    na, nb = (a1, b2), (a2, b1)
    st.E[i] = na
    st.E[j] = nb
    st.Eset.add(na)
    st.Eset.add(nb)
    st.adj[a1].add(b2)
    st.adj[b2].add(a1)
    st.adj[a2].add(b1)
    st.adj[b1].add(a2)


def _insert_pair(st, d, rng):
    """Add a new left vertex A and right vertex B, each of degree d, by splitting d edges.

    Chosen edges (x, y) with distinct x and distinct y are replaced by (A, y) and (x, B).
    Every old vertex keeps its degree. Returns False if too few edges can be split.
    """
    idxs = list(range(len(st.E)))
    rng.shuffle(idxs)
    chosen, ux, uy = [], set(), set()
    for i in idxs:
        x, y = st.E[i]
        if x in ux or y in uy:
            continue
        chosen.append(i)
        ux.add(x)
        uy.add(y)
        if len(chosen) == d:
            break
    if len(chosen) < d:
        return False
    A = st.n
    B = A + 1
    st.n += 2
    st.adj.append(set())
    st.adj.append(set())
    for i in chosen:
        x, y = st.E[i]
        st.Eset.discard((x, y))
        st.adj[x].discard(y)
        st.adj[y].discard(x)
        st.E[i] = (A, y)
        st.Eset.add((A, y))
        st.adj[A].add(y)
        st.adj[y].add(A)
        st.E.append((x, B))
        st.Eset.add((x, B))
        st.adj[x].add(B)
        st.adj[B].add(x)
    return True


def _anneal(st, D, rng, iters, deadline, T0=3.0, T1=0.3):
    """Degree-preserving double-edge-switch annealing on the number of bad pairs."""
    cur = _cost(st, D)
    m = len(st.E)
    for it in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        T = T0 * (T1 / T0) ** (it / iters)
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = st.E[i]
        a2, b2 = st.E[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in st.Eset or (a2, b1) in st.Eset:
            continue
        _apply(st, i, j, a1, b1, a2, b2)
        c2 = _cost(st, D)
        delta = c2 - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = c2
        else:
            _apply(st, i, j, a1, b2, a2, b1)
    return cur


def _grow(d, D, n0, e0, deadline, rng, iters=800, attempts=3):
    """Repeatedly add a vertex pair and repair it; keep the last valid graph."""
    snap_n, snap_e = n0, list(e0)
    st = _State(snap_n, snap_e)
    while time.monotonic() < deadline:
        ok = False
        for att in range(attempts):
            if att > 0:
                st = _State(snap_n, snap_e)
            if not _insert_pair(st, d, rng):
                return snap_n, snap_e
            if _anneal(st, D, rng, iters, deadline) == 0:
                ok = True
                break
            if time.monotonic() >= deadline:
                break
        if not ok:
            break
        snap_n, snap_e = st.n, list(st.E)
    return snap_n, snap_e


def _safe(d, D, g, fallback):
    """Return g if it passes the exact validity check, else the fallback."""
    if g is not None and lib.is_valid(g[0], g[1], d, D):
        return g
    return fallback


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for every D >= 2.
    fallback = lib.haar_graph(d, range(d))
    if D == 2:
        return fallback

    pg = _pg(d)
    if D == 3 and pg is not None:
        # Moore-optimal for D = 3 when d-1 is a prime power.
        return _safe(d, D, pg, fallback)

    base = pg if pg is not None else fallback
    best = base
    rng = random.Random(seed)
    try:
        n2, e2 = _grow(d, D, base[0], base[1], deadline, rng)
        if n2 > best[0]:
            best = (n2, e2)
    except Exception:
        best = base

    return _safe(d, D, best, _safe(d, D, base, fallback))
