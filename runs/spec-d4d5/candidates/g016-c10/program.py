import math
import random
import time

import lib


def _cost(n, adj, D):
    """Number of unordered vertex pairs at distance greater than D (0 means valid)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            x = reach[v]
            for u in adj[v]:
                x |= reach[u]
            new.append(x)
        if new == reach:
            break
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


class _State:
    """Biregular-by-construction state: left ids are the first side, right ids the second."""

    def __init__(self, n, edges, d):
        self.n = n
        self.d = d
        self.adj = [set() for _ in range(n)]
        self.edges = []
        self.eset = set()
        for a, b in edges:
            self.edges.append((a, b))
            self.eset.add((a, b))
            self.adj[a].add(b)
            self.adj[b].add(a)


def _replace(st, i, j, new_pair):
    """Put new_pair = (e_i, e_j) at positions i, j, updating edge set and adjacency.

    Used both to apply a 2-switch and to undo it (pass the old pair).
    """
    for (u, v) in (st.edges[i], st.edges[j]):
        st.eset.discard((u, v))
        st.adj[u].discard(v)
        st.adj[v].discard(u)
    st.edges[i], st.edges[j] = new_pair
    for (u, v) in new_pair:
        st.eset.add((u, v))
        st.adj[u].add(v)
        st.adj[v].add(u)


def _grow(st, rng, d):
    """Add one left vertex x and one right vertex y, each of degree d.

    Each step takes an existing edge (a, b), reroutes it to (x, b) and adds (a, y).
    Degrees of old vertices are preserved, so the graph stays d-regular-or-less.
    """
    x = st.n
    y = x + 1
    st.n += 2
    st.adj.append(set())
    st.adj.append(set())
    for _ in range(d):
        ok = False
        idx = -1
        a = b = -1
        for _try in range(4000):
            idx = rng.randrange(len(st.edges))
            a, b = st.edges[idx]
            if b in st.adj[x] or a in st.adj[y]:
                continue
            ok = True
            break
        if not ok:
            return False
        # Replace (a, b) by (x, b).
        st.edges[idx] = (x, b)
        st.eset.discard((a, b))
        st.eset.add((x, b))
        st.adj[a].discard(b)
        st.adj[b].discard(a)
        st.adj[x].add(b)
        st.adj[b].add(x)
        # Add (a, y).
        st.edges.append((a, y))
        st.eset.add((a, y))
        st.adj[a].add(y)
        st.adj[y].add(a)
    return True


def _anneal(st, D, rng, deadline):
    """Random 2-switches (degree- and bipartiteness-preserving), annealed on bad-pair count.

    Returns True once every pair is within distance D, False if the deadline passes.
    """
    cost = _cost(st.n, st.adj, D)
    step = 0
    T0, T1, cyc = 1.5, 0.05, 1500
    while cost > 0:
        if time.monotonic() >= deadline:
            return False
        step += 1
        frac = (step % cyc) / cyc
        T = T0 * (T1 / T0) ** frac
        E = st.edges
        m = len(E)
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in st.eset or (a2, b1) in st.eset:
            continue
        old = (E[i], E[j])
        _replace(st, i, j, ((a1, b2), (a2, b1)))
        c2 = _cost(st.n, st.adj, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            _replace(st, i, j, old)
    return True


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, min(0.85 * time_limit, time_limit - 5.0))

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d}, diameter 2, valid for every D >= 2.
    kk = [(i, d + j) for i in range(d) for j in range(d)]
    best_n, best_e = 2 * d, kk
    if D == 2:
        return best_n, best_e

    start_n, start_e = best_n, kk
    try:
        # Diameter-3 base: incidence graph of PG(2, d-1), d-regular, when d-1 is a prime power.
        if d >= 3 and lib.is_prime_power(d - 1):
            n_pg, e_pg = lib.projective_plane_incidence(d - 1)
            if lib.is_valid(n_pg, e_pg, d, D):
                best_n, best_e = n_pg, e_pg
                start_n, start_e = n_pg, e_pg

        rng = random.Random(seed)
        st = _State(start_n, start_e, d)
        # Grow by two vertices at a time, repairing diameter by annealed 2-switches.
        while time.monotonic() < deadline:
            if not _grow(st, rng, d):
                break
            if not _anneal(st, D, rng, deadline):
                break
            if st.n > best_n:
                cand = list(st.edges)
                if lib.is_valid(st.n, cand, d, D):
                    best_n, best_e = st.n, cand
    except Exception:
        pass

    if not lib.is_valid(best_n, best_e, d, D):
        return 2 * d, kk
    return best_n, best_e
