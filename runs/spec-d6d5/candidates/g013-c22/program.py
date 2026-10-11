"""Bold variant: annealed random d-regular bipartite graphs with edge-swap moves
(bad-pair cost), then repair by vertex deletion and greedy saturation.
Safe fallbacks (K_{d,d}, PG(2,q) incidence, cycle for d=2) are always validated
with lib.is_valid before being returned."""
import math
import random
import time

import lib


def _reach(N, adj, D):
    """Bitmask per vertex of all vertices within distance D."""
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        new = []
        for v in range(N):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return reach


def _bad_total(N, adj, D):
    """Number of unordered vertex pairs at distance > D (zero means diameter <= D)."""
    reach = _reach(N, adj, D)
    return sum(N - r.bit_count() for r in reach) // 2


def _rep(lst, old, new):
    lst[lst.index(old)] = new


def _random_regular_bip(h, d, rng):
    """Union of d random perfect matchings between A = 0..h-1 and B = 0..h-1, without repeats.

    Returns a list of (a, b) index pairs, or None if the local repair gets stuck.
    """
    used = set()
    E = []
    for _ in range(d):
        p = list(range(h))
        rng.shuffle(p)
        ok = False
        for _ in range(50 * h + 100):
            bad = [i for i in range(h) if (i, p[i]) in used]
            if not bad:
                ok = True
                break
            i = rng.choice(bad)
            j = rng.randrange(h)
            p[i], p[j] = p[j], p[i]
        if not ok:
            return None
        for i in range(h):
            used.add((i, p[i]))
            E.append((i, p[i]))
    return E


def _anneal(h, d, D, E0, rng, deadline, T0, T1):
    """Simulated annealing over double edge swaps (keeps the graph d-regular bipartite).

    Returns (E, cost) where E is a list of (a, b) index pairs and cost is the bad-pair count.
    """
    N = 2 * h
    E = list(E0)
    Eset = set(E)
    adj = [[] for _ in range(N)]
    for a, b in E:
        adj[a].append(h + b)
        adj[h + b].append(a)
    cost = _bad_total(N, adj, D)
    t_start = time.monotonic()
    span = max(1e-3, deadline - t_start)
    m = len(E)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        frac = (now - t_start) / span
        T = T0 * (T1 / T0) ** frac
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
        hb1 = h + b1
        hb2 = h + b2
        # remove (a1,hb1),(a2,hb2); add (a1,hb2),(a2,hb1)
        _rep(adj[a1], hb1, hb2)
        _rep(adj[hb1], a1, a2)
        _rep(adj[a2], hb2, hb1)
        _rep(adj[hb2], a2, a1)
        c2 = _bad_total(N, adj, D)
        if c2 <= cost or rng.random() < math.exp((cost - c2) / T):
            cost = c2
            Eset.discard((a1, b1))
            Eset.discard((a2, b2))
            Eset.add((a1, b2))
            Eset.add((a2, b1))
            E[i] = (a1, b2)
            E[j] = (a2, b1)
        else:
            _rep(adj[a1], hb2, hb1)
            _rep(adj[hb2], a1, a2)
            _rep(adj[a2], hb1, hb2)
            _rep(adj[hb1], a2, a1)
    return E, cost


def _repair(N, E, side, D, deadline, rng):
    """Delete far-off vertices in batches until diameter <= D. Returns (n, edges, sides) or None."""
    cur_n, cur_e, cur_side = N, list(E), list(side)
    while time.monotonic() < deadline:
        if cur_n == 0:
            return None
        adj = [[] for _ in range(cur_n)]
        for u, v in cur_e:
            adj[u].append(v)
            adj[v].append(u)
        reach = _reach(cur_n, adj, D)
        bad = [cur_n - r.bit_count() for r in reach]
        if not any(bad):
            return cur_n, cur_e, cur_side
        bad_v = [v for v in range(cur_n) if bad[v] > 0]
        rng.shuffle(bad_v)
        bad_v.sort(key=lambda v: -bad[v])
        batch = max(1, len(bad_v) // 12)
        dead = set(bad_v[:batch])
        new = {}
        for v in range(cur_n):
            if v not in dead:
                new[v] = len(new)
        cur_e = [(new[u], new[v]) for u, v in cur_e if u in new and v in new]
        new_side = [None] * len(new)
        for v, idx in new.items():
            new_side[idx] = cur_side[v]
        cur_side = new_side
        cur_n = len(new)
    return None


def _saturate(n, E, side, d, rng):
    """Greedily add edges between deficient opposite-side vertices (never hurts diameter)."""
    E = list(E)
    deg = [0] * n
    ex = set()
    for u, v in E:
        deg[u] += 1
        deg[v] += 1
        ex.add((min(u, v), max(u, v)))
    L = [v for v in range(n) if side[v] == 0 and deg[v] < d]
    R = [v for v in range(n) if side[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in L for b in R if (min(a, b), max(a, b)) not in ex]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            E.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return n, E


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.8 * time_limit - 3.0)
    rng = random.Random(seed)

    if d <= 0 or D <= 0:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    fb_n, fb_e = lib.haar_graph(d, range(d))
    best = {"n": fb_n, "e": fb_e}

    def consider(n, e):
        if n > best["n"] and lib.is_valid(n, e, d, D):
            best["n"], best["e"] = n, e

    if D == 2:
        return best["n"], best["e"]

    # Projective plane incidence graph for the largest prime power q <= d-1.
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            consider(*lib.projective_plane_incidence(q))
            break

    # Main search: annealed bipartite d-regular graphs of growing half-size.
    h = max(d + 1, best["n"] // 2 + 1)
    step = max(1, h // 60)
    while time.monotonic() < deadline - 1.0:
        E0 = None
        for _ in range(20):
            E0 = _random_regular_bip(h, d, rng)
            if E0 is not None:
                break
        if E0 is None:
            h += 1
            continue

        ch = min(deadline, time.monotonic() + 15.0)
        E, cost = _anneal(h, d, D, E0, rng, ch, 2.0, 0.2)
        N = 2 * h
        if cost == 0:
            consider(N, [(a, h + b) for a, b in E])
            h = max(h + 1, best["n"] // 2 + step)
        else:
            side = [0] * h + [1] * h
            edges = [(a, h + b) for a, b in E]
            rep_dl = min(deadline, time.monotonic() + 5.0)
            out = _repair(N, edges, side, D, rep_dl, rng)
            if out is not None:
                n3, e3, s3 = out
                n3, e3 = _saturate(n3, e3, s3, d, rng)
                consider(n3, e3)
            gap = max(1, (h - best["n"] // 2) // 2)
            h = best["n"] // 2 + gap

    n, e = best["n"], best["e"]
    if not lib.is_valid(n, e, d, D):
        n, e = fb_n, fb_e
    return n, e
