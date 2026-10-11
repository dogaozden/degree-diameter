import math
import random
import time

import lib

# ----------------------------------------------------------------------------
# Helpers: bitmask ball counts, projective-plane baseline, cyclic / semidirect
# groups, and bi-Cayley (group-voltage) lifts.
#
# New in this version: a degree-preserving 2-switch annealer (_switch_anneal).
# Group lifts are d-regular, so a near-miss lift can be turned into a valid
# graph by random double-edge swaps (a1-b1, a2-b2 -> a1-b2, a2-b1) that keep
# the graph bipartite and d-regular. Each swap is accepted by a Metropolis rule
# on the number of pairs at distance > D. The parent only deleted vertices
# when a lift missed, and never rewired.
# ----------------------------------------------------------------------------


def _balls(n, adj, r):
    """Bitmask per vertex of all vertices within distance r."""
    ball = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return ball


def _bad(n, adj, D):
    """Number of ordered (source, target) pairs at distance > D. Zero means valid."""
    return sum(n - b.bit_count() for b in _balls(n, adj, D))


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _group(G, rng):
    """Random group of order G: cyclic or Z_m x| Z_k2. Returns (G, mul) or None."""
    divs = [k for k in range(1, 13) if G % k == 0 and G // k >= 2]
    if not divs:
        return None
    for _ in range(30):
        k2 = rng.choice(divs)
        m = G // k2
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in range(2, m)
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            _, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return G, mul
    return None


def _lift_edges(k, G, darts, perms):
    """Edges of the bi-Cayley lift. A_i,g = i*G+g and B_j,h = (k+j)*G+h."""
    E = set()
    for (i, j, _), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return sorted(E)


def _rep_cost(N, k, G, E, D):
    """Pairs not reached within D from block representatives.

    Left translations are automorphisms and act transitively on each block,
    so a representative per block covering all vertices means diameter <= D.
    """
    adj = [[] for _ in range(N)]
    for a, b in E:
        adj[a].append(b)
        adj[b].append(a)
    total = 0
    for t in range(2 * k):
        src = t * G
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
            cnt += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - cnt
    return total


def _lift_cost(k, G, D, darts, mul):
    """(cost, edges) for a dart assignment; (None, None) if two darts coincide."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return None, None
    perms = [[mul(g, s) for g in range(G)] for _, _, s in darts]
    E = _lift_edges(k, G, darts, perms)
    return _rep_cost(2 * k * G, k, G, E, D), E


def _lift_anneal(d, D, k, G, mul, rng, deadline, iters):
    """Anneal voltages and per-layer B-assignments. Returns (cost, darts)."""
    darts = []
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    cur, _ = _lift_cost(k, G, D, darts, mul)
    if cur is None:
        cur = 10 ** 9
    T = 1.0
    for _ in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.99)
        if k > 1 and rng.random() < 0.3:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2, _ = _lift_cost(k, G, D, darts, mul)
            if c2 is not None and (c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T)):
                cur = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
        else:
            idx = rng.randrange(len(darts))
            old = darts[idx][2]
            darts[idx][2] = rng.randrange(G)
            c2, _ = _lift_cost(k, G, D, darts, mul)
            if c2 is not None and (c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T)):
                cur = c2
            else:
                darts[idx][2] = old
    return cur, darts


def _set_pair(el, adj, es, N, p, q, np_, nq):
    """Replace edges p and q of the edge list with np_ and nq, updating adjacency and key set."""
    for idx in (p, q):
        a, b = el[idx]
        adj[a].remove(b)
        adj[b].remove(a)
        es.discard(a * N + b)
    for idx, (a, b) in ((p, np_), (q, nq)):
        el[idx] = [a, b]
        adj[a].append(b)
        adj[b].append(a)
        es.add(a * N + b)


def _switch_anneal(N, E, D, deadline, rng):
    """Degree-preserving bipartite 2-switch annealing toward diameter <= D.

    E holds (A, B) pairs, so every swap keeps the graph bipartite and regular.
    Returns a valid edge list, or None if the deadline passes first.
    """
    el = [[a, b] for a, b in E]
    es = {a * N + b for a, b in el}
    adj = [[] for _ in range(N)]
    for a, b in el:
        adj[a].append(b)
        adj[b].append(a)
    cur = _bad(N, adj, D)
    m = len(el)
    T = 1.0
    while cur > 0 and time.monotonic() < deadline:
        T = max(0.2, T * 0.9995)
        p = rng.randrange(m)
        q = rng.randrange(m)
        if p == q:
            continue
        a1, b1 = el[p]
        a2, b2 = el[q]
        if a1 == a2 or b1 == b2:
            continue
        if a1 * N + b2 in es or a2 * N + b1 in es:
            continue
        _set_pair(el, adj, es, N, p, q, (a1, b2), (a2, b1))
        new = _bad(N, adj, D)
        if new <= cur or rng.random() < math.exp(-(new - cur) / T):
            cur = new
        else:
            _set_pair(el, adj, es, N, p, q, (a1, b1), (a2, b2))
    if cur == 0:
        return [(a, b) for a, b in el]
    return None


def _repair(N, E, D, deadline, rng):
    """Delete far-off vertices in batches until diameter <= D. Returns (n, edges) or None."""
    n, e = N, list(E)
    while n > 0 and time.monotonic() < deadline:
        adj = [[] for _ in range(n)]
        for u, v in e:
            adj[u].append(v)
            adj[v].append(u)
        bad = [n - b.bit_count() for b in _balls(n, adj, D)]
        if not any(bad):
            return n, e
        bv = [v for v in range(n) if bad[v] > 0]
        rng.shuffle(bv)
        bv.sort(key=lambda v: -bad[v])
        dead = set(bv[:max(1, len(bv) // 12)])
        mapping = {}
        for v in range(n):
            if v not in dead:
                mapping[v] = len(mapping)
        e = [(mapping[u], mapping[v]) for u, v in e if u in mapping and v in mapping]
        n = len(mapping)
    return None


def _saturate(n, E, d, rng):
    """Add edges between deficient opposite-colour vertices. Never increases any distance."""
    e = list(E)
    adj = [[] for _ in range(n)]
    ex = set()
    for u, v in e:
        adj[u].append(v)
        adj[v].append(u)
        ex.add((min(u, v), max(u, v)))
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
    deg = [len(a) for a in adj]
    L = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    R = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in L for b in R if (min(a, b), max(a, b)) not in ex]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            e.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return n, e


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.8 * time_limit - 2.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if D < 4:
        return best_n, best_e

    # Main search: group lifts, then (for near misses) switch annealing,
    # with vertex-deletion repair as a fallback.
    while time.monotonic() < deadline:
        k = rng.choice([1, 1, 1, 2])
        G = best_n // (2 * k) + 1 + rng.randint(0, 3)
        g = _group(G, rng)
        if g is None:
            continue
        G, mul = g
        N = 2 * k * G

        cost, darts = _lift_anneal(d, D, k, G, mul, rng, deadline, 250)
        if cost is None or cost >= 10 ** 9:
            continue
        cost, E = _lift_cost(k, G, D, darts, mul)
        if E is None:
            continue
        if cost == 0:
            consider(N, E)
            continue
        if cost > 400:
            continue

        sw_deadline = min(deadline, time.monotonic() + 12.0)
        sol = _switch_anneal(N, E, D, sw_deadline, rng)
        if sol is not None:
            consider(N, sol)
            continue

        rep = _repair(N, E, D, min(deadline, time.monotonic() + 4.0), rng)
        if rep is not None:
            n2, e2 = _saturate(rep[0], rep[1], d, rng)
            consider(n2, e2)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, best_e
