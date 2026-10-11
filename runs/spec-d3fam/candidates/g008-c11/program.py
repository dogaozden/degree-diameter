"""Edge-switch annealing growth for bipartite diameter-3 graphs.

Bold variant: instead of algebraic lifts, start from the best valid algebraic
base (Araujo-Pardo & Lopez when d-2 is a prime power, else PG(2,q) or K_{d,d}).
Grow by two vertices (one per side) by removing a matching of size d, wiring the
two new vertices to the freed endpoints, then repair the diameter with
degree-preserving bipartite double-edge swaps under threshold annealing.
Every returned graph is verified with lib.is_valid; K_{d,d} is the fallback.
"""
import math
import random
import time

import lib


def _candidates(d, D):
    """Algebraic base graphs; each is kept only if it is valid for (d, D)."""
    out = []
    if d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            out.append(lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            out.append(lib.projective_plane_incidence(q))
            break
    out.append(lib.haar_graph(d, range(d)))
    return [c for c in out if lib.is_valid(c[0], c[1], d, D)]


def _two_color(n, adj):
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
    return color


def _cost(n, adj, D):
    """Number of unordered vertex pairs at distance more than D."""
    ball = [1 << v for v in range(n)]
    for _ in range(D):
        nb = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            nb.append(x)
        ball = nb
    return sum(n - b.bit_count() for b in ball) // 2


def _anneal(n, E, adj, d, D, deadline, rng):
    """Double-edge swaps (keep degrees and bipartition) until cost 0 or deadline.

    E is a list of [a, b] with a on side 0 and b on side 1; adj are sets.
    """
    m = len(E)
    if m < 2:
        return False
    cur = _cost(n, adj, D)
    t0 = time.monotonic()
    span = max(1e-6, deadline - t0)
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        frac = min(1.0, (now - t0) / span)
        T = 2.0 * (0.025 ** frac)
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2 or b2 in adj[a1] or b1 in adj[a2]:
            continue
        adj[a1].discard(b1); adj[b1].discard(a1)
        adj[a2].discard(b2); adj[b2].discard(a2)
        adj[a1].add(b2); adj[b2].add(a1)
        adj[a2].add(b1); adj[b1].add(a2)
        E[i] = [a1, b2]
        E[j] = [a2, b1]
        new = _cost(n, adj, D)
        thr = cur + T * (-math.log(1.0 - rng.random()))
        if new <= thr:
            cur = new
        else:
            adj[a1].discard(b2); adj[b2].discard(a1)
            adj[a2].discard(b1); adj[b1].discard(a2)
            adj[a1].add(b1); adj[b1].add(a1)
            adj[a2].add(b2); adj[b2].add(a2)
            E[i] = [a1, b1]
            E[j] = [a2, b2]
    return cur == 0


def _try_grow(n, edges, d, D, deadline, rng):
    """Add one A vertex and one B vertex by removing a size-d matching and rewiring."""
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    color = _two_color(n, adj)
    E = [[u, v] if color[u] == 0 else [v, u] for u, v in edges]

    order = list(range(len(E)))
    rng.shuffle(order)
    ua, ub, chosen = set(), set(), []
    for idx in order:
        a, b = E[idx]
        if a not in ua and b not in ub:
            chosen.append(idx)
            ua.add(a)
            ub.add(b)
            if len(chosen) == d:
                break
    if len(chosen) < d:
        return None

    x, y, N = n, n + 1, n + 2
    cset = set(chosen)
    newE = [E[i] for i in range(len(E)) if i not in cset]
    for idx in chosen:
        a, b = E[idx]
        newE.append([x, b])   # new A vertex joins freed B endpoint
        newE.append([a, y])   # new B vertex joins freed A endpoint

    adjN = [set() for _ in range(N)]
    for a, b in newE:
        adjN[a].add(b)
        adjN[b].add(a)
    if any(len(s) > d for s in adjN):
        return None

    if not _anneal(N, newE, adjN, d, D, deadline, rng):
        return None
    out = [(a, b) for a, b in newE]
    if lib.is_valid(N, out, d, D):
        return N, out
    return None


def _grow_search(n, edges, d, D, deadline, rng):
    """Repeatedly grow by two vertices while annealing succeeds. Returns best (n, edges) or None."""
    best = None
    cur_n, cur_e = n, edges
    failures = 0
    while time.monotonic() < deadline and failures < 20:
        remaining = deadline - time.monotonic()
        attempt_deadline = time.monotonic() + 0.5 * remaining
        res = _try_grow(cur_n, cur_e, d, D, attempt_deadline, rng)
        if res is None:
            failures += 1
            continue
        cur_n, cur_e = res
        best = res
        failures = 0
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    fallback = lib.haar_graph(d, range(d))  # K_{d,d}, diameter 2
    best = fallback

    try:
        for n_c, e_c in _candidates(d, D):
            if n_c > best[0]:
                best = (n_c, e_c)
    except Exception:
        best = fallback

    if D == 3 and d >= 3:
        try:
            grown = _grow_search(best[0], best[1], d, D, deadline, rng)
            if grown is not None and grown[0] > best[0]:
                best = grown
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
