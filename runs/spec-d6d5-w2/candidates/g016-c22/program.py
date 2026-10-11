import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Baseline bases: projective plane incidence and the Araujo-Pardo-Lopez graph
# (both D = 3 records). Bi-Cayley (Haar-type) searches over non-abelian groups
# give the regular base graphs for D >= 5.
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


def _is_prime(p):
    if p < 2:
        return False
    i = 2
    while i * i <= p:
        if p % i == 0:
            return False
        i += 1
    return True


def _affine_mul(p):
    """Multiplication in AGL(1,p): element (u-1)*p + b encodes x -> u*x + b, u in 1..p-1."""
    def mul(x, y):
        u, b = divmod(x, p)
        u += 1
        v, c = divmod(y, p)
        v += 1
        return (((u * v) % p) - 1) * p + (u * c + b) % p
    return mul


def _mul_table(order, mul):
    M = np.empty((order, order), dtype=np.int64)
    for x in range(order):
        M[x, :] = [mul(x, y) for y in range(order)]
    return M


def _group_specs(lo, hi, cap=60):
    """Group specs with order in [lo, hi]: affine groups first, then semidirect products."""
    specs = []
    for p in range(3, hi + 2):
        o = p * (p - 1)
        if lo <= o <= hi and _is_prime(p):
            specs.append((o, ("aff", p)))
    for m in range(3, hi + 1):
        for k in range(2, hi // m + 1):
            o = m * k
            if o < lo or o > hi:
                continue
            for r in range(2, m):
                if math.gcd(r, m) == 1 and pow(r, k, m) == 1 and r != 1:
                    specs.append((o, ("sd", m, k, r)))
                    break
    specs.sort(key=lambda t: (0 if t[1][0] == "aff" else 1, t[0]))
    return specs[:cap]


def _make_group(spec):
    if spec[0] == "aff":
        p = spec[1]
        order = p * (p - 1)
        return order, _mul_table(order, _affine_mul(p))
    _, m, k, r = spec
    order, mul, _ = lib.semidirect_group(m, k, r)
    return order, _mul_table(order, mul)


def _identity_ok(M):
    G = M.shape[0]
    ar = np.arange(G)
    return bool(np.array_equal(M[0], ar) and np.array_equal(M[:, 0], ar))


def _bc_adj(M, inv, S, G):
    """Adjacency array (2G, d): row x < G lists B-nodes G + x*s, row G+w lists A-nodes w*s^-1."""
    Sa = np.asarray(S, dtype=np.int64)
    iS = inv[Sa]
    return np.vstack([G + M[:, Sa], M[:, iS]])


def _bc_cost(adj, G, D):
    """Unreached-vertex count from A_1 (node 0) and B_1 (node G) within D steps. Zero means valid."""
    N = adj.shape[0]
    total = 0
    for src in (0, G):
        seen = np.zeros(N, dtype=bool)
        seen[src] = True
        frontier = np.array([src], dtype=np.int64)
        for _ in range(D):
            nb = adj[frontier].ravel()
            nb = nb[~seen[nb]]
            if nb.size == 0:
                break
            nb = np.unique(nb)
            seen[nb] = True
            frontier = nb
        total += N - int(np.count_nonzero(seen))
    return total


def _search_group(M, G, d, D, deadline, rng, iters=1500):
    """Annealed search over connection sets S (|S| = d) until cost 0 or deadline."""
    inv = np.argmax(M == 0, axis=1)
    while time.monotonic() < deadline:
        S = rng.sample(range(G), d)
        c = _bc_cost(_bc_adj(M, inv, S, G), G, D)
        T = 2.0
        for _ in range(iters):
            if c == 0 or time.monotonic() >= deadline:
                break
            T = max(0.05, T * 0.997)
            i = rng.randrange(d)
            x = rng.randrange(G)
            if x in S:
                continue
            T2 = list(S)
            T2[i] = x
            c2 = _bc_cost(_bc_adj(M, inv, T2, G), G, D)
            if c2 <= c or rng.random() < math.exp((c - c2) / T):
                S, c = T2, c2
        if c == 0:
            return S
    return None


def _bc_edges(M, S, G):
    E = []
    for x in range(G):
        for s in S:
            E.append((x, G + int(M[x, s])))
    return 2 * G, E


def _bicayley_phase(d, D, lo, deadline, rng, accept):
    """Search bi-Cayley graphs over groups of order >= lo with growing budgets per round."""
    best_G = lo - 1
    hi = int(1.5 * lo) + 2
    rnd = 0
    while time.monotonic() < deadline:
        budget = (1.0, 2.5, 5.0, 10.0)[min(rnd, 3)]
        rnd += 1
        specs = _group_specs(max(best_G + 1, lo), hi, cap=60)
        if not specs:
            break
        for o, spec in specs:
            if time.monotonic() >= deadline:
                return
            if o <= best_G:
                continue
            try:
                G, M = _make_group(spec)
            except Exception:
                continue
            if not _identity_ok(M):
                continue
            sub = min(deadline, time.monotonic() + budget)
            S = _search_group(M, G, d, D, sub, rng)
            if S is None:
                continue
            best_G = max(best_G, G)
            n, e = _bc_edges(M, S, G)
            accept(n, e)


# ----------------------------------------------------------------------------
# Graph helpers.
# ----------------------------------------------------------------------------

def _adj_of(n, E):
    adj = [[] for _ in range(n)]
    for u, v in E:
        adj[u].append(v)
        adj[v].append(u)
    return adj


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


def _balls_radius(n, adj, r):
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


# ----------------------------------------------------------------------------
# NEW CONSTRUCTION: split-extension ratchet with degree-preserving repair.
#
# Given a bipartite graph (sides given by `color`, edges oriented side-0 first),
# add two new vertices v (side 0) and w (side 1) without touching any existing
# degree. Choose d edges (x_i, y_i) with distinct x_i and distinct y_i, and
# replace each by (x_i, w) and add (v, y_i). Afterwards v and w have degree d
# and every old degree is unchanged, so the order grows by 2 and the graph
# stays simple and bipartite. The diameter is usually broken, so a
# degree-preserving 2-switch anneal repairs it. Each success becomes the next
# base, which ratchets the order upward.
# ----------------------------------------------------------------------------

def _split_extend(n, E, color, d, rng):
    """Return (n+2, edges, color) with two new vertices of degree d, or None."""
    idx = list(range(len(E)))
    rng.shuffle(idx)
    chosen, used_a, used_b = [], set(), set()
    for i in idx:
        a, b = E[i]
        if a in used_a or b in used_b:
            continue
        chosen.append(i)
        used_a.add(a)
        used_b.add(b)
        if len(chosen) == d:
            break
    if len(chosen) < d:
        return None
    v, w = n, n + 1
    En = [list(e) for e in E]
    for i in chosen:
        x, y = En[i]
        En[i] = [x, w]
        En.append([v, y])
    return n + 2, En, color + [0, 1]


def _anneal_switch(n, E, color, D, deadline, rng, T0=1.5):
    """2-switch annealing that keeps all degrees and bipartiteness.

    E is a list of [a, b] with color[a] = 0 and color[b] = 1. Cost = ordered
    pairs at distance > D. Moves are biased toward vertices with unreached
    pairs. Returns (ok, E).
    """
    adj = [set() for _ in range(n)]
    for a, b in E:
        adj[a].add(b)
        adj[b].add(a)
    balls = _balls_radius(n, adj, D)
    cur = sum(n - x.bit_count() for x in balls)
    T = T0
    m = len(E)
    while cur > 0 and time.monotonic() < deadline and m >= 2:
        T = max(0.05, T * 0.999)
        if rng.random() < 0.6:
            bad = [v for v in range(n) if balls[v].bit_count() < n]
            v = rng.choice(bad)
            cands = [k for k in range(m) if E[k][0] == v or E[k][1] == v]
            i = rng.choice(cands) if cands else rng.randrange(m)
        else:
            i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a, b = E[i]
        c, e = E[j]
        if a == c or b == e or e in adj[a] or b in adj[c]:
            continue
        adj[a].discard(b)
        adj[b].discard(a)
        adj[c].discard(e)
        adj[e].discard(c)
        adj[a].add(e)
        adj[e].add(a)
        adj[c].add(b)
        adj[b].add(c)
        nb = _balls_radius(n, adj, D)
        new = sum(n - x.bit_count() for x in nb)
        if new <= cur or rng.random() < math.exp((cur - new) / T):
            cur = new
            balls = nb
            E[i] = [a, e]
            E[j] = [c, b]
        else:
            adj[a].discard(e)
            adj[e].discard(a)
            adj[c].discard(b)
            adj[b].discard(c)
            adj[a].add(b)
            adj[b].add(a)
            adj[c].add(e)
            adj[e].add(c)
    return cur == 0, E


def _ratchet(n, E, color, d, D, deadline, rng, consider, budget):
    """Repeatedly grow the current valid graph by 2 vertices and repair it."""
    cur = (n, E, color)
    fails = 0
    while time.monotonic() < deadline:
        cn, cE, ccol = cur
        sp = _split_extend(cn, cE, ccol, d, rng)
        if sp is None:
            break
        n2, E2, col2 = sp
        span = budget * (1.0 + 0.5 * min(fails, 4))
        sub = min(deadline, time.monotonic() + span)
        ok, E2 = _anneal_switch(n2, E2, col2, D, sub, rng)
        if ok:
            cur = (n2, E2, col2)
            consider(n2, [(a, b) for a, b in E2])
            fails = 0
        else:
            fails += 1


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.88 * time_limit
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
            best = (n, list(e))
            best_n = n
            return True
        return False

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    # For D >= 5: bi-Cayley base graphs over non-abelian groups.
    if D >= 5 and d >= 3:
        moore_half = lib.moore_bound(d, D) // 2
        lo = max(2 * d, best_n // 2 + 1, int(0.4 * moore_half))
        fam_rng = random.Random(seed * 1000003 + d * 131 + D)
        _bicayley_phase(d, D, lo, start + 0.45 * time_limit, fam_rng, consider)

    # Ratchet: grow the best valid base by split-extensions plus switch repair.
    n0, e0 = best
    adj0 = _adj_of(n0, e0)
    color0 = _two_color(n0, adj0)
    E0 = []
    for u, v in e0:
        if color0[u] == 0:
            E0.append([u, v])
        else:
            E0.append([v, u])
    _ratchet(n0, E0, color0, d, D, deadline, rng, consider, 4.0)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
