import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base graphs.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Point-line incidence graph of the generalized quadrangle W(q): degree q+1, diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))
    edges = [(p, P + j) for j, L in enumerate(lines) for p in L]
    return 2 * P, edges


# ----------------------------------------------------------------------------
# State helpers. A state is (n, S, col, deg):
#   S   : set of edges (a, b) with col[a] = 0 and col[b] = 1,
#   col : side of each vertex, deg : degree of each vertex.
# ----------------------------------------------------------------------------

def _colors(n, E):
    adj = [[] for _ in range(n)]
    for u, v in E:
        adj[u].append(v)
        adj[v].append(u)
    col = [-1] * n
    for s in range(n):
        if col[s] != -1:
            continue
        col[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if col[v] == -1:
                    col[v] = 1 - col[u]
                    stack.append(v)
    return col


def _state(n, E):
    col = _colors(n, E)
    S = set((u, v) if col[u] == 0 else (v, u) for u, v in E)
    deg = [0] * n
    for a, b in S:
        deg[a] += 1
        deg[b] += 1
    return n, S, col, deg


def _saturate(n, S, deg, col, d, rng):
    """Add edges between non-adjacent opposite-side vertices with spare degree (never breaks diameter)."""
    left = [v for v in range(n) if col[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if col[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right if (a, b) not in S]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d and (a, b) not in S:
            S.add((a, b))
            deg[a] += 1
            deg[b] += 1


# ----------------------------------------------------------------------------
# Twin blow-up: a vertex v with spare neighbours gets a twin v' with N(v') = N(v).
# Twins keep the diameter and bipartiteness.
# ----------------------------------------------------------------------------

def _twin_round(n, E, d, rng):
    adj = [[] for _ in range(n)]
    for u, v in E:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    order = list(range(n))
    rng.shuffle(order)
    newE = list(E)
    nn = n
    for v in order:
        nb = adj[v]
        if not nb or any(deg[u] >= d for u in nb):
            continue
        for u in nb:
            deg[u] += 1
            newE.append((u, nn))
        nn += 1
    return nn, newE


# ----------------------------------------------------------------------------
# NEW: insert-and-anneal growth.
# Insert a vertex v of degree d. Full neighbours give up one edge to make room.
# This can break the diameter, so a degree-preserving 2-switch annealing
# (edges (a,b),(a2,b2) -> (a,b2),(a2,b)) repairs it, with cost = bad pairs.
# A new vertex is kept only if the repair reaches zero bad pairs.
# ----------------------------------------------------------------------------

def _grow_once(state, d, D, rng, deadline, moves):
    n, S, col, deg = state
    c = rng.randrange(2)
    v = n
    cols = col + [c]
    Sn = set(S)
    degn = deg + [0]
    others = [x for x in range(n) if col[x] == 1 - c]
    rng.shuffle(others)
    for x in others[:d]:
        if degn[x] >= d:
            e = rng.choice([e for e in Sn if x in e])
            Sn.discard(e)
            degn[e[0]] -= 1
            degn[e[1]] -= 1
        e = (x, v) if c == 1 else (v, x)
        Sn.add(e)
        degn[x] += 1
        degn[v] += 1
    N = n + 1
    _saturate(N, Sn, degn, cols, d, rng)
    L = list(Sn)
    cost = lib.bad_pairs(N, L, D)
    for it in range(moves):
        if cost == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(len(L))
        j = rng.randrange(len(L))
        a, b = L[i]
        a2, b2 = L[j]
        if a == a2 or b == b2 or (a, b2) in Sn or (a2, b) in Sn:
            continue
        Sn.discard((a, b))
        Sn.discard((a2, b2))
        Sn.add((a, b2))
        Sn.add((a2, b))
        L[i] = (a, b2)
        L[j] = (a2, b)
        c2 = lib.bad_pairs(N, L, D)
        T = 0.5 * (0.05 ** (it / moves)) + 0.02
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
        else:
            Sn.discard((a, b2))
            Sn.discard((a2, b))
            Sn.add((a, b))
            Sn.add((a2, b2))
            L[i] = (a, b)
            L[j] = (a2, b2)
    if cost != 0:
        return state
    _saturate(N, Sn, degn, cols, d, rng)
    return N, Sn, cols, degn


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit - 1.0
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    if D == 3:
        pg = _best_pg(d)
        if pg is not None and pg[0] > best[0] and lib.is_valid(pg[0], pg[1], d, D):
            best = pg
        return best

    if D >= 4 and d >= 3 and time.monotonic() < deadline:
        q = [x for x in range(2, d) if lib.is_prime_power(x)][-1]
        n, E = _gq_w(q)
        if n > best[0] and lib.is_valid(n, E, d, D):
            best = (n, E)

        cur = _state(n, E)
        tb = cur
        for _ in range(10):
            if time.monotonic() >= deadline:
                break
            nn, EE = _twin_round(cur[0], list(cur[1]), d, rng)
            if nn > tb[0] and lib.bad_pairs(nn, EE, D) == 0:
                tb = _state(nn, EE)
        _saturate(tb[0], tb[1], tb[3], tb[2], d, rng)

        for cand_state in (tb,):
            if cand_state[0] > best[0]:
                cand = (cand_state[0], list(cand_state[1]))
                if lib.is_valid(cand[0], cand[1], d, D):
                    best = cand

        cur = tb
        while time.monotonic() < deadline:
            cur = _grow_once(cur, d, D, rng, deadline, 400)
        if cur[0] > best[0]:
            cand = (cur[0], list(cur[1]))
            if lib.is_valid(cand[0], cand[1], d, D):
                best = cand

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
