import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base graphs.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Point-line incidence graph of the generalized quadrangle W(q); diameter 4, (q+1)-regular.

    Points are 0..P-1 and lines are P..P+L-1. Every edge joins a point to a line.
    """
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
    return P + len(lines), edges


# ----------------------------------------------------------------------------
# Voltage lifts over Z_m of a bipartite base graph (points lower-indexed).
# A spanning tree of the base gets voltage 0 (WLOG), and the remaining darts
# are annealed. Cost = number of ordered pairs at distance > D, via bitsets.
# ----------------------------------------------------------------------------

def _bfs_tree(nb, pairs):
    """Set of dart indices forming a BFS spanning forest of the base."""
    adj = [[] for _ in range(nb)]
    for idx, (u, v) in enumerate(pairs):
        adj[u].append((v, idx))
        adj[v].append((u, idx))
    seen = [False] * nb
    tree = set()
    for s in range(nb):
        if seen[s]:
            continue
        seen[s] = True
        stack = [s]
        while stack:
            u = stack.pop()
            for v, idx in adj[u]:
                if not seen[v]:
                    seen[v] = True
                    tree.add(idx)
                    stack.append(v)
    return tree


def _lift_cost(nb, pairs, volts, m, D):
    """Return (bad ordered pairs, adjacency) for the Z_m lift with given voltages."""
    N = nb * m
    adj = [[] for _ in range(N)]
    for (u, v), g in zip(pairs, volts):
        ub = u * m
        vb = v * m
        for x in range(m):
            a = ub + x
            b = vb + (x + g) % m
            adj[a].append(b)
            adj[b].append(a)
    ball = [1 << i for i in range(N)]
    for _ in range(D):
        new = [0] * N
        for i in range(N):
            acc = ball[i]
            for j in adj[i]:
                acc |= ball[j]
            new[i] = acc
        ball = new
    bad = 0
    for b in ball:
        bad += N - b.bit_count()
    return bad, adj


def _lift_edges(nb, pairs, volts, m):
    E = set()
    for (u, v), g in zip(pairs, volts):
        for x in range(m):
            a = u * m + x
            b = v * m + (x + g) % m
            E.add((a, b) if a < b else (b, a))
    return nb * m, sorted(E)


def _anneal_lift(nb, pairs, m, D, free, rng, deadline):
    """Anneal non-tree voltages until the lift has diameter <= D or the deadline passes."""
    volts = [0] * len(pairs)
    for i in free:
        volts[i] = rng.randrange(m)
    cur, _ = _lift_cost(nb, pairs, volts, m, D)
    T = 1.5
    while cur > 0 and time.monotonic() < deadline:
        i = rng.choice(free)
        old = volts[i]
        new = rng.randrange(m)
        if new == old:
            continue
        volts[i] = new
        c, _ = _lift_cost(nb, pairs, volts, m, D)
        if c <= cur or rng.random() < math.exp(-(c - cur) / T):
            cur = c
        else:
            volts[i] = old
        T = max(0.2, T * 0.999)
    return (volts if cur == 0 else None), cur


def _lift_search(bases, D, deadline, rng, consider, get_best_n):
    """Try lifts of each base graph over Z_m for growing m, keeping any that pass."""
    now = time.monotonic()
    share = max(0.0, (deadline - now) / max(1, len(bases)))
    for nb, pairs in bases:
        base_deadline = min(deadline, time.monotonic() + share)
        tree = _bfs_tree(nb, pairs)
        free = [i for i in range(len(pairs)) if i not in tree]
        if not free:
            continue
        m = max(2, get_best_n() // nb)
        while time.monotonic() < base_deadline:
            success = False
            while time.monotonic() < base_deadline:
                chunk = min(base_deadline, time.monotonic() + 6.0)
                volts, _ = _anneal_lift(nb, pairs, m, D, free, rng, chunk)
                if volts is not None:
                    n, e = _lift_edges(nb, pairs, volts, m)
                    consider(n, e)
                    success = True
                    break
            if not success:
                break
            m += 1


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    q = d - 1
    pp = q >= 2 and lib.is_prime_power(q)

    if D >= 3 and pp:
        n0, e0 = lib.projective_plane_incidence(q)
        consider(n0, e0)

    if D >= 4 and pp and q <= 7:
        nw, ew = _gq_w(q)
        consider(nw, ew)

    if D >= 5 and pp:
        bases = []
        n0, e0 = lib.projective_plane_incidence(q)
        bases.append((n0, [(int(u), int(v)) for u, v in e0]))
        if q <= 7:
            nw, ew = _gq_w(q)
            bases.append((nw, [(int(u), int(v)) for u, v in ew]))
        _lift_search(bases, D, deadline, rng, consider, lambda: best_n)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
