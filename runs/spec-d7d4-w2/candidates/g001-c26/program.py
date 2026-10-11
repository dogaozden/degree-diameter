import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bases: PG(2,q) for D = 3, generalized quadrangle W(q) for D >= 4.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
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


def _base(d, D):
    """Return (n, edges, color) for a structured base graph, or None."""
    if D == 3:
        q = max(x for x in range(2, d) if lib.is_prime_power(x))
        n, e = lib.projective_plane_incidence(q)
        m = n // 2
        return n, e, [0] * m + [1] * m
    q = max(x for x in range(2, min(d - 1, 8) + 1) if lib.is_prime_power(x))
    n, e = _gq_w(q)
    P = n // 2
    return n, e, [0] * P + [1] * P


# ----------------------------------------------------------------------------
# Bitset distance tools.
# ----------------------------------------------------------------------------

def _balls(N, adj, r):
    ball = [1 << v for v in range(N)]
    for _ in range(r):
        new = []
        for v in range(N):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return ball


def _cost(N, adj, D):
    """Number of unordered vertex pairs at distance > D (0 means valid)."""
    balls = _balls(N, adj, D)
    return sum(N - b.bit_count() for b in balls) // 2


# ----------------------------------------------------------------------------
# Graph moves.
# ----------------------------------------------------------------------------

def _rand_vertex(N, adj, color, side, rng):
    for _ in range(40):
        v = rng.randrange(N)
        if color[v] == side and adj[v]:
            return v
    return None


def _saturate(N, adj, color, d, rng):
    """Greedily add edges between deficient opposite-side vertices."""
    defs0 = [v for v in range(N) if color[v] == 0 and len(adj[v]) < d]
    defs1 = [v for v in range(N) if color[v] == 1 and len(adj[v]) < d]
    rng.shuffle(defs0)
    rng.shuffle(defs1)
    for x in defs0:
        for y in defs1:
            if len(adj[x]) >= d:
                break
            if len(adj[y]) < d and y not in adj[x]:
                adj[x].add(y)
                adj[y].add(x)


def _insert(N, adj, color, d, D, rng):
    """Add one vertex whose neighbourhood greedily covers the radius-(D-1) balls."""
    c = rng.randrange(2)
    full = (1 << N) - 1
    ball = _balls(N, adj, D - 1)
    cands = [s for s in range(N) if color[s] == 1 - c and len(adj[s]) < d]
    rng.shuffle(cands)
    covered = 0
    chosen = []
    while cands and len(chosen) < d and covered != full:
        s = max(cands, key=lambda t: (ball[t] & ~covered).bit_count())
        if (ball[s] & ~covered).bit_count() == 0:
            break
        chosen.append(s)
        cands.remove(s)
        covered |= ball[s]
    v = N
    adj.append(set())
    color.append(c)
    for s in chosen:
        adj[s].add(v)
        adj[v].add(s)
    return N + 1


def _anneal(N, adj, color, d, D, rng, deadline, iters, T0=1.0):
    """Anneal with degree-preserving switches and edge additions. Returns final cost."""
    cost = _cost(N, adj, D)
    for it in range(iters):
        if cost == 0:
            break
        if (it & 15) == 0 and time.monotonic() > deadline:
            break
        T = T0 * (0.03 ** (it / iters))
        if rng.random() < 0.25:
            defs0 = [v for v in range(N) if color[v] == 0 and len(adj[v]) < d]
            defs1 = [v for v in range(N) if color[v] == 1 and len(adj[v]) < d]
            if not defs0 or not defs1:
                continue
            x = rng.choice(defs0)
            y = rng.choice(defs1)
            if y in adj[x]:
                continue
            adj[x].add(y)
            adj[y].add(x)
            cost = _cost(N, adj, D)  # adding edges never increases cost
            continue
        a = _rand_vertex(N, adj, color, 0, rng)
        c = _rand_vertex(N, adj, color, 0, rng)
        if a is None or c is None:
            continue
        b = rng.choice(tuple(adj[a]))
        e = rng.choice(tuple(adj[c]))
        if a == c or b == e or e in adj[a] or b in adj[c]:
            continue
        adj[a].discard(b); adj[b].discard(a)
        adj[c].discard(e); adj[e].discard(c)
        adj[a].add(e); adj[e].add(a)
        adj[c].add(b); adj[b].add(c)
        new = _cost(N, adj, D)
        if new <= cost or rng.random() < math.exp((cost - new) / T):
            cost = new
        else:
            adj[a].discard(e); adj[e].discard(a)
            adj[c].discard(b); adj[b].discard(c)
            adj[a].add(b); adj[b].add(a)
            adj[c].add(e); adj[e].add(c)
    return cost


def _to_edges(N, adj, color):
    return [(a, b) for a in range(N) if color[a] == 0 for b in adj[a]]


# ----------------------------------------------------------------------------
# Main driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = float(time_limit)
    deadline = start + 0.85 * T
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        cyc = [(i, (i + 1) % n) for i in range(n)]
        if lib.is_valid(n, cyc, d, D):
            return n, cyc

    # Safe fallback: K_{d,d}, diameter 2 (valid for every D >= 2).
    best_n, best_e = lib.haar_graph(d, range(d))
    if D == 2:
        return best_n, best_e

    moore = lib.moore_bound(d, D)
    best_adj = None
    best_col = None

    # ---- Structured base -----------------------------------------------------
    try:
        n0, e0, c0 = _base(d, D)
        adj0 = [set() for _ in range(n0)]
        for u, v in e0:
            adj0[u].add(v)
            adj0[v].add(u)
        _saturate(n0, adj0, c0, d, rng)
        E0 = _to_edges(n0, adj0, c0)
        if lib.is_valid(n0, E0, d, D) and n0 > best_n:
            best_n, best_e = n0, E0
            best_adj, best_col = adj0, c0
    except Exception:
        pass

    # ---- Insertion + annealing -----------------------------------------------
    while best_adj is not None and best_n < moore and time.monotonic() < deadline - 0.5:
        try:
            cadj = [set(s) for s in best_adj]
            ccol = list(best_col)
            N2 = _insert(best_n, cadj, ccol, d, D, rng)
            _saturate(N2, cadj, ccol, d, rng)
            slice_end = min(deadline, time.monotonic() + max(2.0, 0.06 * T))
            cost = _anneal(N2, cadj, ccol, d, D, rng, slice_end, 1500)
            if cost == 0:
                E = _to_edges(N2, cadj, ccol)
                if lib.is_valid(N2, E, d, D):
                    best_n, best_e = N2, E
                    best_adj, best_col = cadj, ccol
        except Exception:
            pass

    if lib.is_valid(best_n, best_e, d, D):
        return best_n, best_e
    return lib.haar_graph(d, range(d))
