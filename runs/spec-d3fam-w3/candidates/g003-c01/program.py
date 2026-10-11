import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Utilities.
# ----------------------------------------------------------------------------

def _color(n, adj):
    """Two-colour a bipartite graph given as adjacency collections."""
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


def _bad_count(n, adj, D):
    """Ordered number of vertex pairs at distance > D (zero iff diameter <= D and connected)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach)


def _moore(d, D):
    """Moore-type upper bound on the order of a bipartite graph with max degree d and diameter D."""
    if D == 0 or d == 0:
        return 1
    if d == 1:
        return min(2, D + 1)
    if d == 2:
        return 2 * D
    return 2 * sum((d - 1) ** i for i in range(D))


def _smallest_pp_at_least(x):
    """Smallest prime power >= max(2, x)."""
    q = max(2, x)
    while not lib.is_prime_power(q):
        q += 1
    return q


# ----------------------------------------------------------------------------
# Base constructions (parent's).
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

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _bases(d, D):
    """Candidate structured base graphs (already diameter <= D by construction)."""
    out = []
    if D == 3:
        q = d - 1
        if q >= 2 and lib.is_prime_power(q):
            out.append(lib.projective_plane_incidence(q))
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                out.append(lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass
    elif D == 4:
        for q in range(min(d - 1, 7), 1, -1):
            if lib.is_prime_power(q):
                out.append(_gq_w(q))
                break
    return out


# ----------------------------------------------------------------------------
# Saturation (adding edges never increases distances).
# ----------------------------------------------------------------------------

def _saturate(n, edges, d, rng):
    """Join deficient opposite-side vertices in random order while degrees stay <= d."""
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    col = _color(n, adj)
    deg = [len(s) for s in adj]
    left = [v for v in range(n) if col[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if col[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right if b not in adj[a]]
    rng.shuffle(pairs)
    E = list(edges)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d and b not in adj[a]:
            adj[a].add(b)
            adj[b].add(a)
            deg[a] += 1
            deg[b] += 1
            E.append((a, b))
    return E


# ----------------------------------------------------------------------------
# Parent's vertex augmentation (2-switch anneal adding a point and a line).
# ----------------------------------------------------------------------------

def _augment(n, edges, d, D, rng, deadline, iters):
    """Return (n+2, edges) with diameter <= D, or None if the anneal fails."""
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    col = _color(n, adj)

    P, L = n, n + 1
    adj.append(set())
    adj.append(set())
    N = n + 2

    oriented = [((u, v) if col[u] == 0 else (v, u)) for u, v in edges]
    rng.shuffle(oriented)
    used, pick = set(), []
    for idx, (a, b) in enumerate(oriented):
        if a not in used and b not in used:
            pick.append(idx)
            used.add(a)
            used.add(b)
            if len(pick) == d:
                break
    if len(pick) < d:
        return None

    picked = set(pick)
    E = [oriented[i] for i in range(len(oriented)) if i not in picked]
    for idx in pick:
        a, b = oriented[idx]
        adj[a].discard(b)
        adj[b].discard(a)
        adj[a].add(P)
        adj[P].add(a)
        adj[b].add(L)
        adj[L].add(b)
        E.append((a, P))
        E.append((L, b))

    M = len(E)
    cur = _bad_count(N, adj, D)
    for it in range(iters):
        if cur == 0:
            break
        if time.monotonic() >= deadline:
            return None
        T = 0.8 * (0.02 ** (it / iters))
        i = rng.randrange(M)
        j = rng.randrange(M)
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
        new = _bad_count(N, adj, D)
        if new <= cur or rng.random() < math.exp((cur - new) / T):
            cur = new
            E[i] = (a, e)
            E[j] = (c, b)
        else:
            adj[a].discard(e)
            adj[e].discard(a)
            adj[c].discard(b)
            adj[b].discard(c)
            adj[a].add(b)
            adj[b].add(a)
            adj[c].add(e)
            adj[e].add(c)
    if cur != 0:
        return None
    return N, E


# ----------------------------------------------------------------------------
# Haar random search fallback.
# ----------------------------------------------------------------------------

def _haar_fallback(d, D, rng, deadline):
    best = lib.haar_graph(d, range(d))
    m, misses = d + 1, 0
    while time.monotonic() < deadline and misses < 10:
        found = None
        for _ in range(30):
            if time.monotonic() >= deadline:
                break
            S = [0] + rng.sample(range(1, m), d - 1)
            n, edges = lib.haar_graph(m, S)
            if lib.within_diameter(n, edges, D):
                found = (n, edges)
                break
        if found:
            best, misses = found, 0
        else:
            misses += 1
        m += 1
    return best


# ----------------------------------------------------------------------------
# BOLD branch: different construction for D = 3.
# Start from PG(2,q0) with q0 the smallest prime power >= d-1 (degree q0+1 >= d).
# Greedily delete vertices until max degree <= d, delete extra random vertices to
# reach a target order, saturate spare degree, then anneal with degree-preserving
# 2-switches until the diameter is <= D.
# ----------------------------------------------------------------------------

def _anneal(n, E, D, rng, deadline, iters):
    """Degree-preserving 2-switch anneal on bipartite edge list E until diameter <= D."""
    adj = [set() for _ in range(n)]
    for u, v in E:
        adj[u].add(v)
        adj[v].add(u)
    col = _color(n, adj)
    E = [((u, v) if col[u] == 0 else (v, u)) for u, v in E]
    M = len(E)
    if M == 0:
        return None
    cur = _bad_count(n, adj, D)
    for it in range(iters):
        if cur == 0:
            break
        if time.monotonic() >= deadline:
            return None
        T = 0.8 * (0.02 ** (it / iters))
        i = rng.randrange(M)
        j = rng.randrange(M)
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
        new = _bad_count(n, adj, D)
        if new <= cur or rng.random() < math.exp((cur - new) / T):
            cur = new
            E[i] = (a, e)
            E[j] = (c, b)
        else:
            adj[a].discard(e)
            adj[e].discard(a)
            adj[c].discard(b)
            adj[b].discard(c)
            adj[a].add(b)
            adj[b].add(a)
            adj[c].add(e)
            adj[e].add(c)
    if cur != 0:
        return None
    return n, E


def _attempt(d, D, n0, E0, target, rng, deadline):
    """Try to build a valid graph of exactly `target` vertices from PG(2,q0) by deletion + anneal."""
    nb = [set() for _ in range(n0)]
    for u, v in E0:
        nb[u].add(v)
        nb[v].add(u)
    alive = [True] * n0
    deg = [len(s) for s in nb]

    def remove(w):
        alive[w] = False
        for x in nb[w]:
            if alive[x]:
                deg[x] -= 1

    # Degree fix: every surviving vertex must have degree <= d.
    while True:
        over = [v for v in range(n0) if alive[v] and deg[v] > d]
        if not over:
            break
        v = rng.choice(over)
        cands = [u for u in nb[v] if alive[u]]
        if not cands:
            return None
        remove(rng.choice(cands))

    live = [v for v in range(n0) if alive[v]]
    if len(live) < target:
        return None
    rng.shuffle(live)
    while len(live) > target:
        w = live.pop()
        remove(w)

    idx = {v: i for i, v in enumerate(live)}
    n = len(live)
    E = []
    for u in live:
        for v in nb[u]:
            if alive[v] and u < v:
                E.append((idx[u], idx[v]))
    E = _saturate(n, E, d, rng)
    return _anneal(n, E, D, rng, deadline, iters=20000)


def _bold(d, D, rng, deadline, floor_n):
    """Increase target order from floor_n upward while attempts succeed. Returns (n, edges) or None."""
    q0 = _smallest_pp_at_least(d - 1)
    n0, E0 = lib.projective_plane_incidence(q0)
    mb = _moore(d, D)
    best = None
    target = floor_n + 2
    while time.monotonic() < deadline and target <= mb:
        remaining = deadline - time.monotonic()
        attempt_deadline = min(deadline, time.monotonic() + max(3.0, 0.5 * remaining))
        res = _attempt(d, D, n0, E0, target, rng, attempt_deadline)
        if res is None:
            break
        if not lib.is_valid(res[0], res[1], d, D):
            break
        best = res
        target += 2
    return best


# ----------------------------------------------------------------------------
# Parent pipeline (safe fallback).
# ----------------------------------------------------------------------------

def _parent(d, D, rng, deadline):
    cur = None
    for n_b, e_b in _bases(d, D):
        if lib.is_valid(n_b, e_b, d, D) and (cur is None or n_b > cur[0]):
            cur = (n_b, e_b)

    if cur is None:
        best = _haar_fallback(d, D, rng, deadline)
        if lib.is_valid(best[0], best[1], d, D):
            return best
        return lib.haar_graph(d, range(d))

    sat_edges = _saturate(cur[0], cur[1], d, rng)
    if lib.is_valid(cur[0], sat_edges, d, D):
        cur = (cur[0], sat_edges)

    mb = _moore(d, D)
    while time.monotonic() < deadline and cur[0] + 2 <= mb:
        res = _augment(cur[0], cur[1], d, D, rng, deadline, iters=2000)
        if res is None:
            continue
        if not lib.is_valid(res[0], res[1], d, D):
            break
        cur = res

    if not lib.is_valid(cur[0], cur[1], d, D):
        return lib.haar_graph(d, range(d))
    return cur


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    if D == 2:
        return lib.haar_graph(d, range(d))

    # Parent result first, with a modest share of the budget, as the safe fallback.
    parent_share = 0.25 if D == 3 else 1.0
    parent = _parent(d, D, rng, start + parent_share * total)
    if not lib.is_valid(parent[0], parent[1], d, D):
        parent = lib.haar_graph(d, range(d))

    # Bold branch for D = 3: different construction, uses the remaining budget.
    if D == 3 and d >= 3:
        try:
            bold = _bold(d, D, rng, start + total, parent[0])
        except Exception:
            bold = None
        if bold is not None and bold[0] > parent[0] and lib.is_valid(bold[0], bold[1], d, D):
            return bold

    return parent
