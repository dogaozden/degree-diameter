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


# ----------------------------------------------------------------------------
# Base constructions.
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
            out.append(lib.projective_plane_incidence(q))        # 2(q^2+q+1), degree q+1
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                out.append(lib.araujo_lopez_graph(d - 2))         # 2(q^2+q+5), degree q+2 = d
            except Exception:
                pass
    elif D == 4:
        for q in range(min(d - 1, 7), 1, -1):
            if lib.is_prime_power(q):
                out.append(_gq_w(q))
                break
    return out


def _pg_base(d):
    """NEW: PG(2,q) incidence with q the largest prime power with q+1 <= d.

    Unlike the Araujo-Lopez base, this graph has spare degree on every vertex
    (its degree is q+1 < d), so it can be filled to exact degree d and then grown
    by augmentation. It is a second, independent starting point for the search.
    """
    q = d - 1
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    if q < 2:
        return None
    return lib.projective_plane_incidence(q)


# ----------------------------------------------------------------------------
# NEW: degree filling with diameter-preserving repair.
# Phase 1 adds random opposite-side edges while both ends have spare degree.
# Phase 2 repairs leftover deficient pairs (a, b) with a 2-switch: remove an
# edge (x, y), add (a, y) and (x, b). Degrees of x and y are unchanged, a and b
# each gain one, and the switch is kept only if the diameter stays <= D.
# ----------------------------------------------------------------------------

def _fill(n, edges, d, D, rng, deadline, switch_tries=600):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    col = _color(n, adj)
    E = [((u, v) if col[u] == 0 else (v, u)) for u, v in edges]
    deg = [len(s) for s in adj]
    left = [v for v in range(n) if col[v] == 0]
    right = [v for v in range(n) if col[v] == 1]

    pairs = [(a, b) for a in left if deg[a] < d for b in right
             if deg[b] < d and b not in adj[a]]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d and b not in adj[a]:
            adj[a].add(b)
            adj[b].add(a)
            deg[a] += 1
            deg[b] += 1
            E.append((a, b))

    tries = 0
    while tries < switch_tries and time.monotonic() < deadline:
        da = [a for a in left if deg[a] < d]
        db = [b for b in right if deg[b] < d]
        if not da or not db:
            break
        a = rng.choice(da)
        b = rng.choice(db)
        tries += 1
        if b in adj[a]:
            continue
        i = rng.randrange(len(E))
        x, y = E[i]
        if x == a or y == b or y in adj[a] or x in adj[b]:
            continue
        adj[x].discard(y)
        adj[y].discard(x)
        adj[a].add(y)
        adj[y].add(a)
        adj[x].add(b)
        adj[b].add(x)
        if _bad_count(n, adj, D) == 0:
            deg[a] += 1
            deg[b] += 1
            E[i] = (a, y)
            E.append((x, b))
        else:
            adj[a].discard(y)
            adj[y].discard(a)
            adj[x].discard(b)
            adj[b].discard(x)
            adj[x].add(y)
            adj[y].add(x)
    return E


# ----------------------------------------------------------------------------
# Vertex augmentation: add a point P and a line L via degree-preserving
# 2-switches, annealing the number of pairs at distance > D to zero.
# ----------------------------------------------------------------------------

def _augment(n, edges, d, D, rng, deadline, iters):
    """Return (n+2, edges) with diameter <= D, or None if the anneal fails."""
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    col = _color(n, adj)

    P, L = n, n + 1           # P has colour 1 (neighbours colour 0); L has colour 0
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
# Haar graph random search (fallback for cases without a structured base).
# ----------------------------------------------------------------------------

def _haar_fallback(d, D, rng, deadline):
    best = lib.haar_graph(d, range(d))          # K_{d,d}: always valid for D >= 2
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
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    if D == 2:
        return lib.haar_graph(d, range(d))

    fallback = lib.haar_graph(d, range(d))

    # Candidate bases: the structured ones, plus the new PG-based one for D = 3.
    bases = list(_bases(d, D))
    if D == 3:
        pg = _pg_base(d)
        if pg is not None:
            bases.append(pg)

    # Fill each valid base to full degree, keeping it only if still valid.
    pool = []  # each entry: [n, edges, consecutive failures]
    for n_b, e_b in bases:
        if not lib.is_valid(n_b, e_b, d, D):
            continue
        filled = _fill(n_b, e_b, d, D, rng, deadline)
        if not lib.is_valid(n_b, filled, d, D):
            filled = e_b
        pool.append([n_b, filled, 0])

    if not pool:
        best = _haar_fallback(d, D, rng, deadline)
        if lib.is_valid(best[0], best[1], d, D):
            return best
        return fallback

    best = max(((s[0], s[1]) for s in pool), key=lambda t: t[0])

    # Round-robin augmentation: each live candidate gets one attempt per round,
    # so the candidates with different starting points share the time budget.
    mb = _moore(d, D)
    active = list(pool)
    while time.monotonic() < deadline and active:
        for st in list(active):
            if time.monotonic() >= deadline:
                break
            if st[0] + 2 > mb:
                active = [s for s in active if s is not st]
                continue
            res = _augment(st[0], st[1], d, D, rng, deadline, iters=800)
            if res is None:
                st[2] += 1
                if st[2] >= 40:
                    active = [s for s in active if s is not st]
                continue
            if not lib.is_valid(res[0], res[1], d, D):
                active = [s for s in active if s is not st]
                continue
            st[0], st[1], st[2] = res[0], res[1], 0
            if st[0] > best[0]:
                best = (st[0], st[1])

    if not lib.is_valid(best[0], best[1], d, D):
        return fallback
    return best
