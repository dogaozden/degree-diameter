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


def _build_adj(N, E):
    adj = [set() for _ in range(N)]
    for a, b in E:
        adj[a].add(b)
        adj[b].add(a)
    return adj


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


# ----------------------------------------------------------------------------
# Degree-respecting saturation: adding edges never increases distances.
# ----------------------------------------------------------------------------

def _saturate(n, edges, d, rng):
    """Join deficient opposite-side vertices in random order while degrees stay <= d."""
    adj = _build_adj(n, edges)
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
# Vertex augmentation: add a point P and a line L via degree-preserving
# 2-switches, annealing the number of pairs at distance > D to zero.
#
# Change: several random initial configurations are generated and the one
# with the fewest bad pairs is annealed, instead of trusting a single pick.
# ----------------------------------------------------------------------------

def _initial_config(oriented, n, d, D, rng, trials):
    """Try several random degree-respecting seedings of P and L; return the best (cur, E, adj)."""
    N = n + 2
    P, L = n, n + 1
    best = None
    for _ in range(trials):
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
            continue
        picked = set(pick)
        E = [oriented[i] for i in range(len(oriented)) if i not in picked]
        for idx in pick:
            a, b = oriented[idx]
            E.append((a, P))   # a colour 0, P colour 1
            E.append((L, b))   # L colour 0, b colour 1
        adj = _build_adj(N, E)
        c = _bad_count(N, adj, D)
        if best is None or c < best[0]:
            best = (c, E, adj)
    return best


def _augment(n, edges, d, D, rng, deadline, iters, trials=6):
    """Return (n+2, edges) with diameter <= D, or None if the anneal fails."""
    adj0 = _build_adj(n, edges)
    col = _color(n, adj0)
    N = n + 2
    oriented = [((u, v) if col[u] == 0 else (v, u)) for u, v in edges]  # (colour0, colour1)

    best = _initial_config(oriented, n, d, D, rng, trials)
    if best is None:
        return None
    cur, E, adj = best
    M = len(E)

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
        # 2-switch: (a,b),(c,e) -> (a,e),(c,b); keeps degrees and bipartiteness.
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

    # Best valid structured base.
    cur = None
    for n_b, e_b in _bases(d, D):
        if lib.is_valid(n_b, e_b, d, D) and (cur is None or n_b > cur[0]):
            cur = (n_b, e_b)

    if cur is None:
        best = _haar_fallback(d, D, rng, deadline)
        if lib.is_valid(best[0], best[1], d, D):
            return best
        return lib.haar_graph(d, range(d))

    # Use spare degree (diameter-safe), then grow by augmentation.
    sat_edges = _saturate(cur[0], cur[1], d, rng)
    if lib.is_valid(cur[0], sat_edges, d, D):
        cur = (cur[0], sat_edges)

    mb = _moore(d, D)
    # Anneal budget grows after each failure, so hard steps get longer searches.
    iters = 3000
    while time.monotonic() < deadline and cur[0] + 2 <= mb:
        res = _augment(cur[0], cur[1], d, D, rng, deadline, iters=iters)
        if res is None:
            iters = min(iters * 2, 60000)
            continue
        if not lib.is_valid(res[0], res[1], d, D):
            break
        cur = res
        iters = 3000

    if not lib.is_valid(cur[0], cur[1], d, D):
        return lib.haar_graph(d, range(d))
    return cur
