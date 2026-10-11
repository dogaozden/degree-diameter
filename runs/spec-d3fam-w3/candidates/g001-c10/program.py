import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Utilities (shared with the parent program).
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
# Base constructions (parent).
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
# NEW CONSTRUCTION for D = 3: cyclic Haar graphs from difference covers.
#
# Haar graph H(Z_m, S), |S| = k: a_i ~ b_{i+s} for s in S. Degree is exactly k.
#   * Two same-side vertices a_i, a_j are at distance 2 iff j - i is a difference
#     s - t with s != t in S. So we need S - S to cover all nonzero residues.
#   * Opposite-side vertices are at distance <= 3 iff the difference lies in
#     S U (S - S + S). This is almost always satisfied and is checked exactly.
# So any "difference cover" S of size k in Z_m gives a valid graph on 2m
# vertices with diameter 3. Since k(k-1)+1 >= m is necessary, the order can
# reach 2(k^2 - k + 1), close to the Moore bound. We search for the largest m.
# ----------------------------------------------------------------------------

def _uncovered(S, m):
    """Number of nonzero residues not expressible as s - t with s != t in S."""
    cnt = [0] * m
    k = len(S)
    for i in range(k):
        si = S[i]
        for j in range(k):
            if i != j:
                cnt[(si - S[j]) % m] += 1
    return sum(1 for r in range(1, m) if cnt[r] == 0)


def _find_cover(m, k, rng, deadline, max_iters):
    """Anneal a size-k subset of Z_m (containing 0) whose differences cover Z_m."""
    if k > m:
        return None
    S = [0] + rng.sample(range(1, m), k - 1)
    cur = _uncovered(S, m)
    it = 0
    while cur > 0 and it < max_iters:
        if (it & 255) == 0 and time.monotonic() >= deadline:
            return None
        it += 1
        i = rng.randrange(1, k)
        x = rng.randrange(1, m)
        if x in S:
            continue
        S2 = S[:]
        S2[i] = x
        nu = _uncovered(S2, m)
        if nu <= cur or rng.random() < math.exp(-(nu - cur) / 0.4):
            S = S2
            cur = nu
    if cur == 0:
        return sorted(S)
    return None


def _best_base(d):
    best = None
    for n_b, e_b in _bases(d, 3):
        if lib.is_valid(n_b, e_b, d, 3) and (best is None or n_b > best[0]):
            best = (n_b, e_b)
    return best


def _build_d3_cover(d, seed, deadline):
    """Best of the structured base and the largest cyclic Haar graph found by search."""
    k = d
    rng = random.Random(seed)
    best = _best_base(d)
    if best is None:
        kk = lib.haar_graph(k, range(k))
        if lib.is_valid(kk[0], kk[1], d, 3):
            best = kk
    if best is None:
        return None
    best_m = best[0] // 2

    m_max = k * (k - 1) + 1
    m = best_m + 1
    fails = 0
    while m <= m_max and fails < 2 and time.monotonic() < deadline:
        now = time.monotonic()
        md = min(deadline, now + max(1.0, 0.3 * (deadline - now)))
        S = _find_cover(m, k, rng, md, 200000)
        if S is not None:
            n, edges = lib.haar_graph(m, S)
            if lib.is_valid(n, edges, d, 3):
                best = (n, edges)
                fails = 0
                m += 1
                continue
        fails += 1
        m += 1
    return best


# ----------------------------------------------------------------------------
# Parent driver (used for D != 3 and as the safe fallback).
# ----------------------------------------------------------------------------

def _parent_build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    if D == 2:
        return lib.haar_graph(d, range(d))

    cur = _best_base(d) if D == 3 else None
    if cur is None:
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
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d >= 3 and D == 3:
        try:
            res = _build_d3_cover(d, seed, start + 0.75 * time_limit)
            if res is not None and lib.is_valid(res[0], res[1], d, D):
                return res
        except Exception:
            pass
        return _parent_build(d, D, seed, 0.2 * time_limit)
    return _parent_build(d, D, seed, time_limit)
