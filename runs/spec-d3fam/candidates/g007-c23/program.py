import math
import random
import time

import lib


def _color(n, adj):
    """Two-colour a bipartite graph given as adjacency sets (BFS/DFS from each unseen vertex)."""
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
    """Ordered count of vertex pairs at distance > D (bitmask BFS), computed from adjacency sets."""
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


def _augment(n, edges, d, D, rng, deadline):
    """Add two new vertices (a point P and a line L) using degree-preserving edge switches.

    Returns (n+2, edges) with diameter <= D, or None if the search fails before the deadline.
    """
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
    T = 1.0
    while cur > 0:
        if time.monotonic() >= deadline:
            return None
        i = rng.randrange(M)
        j = rng.randrange(M)
        if i == j:
            continue
        a, b = E[i]
        c, e = E[j]
        if a == c or b == e or e in adj[a] or b in adj[c]:
            continue
        adj[a].discard(b); adj[b].discard(a)
        adj[c].discard(e); adj[e].discard(c)
        adj[a].add(e); adj[e].add(a)
        adj[c].add(b); adj[b].add(c)
        new = _bad_count(N, adj, D)
        if new <= cur or rng.random() < math.exp((cur - new) / T):
            cur = new
            E[i] = (a, e)
            E[j] = (c, b)
        else:
            adj[a].discard(e); adj[e].discard(a)
            adj[c].discard(b); adj[b].discard(c)
            adj[a].add(b); adj[b].add(a)
            adj[c].add(e); adj[e].add(c)
    return N, list(E)


def _structured_base(d, D):
    """Algebraic base graph for D = 3 when available, else None."""
    q = d - 1
    if D == 3 and q >= 2 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)
    return None


def _parent_build(d, D, seed, time_limit):
    """Previous approach: structured base, grown by annealing; random Haar fallback."""
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
    rng = random.Random(seed)

    base = _structured_base(d, D)
    if base is not None:
        n, edges = base
        if lib.is_valid(n, edges, d, D):
            cur = (n, edges)
            mb = _moore(d, D)
            while time.monotonic() < deadline and cur[0] + 2 <= mb:
                res = _augment(cur[0], cur[1], d, D, rng, deadline)
                if res is None:
                    break
                if not lib.is_valid(res[0], res[1], d, D):
                    break
                cur = res
            return cur

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


# ---------------------------------------------------------------------------
# New construction: Haar graphs from difference bases.
#
# Haar graph H(m, S): a_i ~ b_j iff j - i in S (mod m), degree |S| = d.
# Its diameter is <= 3 exactly when S - S covers all of Z_m, since a-a and
# b-b distances are even and every a-to-b odd distance is then also covered.
# So we search for a d-subset of Z_m whose difference set is all of Z_m,
# for m as large as possible, giving order 2m.
# ---------------------------------------------------------------------------

def _sa_difference_cover(m, k, rng, deadline, max_iters):
    """Simulated annealing for a k-subset S of Z_m (0 in S) with S - S = Z_m. Returns S or None."""
    S = [0] + rng.sample(range(1, m), k - 1)
    inS = [False] * m
    for s in S:
        inS[s] = True
    cnt = [0] * m
    for a in S:
        for b in S:
            if a != b:
                cnt[(a - b) % m] += 1
    unc = sum(1 for r in range(1, m) if cnt[r] == 0)
    T = 0.5
    for it in range(max_iters):
        if unc == 0:
            return list(S)
        if (it & 1023) == 0 and time.monotonic() >= deadline:
            return None
        i = rng.randrange(1, k)
        s = S[i]
        x = rng.randrange(1, m)
        if inS[x]:
            continue
        before = unc
        # remove s's differences
        for j in range(k):
            if j == i:
                continue
            b = S[j]
            for r in ((s - b) % m, (b - s) % m):
                cnt[r] -= 1
                if cnt[r] == 0:
                    unc += 1
        # add x's differences
        for j in range(k):
            if j == i:
                continue
            b = S[j]
            for r in ((x - b) % m, (b - x) % m):
                if cnt[r] == 0:
                    unc -= 1
                cnt[r] += 1
        delta = unc - before
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S[i] = x
            inS[s] = False
            inS[x] = True
        else:
            # revert: remove x's differences, restore s's
            for j in range(k):
                if j == i:
                    continue
                b = S[j]
                for r in ((x - b) % m, (b - x) % m):
                    cnt[r] -= 1
                    if cnt[r] == 0:
                        unc += 1
            for j in range(k):
                if j == i:
                    continue
                b = S[j]
                for r in ((s - b) % m, (b - s) % m):
                    if cnt[r] == 0:
                        unc -= 1
                    cnt[r] += 1
    return list(S) if unc == 0 else None


def _haar_search(d, D, base_n, rng, deadline):
    """Find the largest m > base_n/2 with a valid Haar graph of degree d; return (n, edges) or None."""
    best = None
    m = base_n // 2 + 1
    while True:
        now = time.monotonic()
        if now >= deadline:
            break
        att = now + 0.5 * (deadline - now)
        S = None
        while S is None and time.monotonic() < att:
            S = _sa_difference_cover(m, d, rng, att, 200000)
        if S is None:
            break
        n, edges = lib.haar_graph(m, S)
        if n <= base_n or not lib.is_valid(n, edges, d, D):
            break
        best = (n, edges)
        m += 1
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    candidates = []
    try:
        base = _structured_base(d, D)
    except Exception:
        base = None

    mb = _moore(d, D)
    if (D == 3 and d >= 6 and base is not None and base[0] < mb
            and lib.is_valid(base[0], base[1], d, D)):
        try:
            haar = _haar_search(d, D, base[0], rng, start + 0.7 * time_limit)
            if haar is not None:
                candidates.append(haar)
        except Exception:
            pass

    remaining = start + 0.9 * time_limit - time.monotonic()
    try:
        candidates.append(_parent_build(d, D, seed, max(remaining, 0.5)))
    except Exception:
        pass

    candidates.sort(key=lambda t: t[0], reverse=True)
    for n, edges in candidates:
        if lib.is_valid(n, edges, d, D):
            return n, edges
    return 1, []
