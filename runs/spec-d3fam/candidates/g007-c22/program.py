import math
import random
import time

import lib


def _color(n, adj):
    """Two-colour a bipartite graph given as adjacency sets (DFS from each unseen vertex)."""
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
    """Add two vertices (a point P and a line L) by degree-preserving 2-switch annealing.

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


# ---------------------------------------------------------------------------
# New construction: Haar graphs of Z_m from difference covers.
#
# Haar graph H(Z_m, S): a_g ~ b_{g+s} for s in S, |S| = k = d, so it is bipartite
# and d-regular with 2m vertices. With 0 in S, diameter <= 3 holds iff
#   (i)  S - S covers Z_m   (same-side pairs, distance 2), and
#   (ii) S U (S - S + S) covers Z_m   (cross pairs, distance 1 or 3).
# We search for such S by simulated annealing and try to beat the augmented
# structured base by using a larger m.
# ---------------------------------------------------------------------------

def _cover_cost(m, S):
    """Number of residues missing from the difference cover plus cross-condition cover."""
    Sset = set(S)
    D1 = {(a - b) % m for a in S for b in S if a != b}
    D3 = {(a - b + c) % m for a in S for b in S for c in S}
    return (m - 1 - len(D1)) + (m - len(D3 | Sset))


def _cover_search(m, k, rng, deadline, steps):
    """Anneal a k-subset S of Z_m (containing 0) to zero cover cost. Returns S or None."""
    S = [0] + rng.sample(range(1, m), k - 1)
    cur = _cover_cost(m, S)
    T = 0.6
    for step in range(steps):
        if cur == 0:
            return S
        if step % 64 == 0 and time.monotonic() >= deadline:
            break
        i = rng.randrange(1, k)
        x = rng.randrange(m)
        if x in S:
            continue
        old = S[i]
        S[i] = x
        new = _cover_cost(m, S)
        if new <= cur or rng.random() < math.exp((cur - new) / T):
            cur = new
        else:
            S[i] = old
    return list(S) if cur == 0 else None


def _haar_improve(d, D, best, rng, deadline):
    """Try Haar graphs of Z_m with m just above the current order's half, growing while successful."""
    n0, _ = best
    k = d
    m = n0 // 2 + 1
    mmax = k * (k - 1) + 1          # same-side difference-cover bound
    mb = _moore(d, D) // 2          # order cap from the Moore-type bound
    cur = best
    while m <= mmax and 2 * m <= mb and time.monotonic() < deadline:
        found = None
        while time.monotonic() < deadline and found is None:
            S = _cover_search(m, k, rng, deadline, steps=4000)
            if S is None:
                continue
            n, edges = lib.haar_graph(m, S)
            if lib.is_valid(n, edges, d, D):
                found = (n, edges)
        if found is None:
            break
        cur = found
        m += 1
    return cur


def _safe_base(d, D):
    """Always-valid small fallback graph."""
    if d == 0 or D == 0:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    return lib.haar_graph(d, range(d))   # K_{d,d}, diameter 2


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, 0.8 * time_limit - 0.5)
    deadline = start + budget
    rng = random.Random(seed)

    best = _safe_base(d, D)

    # Structured base for D = 3.
    base = None
    q = d - 1
    if D == 3 and q >= 2 and lib.is_prime_power(q):
        base = lib.projective_plane_incidence(q)
    elif D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        base = lib.araujo_lopez_graph(d - 2)

    if base is not None and lib.is_valid(base[0], base[1], d, D):
        best = base
        if D == 3 and d >= 3:
            # Short augmentation phase (parent-style), then the new difference-cover search.
            p1 = start + 0.2 * budget
            cur = best
            mb = _moore(d, D)
            while time.monotonic() < p1 and cur[0] + 2 <= mb:
                res = _augment(cur[0], cur[1], d, D, rng, p1)
                if res is None or not lib.is_valid(res[0], res[1], d, D):
                    break
                cur = res
            best = cur
            improved = _haar_improve(d, D, best, rng, deadline)
            if improved[0] > best[0] and lib.is_valid(improved[0], improved[1], d, D):
                best = improved
    else:
        # General fallback: random Haar graphs over growing m.
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
                if found[0] > best[0]:
                    best = found
                misses = 0
            else:
                misses += 1
            m += 1

    if lib.is_valid(best[0], best[1], d, D):
        return best
    return _safe_base(d, D)
