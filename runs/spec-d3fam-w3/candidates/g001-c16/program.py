import math
import random
import time

import numpy as np

import lib


def _color(n, adj):
    """Two-colour a bipartite graph given as adjacency sets."""
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
    """Ordered count of vertex pairs at distance > D (bitmask BFS)."""
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
    """Add two vertices (a point P and a line L) via degree-preserving 2-switch annealing.

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


# ------------------------------------------------ group Haar graphs for D = 3
#
# Group Haar graph H(G, S): a_x ~ b_{x s} for s in S, |S| = d, |G| = N, so 2N vertices,
# d-regular and bipartite. Left multiplication is an automorphism that is transitive on
# each side, so diameter <= 3 holds iff, with T = S and T = S^{-1}:
#   T T^{-1} = G                      (same-side pairs at distance 2)
#   T ∪ T T^{-1} T = G                (opposite-side pairs at distance 1 or 3)
# Abelian groups need only the T = S test, since the second is its negation.
#
# New routine: the group is Z_m x|_r Z_k, enumerated by order N. Tables are built once,
# and an annealer searches S minimising the number of uncovered group elements.

def _group_candidates(N, rng, limit):
    """Semidirect groups Z_m x|_r Z_k of order N (cyclic ones first), shuffled within each class."""
    cands = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                cands.append((m, k, r))
    rng.shuffle(cands)
    cyc = [c for c in cands if c[1] == 1]
    rest = [c for c in cands if c[1] != 1]
    return (cyc + rest)[:limit]


def _mul_table(N, mul):
    """Full multiplication table of a group with identity 0."""
    M = np.empty((N, N), dtype=np.int64)
    for x in range(N):
        for y in range(N):
            M[x, y] = mul(x, y)
    return M


def _cond(T, M, inv, N):
    """Uncovered count for: T T^{-1} = G and T ∪ T T^{-1} T = G."""
    diffs = np.unique(M[T[:, None], inv[T][None, :]])
    c1 = N - len(diffs)
    trip = M[diffs[:, None], T[None, :]].ravel()
    cov = np.zeros(N, dtype=bool)
    cov[trip] = True
    cov[T] = True
    c2 = N - int(cov.sum())
    return c1 + c2


def _group_cost(S, M, inv, N):
    """Total uncovered count for S (both S and S^{-1} conditions)."""
    return _cond(S, M, inv, N) + _cond(inv[S], M, inv, N)


def _anneal_group(d, N, M, inv, rng, deadline):
    """Find a d-subset S of G with zero group-Haar cost, or None before the deadline."""
    S = np.array(rng.sample(range(N), d), dtype=np.int64)
    inS = set(int(x) for x in S)
    cost = _group_cost(S, M, inv, N)
    T = 0.8
    steps = 0
    while cost > 0:
        if steps % 64 == 0 and time.monotonic() >= deadline:
            return None
        steps += 1
        i = rng.randrange(d)
        new = rng.randrange(N)
        if new in inS:
            continue
        S2 = S.copy()
        S2[i] = new
        c2 = _group_cost(S2, M, inv, N)
        if c2 <= cost or rng.random() < math.exp((cost - c2) / T):
            inS.discard(int(S[i]))
            inS.add(new)
            S, cost = S2, c2
    return S


def _haar_group_edges(N, M, S):
    """Edges of H(G, S): a_x (vertex x) ~ b_{x s} (vertex N + x*s)."""
    edges = []
    for x in range(N):
        for s in S:
            edges.append((x, N + int(M[x, s])))
    return edges


def _group_phase(d, best, rng, deadline):
    """Escalate the group order N upward from the current best, keeping valid improvements."""
    best_n, best_edges = best
    N = best_n // 2 + 1
    hi = d * d - d + 1  # covering S S^{-1} = G needs |G| <= d^2 - d + 1
    while N <= hi:
        if time.monotonic() >= deadline:
            break
        cands = _group_candidates(N, rng, 6)
        found = None
        for (m, k, r) in cands:
            now = time.monotonic()
            if now >= deadline:
                break
            sub = min(deadline, now + max(1.0, 0.3 * (deadline - now)))
            order, mul, _ = lib.semidirect_group(m, k, r)
            M = _mul_table(order, mul)
            inv = np.argmax(M == 0, axis=1)
            S = _anneal_group(d, order, M, inv, rng, sub)
            if S is None:
                continue
            n = 2 * order
            edges = _haar_group_edges(order, M, S)
            if n > best_n and lib.is_valid(n, edges, d, 3):
                found = (n, edges)
                break
        if found is None:
            break
        best_n, best_edges = found
        N += 1
    return best_n, best_edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 <= D.
    kdd = lib.haar_graph(d, range(d))
    if not lib.is_valid(kdd[0], kdd[1], d, D):
        kdd = (1, [])
    best = kdd

    if D == 3:
        base = None
        q = d - 1
        if q >= 2 and lib.is_prime_power(q):
            base = lib.projective_plane_incidence(q)
        elif d - 2 >= 3 and lib.is_prime_power(d - 2):
            base = lib.araujo_lopez_graph(d - 2)

        base_ok = base is not None and lib.is_valid(base[0], base[1], d, D)
        if base_ok and base[0] > best[0]:
            best = base
        base_n = best[0]

        # New: group Haar search over semidirect products, escalating the order past the best.
        if d >= 2:
            n2, e2 = _group_phase(d, best, rng, start + 0.7 * time_limit)
            if n2 > best[0] and lib.is_valid(n2, e2, d, D):
                best = (n2, e2)

        # Augmentation of the structured base, only if the group phase did not improve on it.
        if base_ok and best[0] <= base_n:
            cur = base
            mb = _moore(d, D)
            aug_deadline = start + 0.8 * time_limit
            while time.monotonic() < aug_deadline and cur[0] + 2 <= mb:
                res = _augment(cur[0], cur[1], d, D, rng, aug_deadline)
                if res is None:
                    break
                if not lib.is_valid(res[0], res[1], d, D):
                    break
                cur = res
            if lib.is_valid(cur[0], cur[1], d, D) and cur[0] > best[0]:
                best = cur
    else:
        # Random Haar fallback for other diameters.
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
                if found[0] > best[0] and lib.is_valid(found[0], found[1], d, D):
                    best = found
                misses = 0
            else:
                misses += 1
            m += 1

    if not lib.is_valid(best[0], best[1], d, D):
        return kdd
    return best
