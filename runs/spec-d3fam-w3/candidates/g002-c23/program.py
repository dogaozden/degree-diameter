import math
import random
import time

import lib


def _moore(d, D):
    """Moore-type upper bound on the order of a bipartite graph with max degree d and diameter D."""
    if D == 0 or d == 0:
        return 1
    if d == 1:
        return min(2, D + 1)
    if d == 2:
        return 2 * D
    return 2 * sum((d - 1) ** i for i in range(D))


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


def _augment(n, edges, d, D, rng, deadline):
    """Add two vertices (a point P and a line L) via degree-preserving 2-switch annealing.

    Returns (n+2, edges) with diameter <= D, or None if the search fails before the deadline.
    Bipartiteness is kept: every edge is stored as (colour-0 vertex, colour-1 vertex).
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


# ----------------------------------------------------------------------------
# Bi-Cayley (Haar) graphs from difference covers (diameter 3).
#
# S a d-subset of Z_m with S - S = Z_m gives a d-regular bipartite Haar graph
# a_x ~ b_y iff y - x in S, of diameter <= 3. A difference cover is necessary for
# diameter 3 in any Haar graph, so we anneal S to cover all residues.
# ----------------------------------------------------------------------------

def _cover_search(m, d, rng, deadline, iters):
    """Anneal a d-subset S of Z_m (0 in S) so that S - S covers Z_m. Returns S or None."""
    S = [0] + rng.sample(range(1, m), d - 1)
    inS = [False] * m
    for s in S:
        inS[s] = True
    cnt = [0] * m
    for i in range(d):
        for j in range(d):
            if i != j:
                cnt[(S[i] - S[j]) % m] += 1
    zeros = sum(1 for x in range(1, m) if cnt[x] == 0)
    exp = math.exp
    rand = rng.random

    for it in range(iters):
        if zeros == 0:
            return S
        if (it & 1023) == 0 and time.monotonic() > deadline:
            break
        T = 0.8 * (0.05 / 0.8) ** (it / iters)
        idx = rng.randrange(1, d)
        old = S[idx]
        new = rng.randrange(1, m)
        if inS[new]:
            continue

        pold = []
        for j in range(d):
            if j != idx:
                t = S[j]
                pold.append((old - t) % m)
                pold.append((t - old) % m)
        z = zeros
        for x in pold:
            cnt[x] -= 1
            if cnt[x] == 0:
                z += 1

        S[idx] = new
        pnew = []
        for j in range(d):
            if j != idx:
                t = S[j]
                pnew.append((new - t) % m)
                pnew.append((t - new) % m)
        for x in pnew:
            if cnt[x] == 0:
                z -= 1
            cnt[x] += 1

        delta = z - zeros
        if delta <= 0 or rand() < exp(-delta / T):
            zeros = z
            inS[old] = False
            inS[new] = True
        else:
            for x in pnew:
                cnt[x] -= 1
            for x in pold:
                cnt[x] += 1
            S[idx] = old

    return S if zeros == 0 else None


def _haar_phase(d, best_n, rng, deadline, consider):
    """Try difference-cover Haar graphs of order 2m for m just above best_n/2, upward.

    A failed m ends the sweep, since larger m is harder to cover.
    """
    m_start = max(d, best_n // 2 + 1)
    m_max = d * (d - 1) + 1
    m = m_start
    while m <= m_max and time.monotonic() < deadline:
        now = time.monotonic()
        budget_end = now + 0.6 * (deadline - now)
        S = None
        while time.monotonic() < budget_end:
            S = _cover_search(m, d, rng, budget_end, 100000)
            if S is not None:
                break
        if S is None:
            break
        consider(*lib.haar_graph(m, S))
        m += 1


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    if not lib.is_valid(best[0], best[1], d, D):
        best = (1, [])
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    if D == 3:
        # Moore-optimal: PG(2, d-1) incidence graph.
        if d - 1 >= 2 and lib.is_prime_power(d - 1):
            consider(*lib.projective_plane_incidence(d - 1))
            return best

        # Araujo-Pardo & Lopez record family (degree d, order 2(q^2+q+5), q = d-2).
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                base = lib.araujo_lopez_graph(d - 2)
                consider(*base)
            except (ValueError, StopIteration, KeyError):
                pass

        # Augment the structured base by two vertices at a time, within a bounded share of time.
        if best_n > 0 and lib.is_valid(best[0], best[1], d, D):
            cur = best
            mb = _moore(d, D)
            now = time.monotonic()
            aug_deadline = now + 0.3 * (deadline - now)
            while time.monotonic() < aug_deadline and cur[0] + 2 <= mb:
                res = _augment(cur[0], cur[1], d, D, rng, aug_deadline)
                if res is None or not lib.is_valid(res[0], res[1], d, D):
                    break
                cur = res
                consider(*cur)

    # Difference-cover Haar search (valid for any D >= 3).
    if d >= 2:
        _haar_phase(d, best_n, rng, deadline, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        fallback = lib.haar_graph(d, range(d))
        if lib.is_valid(fallback[0], fallback[1], d, D):
            return fallback
        return (1, [])
    return best
