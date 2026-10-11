import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Helpers for bipartite graphs stored as adjacency sets.
# ----------------------------------------------------------------------------

def _to_sets(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return adj


def _sides(n, adj):
    """Proper 2-colouring of a bipartite graph (list of 0/1), or None if not bipartite."""
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
                elif color[v] == color[u]:
                    return None
    return color


def _bad(n, adj, D):
    """Number of unordered pairs at distance > D (unreachable pairs included)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        nxt = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            nxt.append(r)
        reach = nxt
    return sum(n - r.bit_count() for r in reach) // 2


# ----------------------------------------------------------------------------
# NEW IDEA: matching-swap vertex insertion ("edge-switch extension").
#
# Pick a matching M = {(a_i, b_i)} of d edges (a_i in side 0, b_i in side 1)
# of the current bipartite graph G. Delete M and add two new vertices:
#   A* (side 0) joined to all b_i, and B* (side 1) joined to all a_i.
# Every old vertex keeps its degree, A* and B* get degree d, and the graph
# stays bipartite. Order grows by 2. Whether the diameter survives depends on
# the choice of M, so we search for M by simulated annealing, minimising the
# number of pairs at distance > D. Success is confirmed with lib.is_valid.
# ----------------------------------------------------------------------------

def _matching_graph(n, adj, M):
    adj2 = [set(s) for s in adj] + [set(), set()]
    A, B = n, n + 1
    for a, b in M:
        adj2[a].discard(b)
        adj2[b].discard(a)
        adj2[A].add(b)
        adj2[b].add(A)
        adj2[B].add(a)
        adj2[a].add(B)
    return n + 2, adj2


def _greedy_matching(E, d, rng):
    order = E[:]
    rng.shuffle(order)
    used = set()
    M = []
    for a, b in order:
        if a in used or b in used:
            continue
        M.append((a, b))
        used.add(a)
        used.add(b)
        if len(M) == d:
            return M
    return None


def _search_matching(n, adj, color, E, d, D, rng, deadline, steps=3000):
    """Anneal a size-d matching so that the matching-swap extension has no bad pairs."""
    def score(M):
        n2, adj2 = _matching_graph(n, adj, M)
        return _bad(n2, adj2, D)

    while time.monotonic() < deadline:
        M = _greedy_matching(E, d, rng)
        if M is None:
            return None
        cur = score(M)
        for it in range(steps):
            if cur == 0:
                return M
            if (it & 31) == 0 and time.monotonic() > deadline:
                return None
            T = 2.0 * (0.05 / 2.0) ** (it / steps)
            i = rng.randrange(d)
            ends = set()
            for j in range(d):
                if j != i:
                    ends.add(M[j][0])
                    ends.add(M[j][1])
            Mset = set(M)
            cand = None
            for _ in range(60):
                e = E[rng.randrange(len(E))]
                if e[0] in ends or e[1] in ends or e in Mset:
                    continue
                cand = e
                break
            if cand is None:
                continue
            newM = M[:]
            newM[i] = cand
            val = score(newM)
            if val <= cur or rng.random() < math.exp(-(val - cur) / T):
                M = newM
                cur = val
    return None


def _extend_once(n, adj, color, d, D, rng, deadline):
    """One successful matching-swap extension, or None."""
    E = [(a, b) for a in range(n) if color[a] == 0 for b in adj[a]]
    if not E:
        return None
    M = _search_matching(n, adj, color, E, d, D, rng, deadline)
    if M is None:
        return None
    n2, adj2 = _matching_graph(n, adj, M)
    edges = [(u, v) for u in range(n2) for v in adj2[u] if u < v]
    if not lib.is_valid(n2, edges, d, D):
        return None
    color2 = color + [0, 1]
    return n2, adj2, color2, edges


# ----------------------------------------------------------------------------
# Difference-cover Haar graphs (from the parent), kept as a fallback family.
# ----------------------------------------------------------------------------

def _cover_search(m, d, rng, deadline, iters):
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
        if delta <= 0 or rand() < math.exp(-delta / T):
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


def _haar_search(d, m_start, deadline, rng, consider):
    m = m_start
    m_max = d * (d - 1) + 1
    while m <= m_max and time.monotonic() < deadline:
        S = None
        while time.monotonic() < deadline:
            S = _cover_search(m, d, rng, deadline, 150000)
            if S is not None:
                break
        if S is None:
            break
        n, e = lib.haar_graph(m, S)
        consider(n, e)
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

    # Safe fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    if D == 3:
        # Moore-optimal: PG(2, d-1) incidence graph. Nothing can be added to it.
        if d - 1 >= 2 and lib.is_prime_power(d - 1):
            consider(*lib.projective_plane_incidence(d - 1))
            return best
        # Araujo-Pardo & Lopez record family when d-2 is a prime power.
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except (ValueError, StopIteration, KeyError):
                pass

    # Difference-cover Haar graphs, a short slice of the budget.
    if d >= 2:
        m_start = max(d, best_n // 2 + 1)
        if m_start <= d * (d - 1) + 1:
            haar_deadline = start + 0.3 * time_limit
            try:
                _haar_search(d, m_start, haar_deadline, rng, consider)
            except Exception:
                pass

    # Matching-swap extension on the best graph found so far.
    try:
        n, edges = best
        adj = _to_sets(n, edges)
        color = _sides(n, adj)
        if color is not None:
            state = (n, adj, color)
            while time.monotonic() < deadline:
                cn, cadj, ccolor = state
                res = _extend_once(cn, cadj, ccolor, d, D, rng, deadline)
                if res is None:
                    break
                n2, adj2, color2, edges2 = res
                state = (n2, adj2, color2)
                consider(n2, edges2)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
