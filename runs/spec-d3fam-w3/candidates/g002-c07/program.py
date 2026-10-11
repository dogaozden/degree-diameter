import math
import random
import time

import numpy as np

import lib

TIME_FRAC = 0.80   # fraction of time_limit used before returning
MARGIN = 2.0       # seconds kept in reserve


# ---------------------------------------------------------------- helpers

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

    Bipartiteness is preserved: every swap keeps side-0 vertices on the first slot.
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
    steps = 0
    while cur > 0:
        if steps % 64 == 0 and time.monotonic() >= deadline:
            return None
        steps += 1
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


# ---------------------------------------------------------------- cyclic Haar search (D = 3)
#
# Haar graph H(m, S): a_i ~ b_{i+s} for s in S, S a d-subset of Z_m with 0 in S.
# Diameter <= 3 iff every x in Z_m is in S-S and every y is in S or S-S+S.

def _cost(a, m):
    """Number of residues missed by the a-side and b-side coverage conditions."""
    diff = (a[:, None] - a[None, :]) % m
    cov_a = np.zeros(m, dtype=bool)
    cov_a[diff.ravel()] = True
    tri = (diff[:, :, None] + a[None, None, :]) % m
    cov_b = np.zeros(m, dtype=bool)
    cov_b[tri.ravel()] = True
    cov_b[a] = True
    return int((~cov_a).sum() + (~cov_b).sum())


def _cyclic_search(d, m, rng, deadline):
    """Find S (size d, 0 in S) in Z_m satisfying the diameter-3 covering conditions, or None."""
    if d > m:
        return None
    S = [0] + rng.sample(range(1, m), d - 1)
    a = np.array(S, dtype=np.int64)
    cost = _cost(a, m)
    T = 0.6
    steps = 0
    while cost > 0:
        if steps % 256 == 0 and time.monotonic() >= deadline:
            return None
        steps += 1
        idx = rng.randrange(1, d)
        new = rng.randrange(1, m)
        if new in S:
            continue
        a2 = a.copy()
        a2[idx] = new
        c2 = _cost(a2, m)
        if c2 <= cost or rng.random() < math.exp((cost - c2) / T):
            S[idx] = new
            a, cost = a2, c2
    return [int(x) for x in a]


def _cyclic_phase(d, best, rng, deadline):
    """Sweep cyclic orders m upward from just above the current best, sharing time evenly."""
    best_n, best_edges = best
    m0 = max(d, best_n // 2 + 1)
    mcap = d * d - d + 1  # covering S-S needs d^2-d+1 >= m
    ms = list(range(m0, mcap + 1))
    for i, m in enumerate(ms):
        now = time.monotonic()
        if now >= deadline:
            break
        share = (deadline - now) / (len(ms) - i)
        S = _cyclic_search(d, m, rng, now + share)
        if S is not None:
            n, edges = lib.haar_graph(m, S)
            if n > best_n and lib.is_valid(n, edges, d, 3):
                best_n, best_edges = n, edges
    return best_n, best_edges


# ---------------------------------------------------------------- structured bases

def _structured(d):
    """Best known structured D=3 base: PG(2,d-1), else Araujo-Pardo-Lopez, else smaller PG."""
    q = d - 1
    if q >= 2 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)
    if d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            return lib.araujo_lopez_graph(d - 2)
        except (ValueError, AssertionError):
            pass
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, TIME_FRAC * time_limit - MARGIN)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    kdd = lib.haar_graph(d, range(d))
    if not lib.is_valid(kdd[0], kdd[1], d, D):
        kdd = (1, [])
    best = kdd

    def consider(c):
        nonlocal best
        if c is not None and c[0] > best[0] and lib.is_valid(c[0], c[1], d, D):
            best = c

    if d == 2:
        n = 2 * D
        cyc = (n, [(i, (i + 1) % n) for i in range(n)])
        consider(cyc)
        return best
    if D == 2:
        return best

    if D == 3:
        base = None
        try:
            base = _structured(d)
        except (ValueError, AssertionError):
            base = None

        if base is not None and lib.is_valid(base[0], base[1], d, D):
            consider(base)
            cur = base
            mb = lib.moore_bound(d, D)
            fails = 0
            aug_deadline = start + 0.55 * (deadline - start)
            while fails < 3 and time.monotonic() < aug_deadline and cur[0] + 2 <= mb:
                now = time.monotonic()
                slice_end = min(aug_deadline, now + max(3.0, (aug_deadline - now) / 3))
                res = _augment(cur[0], cur[1], d, D, rng, slice_end)
                if res is None or not lib.is_valid(res[0], res[1], d, D):
                    fails += 1
                    continue
                fails = 0
                cur = res
                consider(cur)

        if time.monotonic() < deadline:
            n2, e2 = _cyclic_phase(d, best, rng, deadline)
            consider((n2, e2))
    else:
        # Random Haar search for other diameters.
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
                consider(found)
                misses = 0
            else:
                misses += 1
            m += 1

    if lib.is_valid(best[0], best[1], d, D):
        return best
    return kdd
