import math
import random
import sys
import time

import lib

sys.setrecursionlimit(10000)


# ----------------------------------------------------------------------------
# Host: incidence graph of PG(2, q) with q + 1 >= d, minus (q + 1 - d) disjoint
# perfect matchings, so the host is exactly d-regular and bipartite.
# ----------------------------------------------------------------------------

def _perfect_matching(m, adj):
    """Perfect matching of a regular bipartite graph; left = 0..m-1, right = m..2m-1."""
    match_l = [-1] * m
    match_r = {}

    def aug(u, seen):
        for v in adj[u]:
            if v in seen:
                continue
            seen.add(v)
            w = match_r.get(v)
            if w is None or aug(w, seen):
                match_r[v] = u
                match_l[u] = v
                return True
        return False

    for u in range(m):
        if not aug(u, set()):
            return None
    return [(u, match_l[u]) for u in range(m)]


def _host(d):
    """Return (m, adjl) for a d-regular host built from PG(2, q), or None."""
    q = max(2, d - 1)
    while not (lib.is_prime_power(q) and q + 1 >= d):
        q += 1
    n, edges = lib.projective_plane_incidence(q)
    m = n // 2
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    for _ in range(q + 1 - d):
        M = _perfect_matching(m, adj)
        if M is None:
            return None
        for u, v in M:
            adj[u].discard(v)
            adj[v].discard(u)
    return m, [list(s) for s in adj]


# ----------------------------------------------------------------------------
# Induced-subgraph search: choose a vertex subset S of the host whose induced
# subgraph has diameter <= D. Induced subgraphs keep degree <= d automatically.
# ----------------------------------------------------------------------------

def _bad(S_in, Sv, adjl, D):
    """Number of unordered pairs in S at distance > D inside the induced subgraph."""
    N = len(S_in)
    reach = [0] * N
    for v in Sv:
        reach[v] = 1 << v
    for _ in range(D):
        nxt = [0] * N
        changed = False
        for v in Sv:
            r = reach[v]
            for u in adjl[v]:
                if S_in[u]:
                    r |= reach[u]
            if r != reach[v]:
                changed = True
            nxt[v] = r
        reach = nxt
        if not changed:
            break
    k = len(Sv)
    missing = sum(k - reach[v].bit_count() for v in Sv)
    return missing // 2


def _greedy(N, adjl, D, rng, deadline):
    """Randomized greedy: add vertices while the induced subgraph stays valid."""
    order = list(range(N))
    rng.shuffle(order)
    S_in = [False] * N
    Sv = []
    for v in order:
        if time.monotonic() >= deadline:
            break
        S_in[v] = True
        if _bad(S_in, Sv + [v], adjl, D) == 0:
            Sv.append(v)
        else:
            S_in[v] = False
    return S_in, Sv


def _anneal(N, adjl, D, S_in, rng, deadline, lam=1.0, T0=1.0, T1=0.05):
    """Metropolis search maximizing |S| - lam * bad(S); returns the largest valid S seen."""
    Sv = [v for v in range(N) if S_in[v]]
    b = _bad(S_in, Sv, adjl, D)
    cnt = len(Sv)
    f = cnt - lam * b
    best_cnt = cnt if b == 0 else -1
    best = list(Sv) if b == 0 else None
    t0 = time.monotonic()
    span = max(1e-6, deadline - t0)
    while True:
        now = time.monotonic()
        if now >= deadline:
            break
        T = T0 * (T1 / T0) ** ((now - t0) / span)
        v = rng.randrange(N)
        S_in[v] = not S_in[v]
        Sv2 = [x for x in range(N) if S_in[x]]
        b2 = _bad(S_in, Sv2, adjl, D)
        cnt2 = len(Sv2)
        f2 = cnt2 - lam * b2
        if f2 >= f or rng.random() < math.exp((f2 - f) / T):
            f, b, cnt = f2, b2, cnt2
            if b == 0 and cnt > best_cnt:
                best_cnt = cnt
                best = Sv2
        else:
            S_in[v] = not S_in[v]
    return best_cnt, best


def _saturate(Sv, m, adjl, d, rng):
    """Build the induced subgraph on Sv, then add edges between deficient opposite-side vertices."""
    idx = {v: i for i, v in enumerate(Sv)}
    n = len(Sv)
    present = set()
    edges = []
    deg = [0] * n
    for v in Sv:
        for u in adjl[v]:
            if u in idx and v < u:
                a, b = idx[v], idx[u]
                edges.append((a, b))
                present.add((min(a, b), max(a, b)))
                deg[a] += 1
                deg[b] += 1
    side = [0 if v < m else 1 for v in Sv]
    left = [i for i in range(n) if side[i] == 0 and deg[i] < d]
    right = [i for i in range(n) if side[i] == 1 and deg[i] < d]
    pairs = [(a, b) for a in left for b in right if (min(a, b), max(a, b)) not in present]
    rng.shuffle(pairs)
    for a, b in pairs:
        key = (min(a, b), max(a, b))
        if deg[a] < d and deg[b] < d and key not in present:
            edges.append((a, b))
            present.add(key)
            deg[a] += 1
            deg[b] += 1
    return n, edges


def _search(d, D, rng, deadline):
    host = _host(d)
    if host is None:
        return None
    m, adjl = host
    N = 2 * m
    S_in, Sv = _greedy(N, adjl, D, rng, deadline)
    if not Sv:
        return None
    best_cnt, best = _anneal(N, adjl, D, S_in, rng, deadline)
    if best is None:
        best = Sv
    return _saturate(best, m, adjl, d, rng)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3 and d >= 3:
        # Known record family for d = q + 2, q a prime power (safe baseline).
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                n_a, e_a = lib.araujo_lopez_graph(d - 2)
                consider(n_a, e_a)
            except Exception:
                pass
        # New family: induced subgraphs of a regularized projective plane host.
        try:
            res = _search(d, D, rng, deadline)
            if res is not None:
                consider(res[0], res[1])
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
