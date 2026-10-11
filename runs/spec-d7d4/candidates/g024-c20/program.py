import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Haar graphs of finite groups.
#
# For a group G (order M) and a connection set S of d distinct elements, the
# Haar graph has vertices a_g, b_g (g in G) and edges a_g -- b_{g*s} for s in S.
# It is bipartite, d-regular, and vertex-transitive on each side (left
# multiplication is an automorphism). So the diameter is at most D iff, from
# a_1 and from b_1, every vertex of the right kind lies within distance D.
# This is a search over connection sets for a fixed group, not a copy of any
# known record construction.
# ----------------------------------------------------------------------------

def _tables(g):
    """Return (mul, inv, M) as Python lists for a group spec g."""
    if g[0] == 'cyc':
        M = g[1]
        x = np.arange(M, dtype=np.int64)
        mul = (x[:, None] + x[None, :]) % M
        inv = (-x) % M
    else:
        _, m, k, r = g
        M = m * k
        idx = np.arange(M, dtype=np.int64)
        a = idx // k
        b = idx % k
        pw = np.array([pow(r, t, m) for t in range(k)], dtype=np.int64)
        mul = ((a[:, None] + pw[b][:, None] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
        nb = (-b) % k
        inv = ((-pw[nb] * a) % m) * k + nb
    return mul.tolist(), inv.tolist(), M


def _groups(M, rng):
    """Cyclic group of order M plus a few random semidirect products Z_m x| Z_k with m*k = M."""
    cands = []
    for k in range(2, M):
        if M % k:
            continue
        m = M // k
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                cands.append(('sd', m, k, r))
    rng.shuffle(cands)
    return [('cyc', M)] + cands[:3]


def _reach(adj, src, D, N):
    seen = bytearray(N)
    seen[src] = 1
    frontier = [src]
    for _ in range(D):
        nxt = []
        for v in frontier:
            for u in adj[v]:
                if not seen[u]:
                    seen[u] = 1
                    nxt.append(u)
        if not nxt:
            break
        frontier = nxt
    return seen


def _cost(S, M, D, mt, it):
    """Number of far pairs (0 means the Haar graph has diameter <= D)."""
    invS = [it[s] for s in S]
    N = 2 * M
    adj = [None] * N
    for g in range(M):
        row = mt[g]
        adj[g] = [M + row[s] for s in S]
        adj[M + g] = [row[t] for t in invS]
    seen_a = _reach(adj, 0, D, N)
    seen_b = _reach(adj, M, D, N)
    return (N - sum(seen_a)) + (M - sum(seen_b[M:]))


def _anneal(M, d, D, mt, it, rng, deadline):
    iters = 2000
    while time.monotonic() < deadline:
        S = rng.sample(range(M), d)
        cur = _cost(S, M, D, mt, it)
        for step in range(iters):
            if cur == 0:
                return S
            if (step & 31) == 0 and time.monotonic() >= deadline:
                return None
            i = rng.randrange(d)
            x = rng.randrange(M)
            if x in S:
                continue
            old = S[i]
            S[i] = x
            new = _cost(S, M, D, mt, it)
            T = 0.2 + 1.8 * (1 - step / iters)
            if new <= cur or rng.random() < math.exp(-(new - cur) / T):
                cur = new
            else:
                S[i] = old
        if cur == 0:
            return S
    return None


def _search(M, d, D, deadline, rng):
    groups = _groups(M, rng)
    for idx, g in enumerate(groups):
        now = time.monotonic()
        if now >= deadline:
            break
        gd = now + (deadline - now) / (len(groups) - idx)
        mt, it, _ = _tables(g)
        S = _anneal(M, d, D, mt, it, rng, gd)
        if S is not None:
            return mt, S
    return None


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.0, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    n0, e0 = lib.haar_graph(d, range(d))
    best = (n0, e0) if lib.is_valid(n0, e0, d, D) else (1, [])

    moore = lib._moore_bound(d, D)
    if best[0] >= moore:
        return best

    Mmax = moore // 2
    Mcap = min(Mmax, 700)

    # Ladder over group orders M (graph order 2M), increasing while search succeeds.
    M = max(d, 2)
    fails = 0
    while M <= Mcap and fails < 6:
        now = time.monotonic()
        remaining = deadline - now
        if remaining <= 0.05:
            break
        mb = min(remaining, max(0.5, 0.2 * remaining))
        res = _search(M, d, D, now + mb, rng)
        if res is not None:
            mt, S = res
            edges = [(g, M + mt[g][s]) for g in range(M) for s in S]
            if 2 * M > best[0] and lib.is_valid(2 * M, edges, d, D):
                best = (2 * M, edges)
            fails = 0
        else:
            fails += 1
        M += 1

    return best
