import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# D = 3 baseline: incidence graph of PG(2, q) for the largest prime power q
# with q + 1 <= d.
# ----------------------------------------------------------------------------

def _best_pg(d):
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over Z_m x|_r Z_k with annealed connection sets.
# ----------------------------------------------------------------------------

MAX_GROUPS = 8
CLIMB_ITERS = 800
_TABLE_CACHE = {}


def _groups(N):
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _tables(m, k, r):
    key = (m, k, r)
    hit = _TABLE_CACHE.get(key)
    if hit is not None:
        return hit
    order, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(order)] for x in range(order)]
    invs = [inv(g) for g in range(order)]
    val = (order, mul, T, invs)
    if len(_TABLE_CACHE) >= 48:
        _TABLE_CACHE.clear()
    _TABLE_CACHE[key] = val
    return val


def _unreached(N, T, invs, S, D):
    Sinv = [invs[g] for g in S]
    total = 0
    for src in (0, N):
        seen = bytearray(2 * N)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < N:
                    row = T[u]
                    for g in S:
                        v = N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    row = T[u - N]
                    for h in Sinv:
                        v = row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += 2 * N - count
    return total


def _climb(N, T, invs, d, D, rng, iters, deadline):
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(N, T, invs, S, D)
    best_S, best_v = S, cur
    T0 = 4.0 + 0.05 * cur
    for step in range(iters):
        if best_v == 0 or time.monotonic() > deadline:
            break
        temp = T0 * (1.0 - step / iters) + 0.2
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, T, invs, S2, D)
        delta = v - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            S, cur = S2, v
            if cur < best_v:
                best_S, best_v = S, cur
    return best_S if best_v == 0 else None


# ----------------------------------------------------------------------------
# NEW: degree-preserving bipartite double-edge-switch annealing.
#
# Start from a random d-regular bipartite graph with h + h vertices (union of d
# random perfect matchings), then repeatedly apply switches
#     (a,b), (c,e)  ->  (a,e), (c,b)      (a, c on the left; b, e on the right)
# which keep every degree and bipartiteness. The objective is the number of
# ordered vertex pairs at distance > D, computed with big-integer bitsets.
# Switches are accepted by simulated annealing on a time-based schedule.
# ----------------------------------------------------------------------------

def _replace(adj, x, old, new):
    lst = adj[x]
    lst[lst.index(old)] = new


def _apply_switch(adj, a, b, c, e):
    """Replace edges (a,b),(c,e) by (a,e),(c,b) in adjacency lists."""
    _replace(adj, a, b, e)
    _replace(adj, b, a, c)
    _replace(adj, c, e, b)
    _replace(adj, e, c, a)


def _ball_cost(n, adj, D):
    """Number of ordered pairs (v, w) with dist(v, w) > D; zero iff diameter <= D."""
    ball = [1 << v for v in range(n)]
    for _ in range(D):
        nb = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            nb.append(x)
        ball = nb
    return sum(n - b.bit_count() for b in ball)


def _switch_anneal(h, d, D, rng, deadline):
    """Anneal a d-regular bipartite graph on h+h vertices toward diameter <= D."""
    n = 2 * h
    L, R = [], []
    adj = [[] for _ in range(n)]
    for _ in range(d):
        ok = False
        for _t in range(2000):
            p = list(range(h))
            rng.shuffle(p)
            if all(h + p[i] not in adj[i] for i in range(h)):
                ok = True
                break
        if not ok:
            return None
        for i in range(h):
            b = h + p[i]
            L.append(i)
            R.append(b)
            adj[i].append(b)
            adj[b].append(i)

    m = len(L)
    cur = _ball_cost(n, adj, D)
    t_start = time.monotonic()
    span = max(1e-6, deadline - t_start)
    T0 = 2.0
    it = 0
    while cur > 0:
        it += 1
        if (it & 15) == 0:
            now = time.monotonic()
            if now > deadline:
                break
            frac = (now - t_start) / span
        else:
            frac = (time.monotonic() - t_start) / span if False else frac if it > 1 else 0.0
        T = T0 * (1.0 - min(1.0, frac)) + 0.05

        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a, b, c, e = L[i], R[i], L[j], R[j]
        if a == c or b == e or e in adj[a] or b in adj[c]:
            continue
        _apply_switch(adj, a, b, c, e)
        R[i] = e
        R[j] = b
        new = _ball_cost(n, adj, D)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = new
        else:
            _apply_switch(adj, a, e, c, b)  # undo
            R[i] = b
            R[j] = e

    if cur == 0:
        return n, [(L[k], R[k]) for k in range(m)]
    return None


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    tried = {}
    while best[0] < moore and time.monotonic() < deadline:
        n_best = best[0]
        now = time.monotonic()
        remaining = deadline - now
        if remaining <= 0:
            break

        use_switch = d >= 3 and rng.random() < 0.5
        if use_switch:
            # Aim one half-step above the current best: total order 2h with h = best//2 + 1.
            h = n_best // 2 + 1
            if 2 * h > moore:
                break
            chunk = min(remaining, max(3.0, 0.25 * remaining))
            res = _switch_anneal(h, d, D, rng, now + chunk)
            if res is not None:
                consider(res[0], res[1])
        else:
            lo = n_best // 2 + 1
            if lo > moore // 2:
                break
            window = max(2, lo // 10)
            hi = min(lo + window, moore // 2 + 1)
            N = min(range(lo, hi), key=lambda x: (tried.get(x, 0), rng.random()))
            tried[N] = tried.get(N, 0) + 1
            groups = _groups(N)
            rng.shuffle(groups)
            found = None
            for m, k2, r in groups[:MAX_GROUPS]:
                if time.monotonic() > deadline:
                    break
                _, _, T, invs = _tables(m, k2, r)
                S = _climb(N, T, invs, d, D, rng, CLIMB_ITERS, deadline)
                if S is not None:
                    found = (T, S)
                    break
            if found is not None:
                T, S = found
                edges = [(x, N + T[x][g]) for x in range(N) for g in S]
                consider(2 * N, edges)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
