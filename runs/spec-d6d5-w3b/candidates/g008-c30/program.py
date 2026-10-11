import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Cheap algebraic baselines (used only as fallbacks and for D = 3).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez graph for d = q + 2 with q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# New family: incremental "edge-split" growth of a d-regular bipartite graph,
# with simulated annealing by degree-preserving double-edge swaps.
#
# Invariant: every edge is stored as (l, r) with l on the left side and r on
# the right side. Degrees stay exactly d throughout, so max degree <= d.
# A growth step adds a new left vertex a and a new right vertex b: it takes d
# edges (l_i, r_i) with distinct endpoints, deletes them, and adds (a, r_i)
# and (l_i, b). Both new vertices get degree d and all old degrees are kept.
# ----------------------------------------------------------------------------

def _adj(n, E):
    adj = [set() for _ in range(n)]
    for u, v in E:
        adj[u].add(v)
        adj[v].add(u)
    return adj


def _bad(n, adj, D):
    """Ordered pairs at distance > D (bit-parallel). Zero iff diameter <= D and connected."""
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


def _add_pair(n, E, adj, d, rng):
    """Add one left vertex n and one right vertex n+1 by edge splitting. Mutates E and adj."""
    order = list(range(len(E)))
    rng.shuffle(order)
    used_l, used_r, chosen = set(), set(), []
    for idx in order:
        l, r = E[idx]
        if l in used_l or r in used_r:
            continue
        used_l.add(l)
        used_r.add(r)
        chosen.append(idx)
        if len(chosen) == d:
            break
    if len(chosen) < d:
        return False
    a, b = n, n + 1
    adj.append(set())
    adj.append(set())
    cs = set(chosen)
    newE = [E[i] for i in range(len(E)) if i not in cs]
    for idx in chosen:
        l, r = E[idx]
        adj[l].discard(r)
        adj[r].discard(l)
        adj[l].add(b)
        adj[b].add(l)
        adj[a].add(r)
        adj[r].add(a)
        newE.append((l, b))
        newE.append((a, r))
    E[:] = newE
    return True


def _anneal(n, E, adj, D, rng, deadline):
    """Degree-preserving double-edge swaps with Metropolis acceptance on the bad-pair count."""
    T = 1.5
    cost = _bad(n, adj, D)
    m = len(E)
    while cost and time.monotonic() < deadline:
        i = rng.randrange(m)
        j = rng.randrange(m)
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
        new = _bad(n, adj, D)
        if new <= cost or rng.random() < math.exp(-(new - cost) / T):
            cost = new
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
    return cost == 0


def build(d, D, seed, time_limit):
    start = time.monotonic()
    hard = start + 0.85 * time_limit

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    # K_{d,d}: diameter 2, optimal for D = 2 and always a valid fallback.
    kn, ke = lib.haar_graph(d, range(d))
    if D <= 2 or d == 1:
        return kn, ke

    best = (kn, ke)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    # Growth + annealing search.
    rng = random.Random(seed)
    cur_n = kn
    cur_E = list(ke)
    cur_adj = _adj(cur_n, cur_E)
    frac = 1.0 / 12.0
    step_cap = max(1.5, 0.08 * time_limit)

    while time.monotonic() < hard:
        N = cur_n // 2
        chunk = max(1, int(N * frac))
        n_try = cur_n
        E_try = list(cur_E)
        adj_try = [set(s) for s in cur_adj]
        for _ in range(chunk):
            if not _add_pair(n_try, E_try, adj_try, d, rng):
                break
            n_try += 2
        if n_try == cur_n:
            frac = max(frac * 0.5, 1.0 / 500.0)
            continue

        end = min(hard, time.monotonic() + step_cap)
        if _anneal(n_try, E_try, adj_try, D, rng, end):
            consider(n_try, E_try)
            cur_n, cur_E, cur_adj = n_try, E_try, adj_try
            frac = min(frac * 1.5, 1.0 / 12.0)
        else:
            frac = max(frac * 0.5, 1.0 / 500.0)

    n, e = best
    if not lib.is_valid(n, e, d, D):
        return kn, ke
    return n, e
