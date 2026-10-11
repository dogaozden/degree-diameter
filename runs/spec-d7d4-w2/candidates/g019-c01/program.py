import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Construction: random bipartite voltage lifts over small groups, repaired by
# local search on the number of pairs at distance > D.
#
# Base graph: s vertices on side A and s on side B, with d "layers". Each layer
# is a permutation pi (A-vertex i joins B-vertex pi[i]) with a group voltage
# vol[i] per A-vertex. Every base vertex then has degree d, and the lift over a
# group G of order N has 2*s*N vertices, bipartite by construction.
#
# Search: start from random voltages and permutations, then move one voltage or
# swap two permutation targets at a time, keeping moves that do not increase the
# count of bad pairs. Every returned graph is checked with lib.is_valid.
# Groups are cyclic Z_N and semidirect products Z_m x| Z_k (via lib.semidirect_group).
# ----------------------------------------------------------------------------

def _cyclic_table(N):
    return [[(x + g) % N for g in range(N)] for x in range(N)]


def _group_options(N, rng):
    """Multiplication tables mt[x][g] = x*g for a few groups of order N."""
    tables = [_cyclic_table(N)]
    for k in range(2, 9):
        if N % k or N // k < 2:
            continue
        m = N // k
        rs = [r for r in range(1, m)
              if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if not rs:
            continue
        for r in rng.sample(rs, min(2, len(rs))):
            order, mul, _inv = lib.semidirect_group(m, k, r)
            tables.append([[mul(x, g) for g in range(order)] for x in range(order)])
    return tables


def _edges_of(s, N, mt, layers):
    """Lift the base graph: A-vertex i over x joins B-vertex perm[i] over x*vol[i]."""
    E = []
    for perm, vol in layers:
        for i in range(s):
            ib = i * N
            jb = (s + perm[i]) * N
            g = vol[i]
            for x in range(N):
                E.append((ib + x, jb + mt[x][g]))
    return E


def _bad(n, E, D):
    """Number of unordered pairs at distance > D (unreachable pairs count)."""
    adj = [[] for _ in range(n)]
    for u, v in E:
        adj[u].append(v)
        adj[v].append(u)
    ball = [1 << v for v in range(n)]
    for _ in range(D):
        nb = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            nb.append(x)
        ball = nb
    return sum(n - b.bit_count() for b in ball) // 2


def _clean(E):
    return sorted({(min(u, v), max(u, v)) for u, v in E if u != v})


def _search(s, N, mt, d, D, deadline, rng):
    """Local search for a regular lift with no bad pairs; returns edges or None."""
    n = 2 * s * N
    layers = []
    for _ in range(d):
        perm = list(range(s))
        rng.shuffle(perm)
        vol = [rng.randrange(N) for _ in range(s)]
        layers.append([perm, vol])
    cur = _bad(n, _edges_of(s, N, mt, layers), D)
    while cur > 0:
        if time.monotonic() > deadline:
            return None
        perm, vol = layers[rng.randrange(d)]
        if s >= 2 and rng.random() >= 0.6:
            # Swap two B-targets inside one layer (keeps the layer a permutation).
            i, j = rng.sample(range(s), 2)
            perm[i], perm[j] = perm[j], perm[i]
            new = _bad(n, _edges_of(s, N, mt, layers), D)
            if new <= cur or rng.random() < 0.02:
                cur = new
            else:
                perm[i], perm[j] = perm[j], perm[i]
        else:
            i = rng.randrange(s)
            old = vol[i]
            vol[i] = rng.randrange(N)
            new = _bad(n, _edges_of(s, N, mt, layers), D)
            if new <= cur or rng.random() < 0.02:
                cur = new
            else:
                vol[i] = old
    return _clean(_edges_of(s, N, mt, layers))


def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = float(time_limit)
    deadline = start + 0.80 * T
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))
    if D == 2 or d == 1:
        return best
    if d == 2:
        n = 2 * D
        cyc = [(i, (i + 1) % n) for i in range(n)]
        if lib.is_valid(n, cyc, d, D):
            return n, cyc
        return best

    moore = lib.moore_bound(d, D)
    if best[0] >= moore:
        return best

    # Ascending chain of even orders, each target searched over several
    # (base size, group) options. A target that fails entirely ends the chain.
    n_t = best[0] + 2
    s_opts = (1, 2, 3, 4)
    while time.monotonic() < deadline and n_t <= moore:
        slice_t = 0.25 if n_t < 300 else 2.0
        options = []
        for s in s_opts:
            if n_t % (2 * s):
                continue
            N = n_t // (2 * s)
            if N < 2:
                continue
            for mt in _group_options(N, rng):
                options.append((s, N, mt))
        rng.shuffle(options)

        found = None
        for s, N, mt in options:
            if time.monotonic() >= deadline:
                break
            sub = min(deadline, time.monotonic() + slice_t)
            E = _search(s, N, mt, d, D, sub, rng)
            if E is not None and lib.is_valid(n_t, E, d, D):
                found = (n_t, E)
                break

        if found is None:
            break
        best = found
        n_t += 2

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
