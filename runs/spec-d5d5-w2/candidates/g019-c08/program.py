import math
import random
import time

import lib

# Bold change for the weak D = 5 cases: abandon the cyclic/semidirect hill-climb
# and the cover-growth stage. Instead, anneal multi-orbit bi-Cayley lifts directly.
#
# Model: nb A-orbits and nb B-orbits, each of size G (a finite group, here
# Z_m x|_r Z_k). Layer L is a perfect matching between A-orbits and B-orbits
# (permutation sig[L]) with a voltage vol[L][i] in G, so A(i,x) ~ B(sig[L][i], x*vol[L][i]).
# Every vertex gets degree d, the graph is bipartite, and left translation by G
# is an automorphism, so distances only need checking from one representative per orbit.
# The cost is the number of (representative, vertex) pairs farther than D apart.
# Simulated annealing drives this cost to zero. Only graphs passing lib.is_valid are kept.

_BIG = 10 ** 9
_MAX_G = 800
_GROUP_CACHE = {}
_TABLE_CACHE = {}


def _groups(N):
    """All semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _groups_of(N):
    hit = _GROUP_CACHE.get(N)
    if hit is None:
        hit = _groups(N)
        if len(_GROUP_CACHE) >= 64:
            _GROUP_CACHE.clear()
        _GROUP_CACHE[N] = hit
    return hit


def _table(m, k, r):
    """Return (order, T) with T[x][g] = x*g for the semidirect group."""
    key = (m, k, r)
    hit = _TABLE_CACHE.get(key)
    if hit is not None:
        return hit
    order, mul, _ = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(order)] for x in range(order)]
    val = (order, T)
    if len(_TABLE_CACHE) >= 24:
        _TABLE_CACHE.clear()
    _TABLE_CACHE[key] = val
    return val


def _cost(G, T, nb, d, D, sig, vol):
    """Number of (orbit representative, vertex) pairs at distance > D. Zero means valid."""
    N = 2 * nb * G
    for i in range(nb):
        seen = set()
        for L in range(d):
            key = (sig[L][i], vol[L][i])
            if key in seen:
                return _BIG          # parallel edges would appear
            seen.add(key)
    adj = [[] for _ in range(N)]
    for L in range(d):
        sL = sig[L]
        vL = vol[L]
        for i in range(nb):
            bi = i * G
            bj = (nb + sL[i]) * G
            s = vL[i]
            for x in range(G):
                a = bi + x
                b = bj + T[x][s]
                adj[a].append(b)
                adj[b].append(a)
    reps = [i * G for i in range(nb)] + [(nb + j) * G for j in range(nb)]
    total = 0
    for src in reps:
        seen = bytearray(N)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += N - count
    return total


def _edges(G, T, nb, d, sig, vol):
    E = []
    for L in range(d):
        for i in range(nb):
            bi = i * G
            bj = (nb + sig[L][i]) * G
            s = vol[L][i]
            for x in range(G):
                E.append((bi + x, bj + T[x][s]))
    return 2 * nb * G, E


def _anneal(G, T, nb, d, D, rng, iters, deadline):
    """Simulated annealing over voltages and layer permutations. Returns (n, edges) or None."""
    sig = [rng.sample(range(nb), nb) for _ in range(d)]
    vol = [[rng.randrange(G) for _ in range(nb)] for _ in range(d)]
    cur = _cost(G, T, nb, d, D, sig, vol)
    temp0 = max(1.0, 0.05 * cur) if cur < _BIG else 2.0

    for it in range(iters):
        if cur == 0:
            break
        if (it & 15) == 0 and time.monotonic() > deadline:
            break
        temp = temp0 * (1.0 - it / iters) + 0.02
        L = rng.randrange(d)
        if nb > 1 and rng.random() < 0.3:
            i1, i2 = rng.sample(range(nb), 2)
            row = sig[L]
            row[i1], row[i2] = row[i2], row[i1]
            new = _cost(G, T, nb, d, D, sig, vol)
            if new <= cur or rng.random() < math.exp((cur - new) / temp):
                cur = new
            else:
                row[i1], row[i2] = row[i2], row[i1]
        else:
            i = rng.randrange(nb)
            old = vol[L][i]
            s = rng.randrange(G)
            if s == old:
                continue
            vol[L][i] = s
            new = _cost(G, T, nb, d, D, sig, vol)
            if new <= cur or rng.random() < math.exp((cur - new) / temp):
                cur = new
            else:
                vol[L][i] = old

    if cur != 0:
        return None
    return _edges(G, T, nb, d, sig, vol)


def _search(d, D, n0, deadline, moore, rng):
    """Repeatedly aim for the smallest order that beats the current best."""
    best = None
    cur = n0
    slice_len = max(2.0, 0.15 * (deadline - time.monotonic()))
    while time.monotonic() < deadline and cur < moore:
        opts = []
        for nb in (1, 2, 3):
            G = cur // (2 * nb) + 1
            if G > _MAX_G or 2 * nb * G > moore:
                continue
            opts.append((nb, G))
        if not opts:
            break
        nb, G = rng.choice(opts)
        m, k2, r = rng.choice(_groups_of(G))
        order, T = _table(m, k2, r)
        slice_end = min(deadline, time.monotonic() + slice_len)
        res = _anneal(order, T, nb, d, D, rng, 4000, slice_end)
        if res is not None and res[0] > cur and lib.is_valid(res[0], res[1], d, D):
            cur = res[0]
            best = res
    return best


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 5.0))
    deadline = t0 + budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    if D == 2:
        return best_n, list(best_e)

    moore = lib.moore_bound(d, D)
    rng = random.Random(seed * 1000003 + 97 * d + D)

    try:
        # D = 3: projective plane incidence graph of the largest q with q + 1 <= d.
        if D == 3:
            for q in range(min(d - 1, 25), 1, -1):
                if lib.is_prime_power(q):
                    n, e = lib.projective_plane_incidence(q)
                    if n > best_n and lib.is_valid(n, e, d, D):
                        best_n, best_e = n, e
                    break

        extra = _search(d, D, best_n, deadline, moore, rng)
        if extra is not None and extra[0] > best_n and lib.is_valid(extra[0], extra[1], d, D):
            best_n, best_e = extra
    except Exception:
        pass

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, list(best_e)
