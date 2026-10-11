"""Bipartite diameter-D search for d=5, D=5 and other cases.

Two constructions are searched within the time budget, and the best valid graph
found is returned:

1. Multi-base voltage lifts over semidirect products Z_m x| Z_k (k base vertices
   per side, d permutation layers with voltages). Annealed on the number of vertex
   pairs farther than D apart. Reachability is evaluated for all 2k base
   representatives at once with numpy gathers, which is much faster than
   per-source Python BFS.
2. Unstructured biregular bipartite graphs: random d-regular start, then 2-switch
   moves (edge exchanges that keep degrees), annealed on the bit-parallel count of
   pairs farther than D apart. This branch is untested in the sense that it is
   not known to reach the record.

Fallbacks: K_{d,d} (diameter 2), PG(2,d-1) incidence for D = 3, and every
candidate is checked with lib.is_valid before it is accepted.
"""
import math
import random
import time

import numpy as np

import lib

_BIG = 10 ** 9
_KS = (1, 2, 3, 4)
_LIFT_ITERS = 6000


# ----------------------------------------------------------------------------
# Group helpers.
# ----------------------------------------------------------------------------

def _groups(N):
    """Semidirect parameters (m, k, r) with m * k = N giving Z_m x|_r Z_k."""
    out = []
    for kk in range(1, N + 1):
        if N % kk:
            continue
        m = N // kk
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, kk, m) == 1 % m:
                out.append((m, kk, r))
    return out


def _perm_getter(mul, G):
    """Cached right-multiplication permutations g -> g * s as numpy arrays."""
    cache = {}

    def get(s):
        p = cache.get(s)
        if p is None:
            p = np.array([mul(g, s) for g in range(G)], dtype=np.int64)
            cache[s] = p
        return p

    return get


# ----------------------------------------------------------------------------
# Voltage-lift evaluation and annealing.
# Vertex ids: left base i -> block i, right base j -> block k + j, each block of size G.
# Edge for layer l: (i, g) -- (k + sig_l[i], g * s_l). Identity element is index 0.
# ----------------------------------------------------------------------------

def _nbr(k, G, d, sig, sv, getP):
    """Neighbour array of shape (2kG, d) for the lift."""
    N = 2 * k * G
    nbr = np.empty((N, d), dtype=np.int64)
    for l in range(d):
        perm = getP(sv[l])
        pinv = np.argsort(perm)
        s_l = sig[l]
        isg = [0] * k
        for i in range(k):
            isg[s_l[i]] = i
        for i in range(k):
            nbr[i * G:(i + 1) * G, l] = (k + s_l[i]) * G + perm
        for j in range(k):
            nbr[(k + j) * G:(k + j + 1) * G, l] = isg[j] * G + pinv
    return nbr


def _unreached(nbr, k, G, D):
    """Number of (base representative, vertex) pairs not within distance D."""
    N = nbr.shape[0]
    B = 2 * k
    R = np.zeros((B, N), dtype=bool)
    idx = np.arange(B)
    R[idx, idx * G] = True
    for _ in range(D):
        R2 = R | R[:, nbr].any(axis=2)
        if np.array_equal(R2, R):
            break
        R = R2
    return B * N - int(R.sum())


def _dups(k, d, sig, sv):
    """Number of repeated (left, right, voltage) darts, which would give parallel edges."""
    seen = set()
    c = 0
    for l in range(d):
        for i in range(k):
            key = (i, sig[l][i], sv[l])
            if key in seen:
                c += 1
            else:
                seen.add(key)
    return c


def _score(k, G, d, D, sig, sv, getP):
    dup = _dups(k, d, sig, sv)
    if dup:
        return _BIG * dup
    return _unreached(_nbr(k, G, d, sig, sv, getP), k, G, D)


def _edges(k, G, d, sig, sv, getP):
    E = []
    for l in range(d):
        perm = getP(sv[l]).tolist()
        for i in range(k):
            bl = i * G
            br = (k + sig[l][i]) * G
            for g in range(G):
                E.append((bl + g, br + perm[g]))
    return 2 * k * G, E


def _anneal_lift(d, D, k, G, mul, rng, deadline, iters):
    """Anneal voltages and layer permutations until every base representative reaches all within D."""
    getP = _perm_getter(mul, G)
    sig = []
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        sig.append(p)
    sv = [rng.randrange(G) for _ in range(d)]
    cost = _score(k, G, d, D, sig, sv, getP)
    for it in range(iters):
        if cost == 0:
            break
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        T = max(0.05, 2.0 * (1.0 - it / iters))
        l = rng.randrange(d)
        if k == 1 or rng.random() < 0.6:
            old = sv[l]
            new = rng.randrange(G)
            if new == old:
                continue
            sv[l] = new
            c2 = _score(k, G, d, D, sig, sv, getP)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                sv[l] = old
        else:
            a, b = rng.sample(range(k), 2)
            row = sig[l]
            row[a], row[b] = row[b], row[a]
            c2 = _score(k, G, d, D, sig, sv, getP)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                row[a], row[b] = row[b], row[a]
    if cost != 0:
        return None
    return _edges(k, G, d, sig, sv, getP)


# ----------------------------------------------------------------------------
# Unstructured biregular search with 2-switch moves.
# Left vertices are 0..M-1, right vertices are M..2M-1 (global ids in edges).
# ----------------------------------------------------------------------------

def _bad_count(adj, N, D):
    """Number of unordered vertex pairs at distance more than D (bit-parallel balls)."""
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        new = []
        for v in range(N):
            x = reach[v]
            for u in adj[v]:
                x |= reach[u]
            new.append(x)
        if new == reach:
            break
        reach = new
    return sum(N - r.bit_count() for r in reach) // 2


def _random_biregular(M, d, rng):
    """Simple d-regular bipartite graph from d random permutation layers; None on failure."""
    S = set()
    E = []
    for _ in range(d):
        for _attempt in range(300):
            perm = list(range(M))
            rng.shuffle(perm)
            if all((i, M + perm[i]) not in S for i in range(M)):
                break
        else:
            return None
        for i in range(M):
            e = (i, M + perm[i])
            S.add(e)
            E.append(e)
    return E, S


def _apply_switch(adj, a, b, c, e):
    """Replace edges (a,b),(c,e) by (a,e),(c,b) in adjacency lists."""
    adj[a].remove(b)
    adj[b].remove(a)
    adj[c].remove(e)
    adj[e].remove(c)
    adj[a].append(e)
    adj[e].append(a)
    adj[c].append(b)
    adj[b].append(c)


def _undo_switch(adj, a, b, c, e):
    adj[a].remove(e)
    adj[e].remove(a)
    adj[c].remove(b)
    adj[b].remove(c)
    adj[a].append(b)
    adj[b].append(a)
    adj[c].append(e)
    adj[e].append(c)


def _switch_search(d, D, M, rng, deadline):
    """Anneal 2-switch moves on a random d-regular bipartite graph with M vertices per side."""
    N = 2 * M
    init = _random_biregular(M, d, rng)
    if init is None:
        return None
    E, S = init
    adj = [[] for _ in range(N)]
    for a, b in E:
        adj[a].append(b)
        adj[b].append(a)
    cur = _bad_count(adj, N, D)
    start = time.monotonic()
    span = max(1e-3, deadline - start)
    m = len(E)
    T0 = 1.5
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            return None
        T = max(0.05, T0 * (1.0 - (now - start) / span))
        i = rng.randrange(m)
        j = rng.randrange(m)
        a, b = E[i]
        c, e = E[j]
        if i == j or a == c or b == e:
            continue
        if (a, e) in S or (c, b) in S:
            continue
        _apply_switch(adj, a, b, c, e)
        new = _bad_count(adj, N, D)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = new
            S.discard((a, b))
            S.discard((c, e))
            S.add((a, e))
            S.add((c, b))
            E[i] = (a, e)
            E[j] = (c, b)
        else:
            _undo_switch(adj, a, b, c, e)
    return E


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 5.0))
    deadline = t0 + budget

    if d < 1:
        return 1, []
    if D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    if D == 2:
        return best_n, best_e

    # Projective plane for D = 3 when d - 1 is a prime power (meets the Moore bound).
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    moore = lib.moore_bound(d, D)
    rng = random.Random(seed * 1000003 + 7919 * d + 31 * D)
    slice_len = max(1.0, 0.12 * budget)

    while best_n < moore and time.monotonic() < deadline:
        if rng.random() < 0.5:
            # Structured: multi-base voltage lift over a semidirect product.
            k = rng.choice(_KS)
            lo = max(best_n // (2 * k) + 1, d)
            hi = moore // (2 * k)
            if lo > hi:
                continue
            G = lo + rng.randrange(min(8, hi - lo + 1))
            groups = _groups(G)
            if not groups:
                continue
            m, kk, r = rng.choice(groups)
            _, mul, _ = lib.semidirect_group(m, kk, r)
            end = min(deadline, time.monotonic() + slice_len)
            res = _anneal_lift(d, D, k, G, mul, rng, end, _LIFT_ITERS)
            if res is not None:
                n, e = res
                if n > best_n and lib.is_valid(n, e, d, D):
                    best_n, best_e = n, e
        else:
            # Unstructured: 2-switch annealing on a biregular bipartite graph.
            M = best_n // 2 + 1
            if M > moore // 2:
                continue
            end = min(deadline, time.monotonic() + slice_len)
            E = _switch_search(d, D, M, rng, end)
            if E is not None:
                n = 2 * M
                if n > best_n and lib.is_valid(n, E, d, D):
                    best_n, best_e = n, E

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, best_e
