import math
import random
import time

import numpy as np

import lib


# ---------------------------------------------------------------- bi-Cayley search (D = 3)
#
# Group G = Z_N x|_r Z_K of order M = N*K (element (a,b) coded as a*K+b, identity 0).
# Bi-Cayley graph: a_x ~ b_{x*s} for s in S, |S| = d, 1 in S WLOG.
# Left translations are automorphisms, transitive on each side, so diameter <= 3 iff
# from a_e and from b_e every vertex is within distance 3. Four coverage conditions:
#   a_e: a-vertices within 2, b-vertices within 3
#   b_e: b-vertices within 2, a-vertices within 3
# Simulated annealing over S minimising the total number of misses.

def _tables(N, K, r):
    """Multiplication table T[x, y] = x*y and inverse vector for the semidirect group."""
    M = N * K
    X = np.arange(M, dtype=np.int64)
    xa = X // K
    xb = X % K
    pw = np.array([pow(r, bb, N) for bb in range(K)], dtype=np.int64)
    pb = pw[xb]
    T = ((xa[:, None] + pb[:, None] * xa[None, :]) % N) * K + (xb[:, None] + xb[None, :]) % K
    nb = (-xb) % K
    inv = ((-pw[nb] * xa) % N) * K + nb
    return T, inv


def _groups(M):
    """All semidirect products Z_N x|_r Z_K with N*K = M, N >= 2 (r = 1 gives direct products)."""
    out = []
    for K in range(1, M + 1):
        if M % K:
            continue
        N = M // K
        if N < 2:
            continue
        if K == 1:
            out.append((N, 1, 1))
            continue
        for r in range(1, N):
            if math.gcd(r, N) == 1 and pow(r, K, N) == 1 % N:
                out.append((N, K, r))
    return out


def _cost(S, iS, T, M):
    """Total coverage misses for the bi-Cayley graph with connection set S (array, S[0] = 0)."""
    A2 = np.unique(T[np.ix_(S, iS)])          # a-vertices at distance 2 from a_e
    B3 = T[np.ix_(A2, S)].ravel()             # b-vertices at distance 3 from a_e
    cov_a = np.zeros(M, dtype=bool)
    cov_a[A2] = True
    cov_a[0] = True
    cov_b = np.zeros(M, dtype=bool)
    cov_b[S] = True
    cov_b[B3] = True
    B2 = np.unique(T[np.ix_(iS, S)])          # b-vertices at distance 2 from b_e
    A3 = T[np.ix_(B2, iS)].ravel()            # a-vertices at distance 3 from b_e
    cov_b2 = np.zeros(M, dtype=bool)
    cov_b2[B2] = True
    cov_b2[0] = True
    cov_a2 = np.zeros(M, dtype=bool)
    cov_a2[iS] = True
    cov_a2[A3] = True
    return 4 * M - int(cov_a.sum() + cov_b.sum() + cov_b2.sum() + cov_a2.sum())


def _edges(S, T, M, d):
    """Edge list of the bi-Cayley graph on 2M vertices (a_x = x, b_y = M + y)."""
    arr = np.array(S, dtype=np.int64)
    Y = T[:, arr]
    edges = [(x, M + int(Y[x, j])) for x in range(M) for j in range(d)]
    return 2 * M, edges


def _rand_set(d, M, rng):
    return [0] + rng.sample(range(1, M), d - 1)


def _search_m(d, D, M, rng, slice_end, hard_deadline):
    """Search bi-Cayley graphs of order 2M over several groups; return (n, edges) or None."""
    groups = _groups(M)
    rng.shuffle(groups)
    groups = groups[:40]
    states = []
    ar = np.arange(M)
    for (N, K, r) in groups:
        T, inv = _tables(N, K, r)
        if not np.all(T[ar, inv] == 0):
            continue
        S = _rand_set(d, M, rng)
        Sa = np.array(S, dtype=np.int64)
        c = _cost(Sa, inv[Sa], T, M)
        states.append({'T': T, 'inv': inv, 'S': S, 'c': c, 'best': c,
                       'stale': 0, 'dead': False})
    if not states:
        return None
    temp = 1.0
    while True:
        alive = [st for st in states if not st['dead']]
        if not alive:
            return None
        for st in alive:
            if time.monotonic() >= slice_end or time.monotonic() >= hard_deadline:
                return None
            T, inv = st['T'], st['inv']
            for _ in range(200):
                if st['c'] == 0:
                    break
                S = st['S']
                idx = rng.randrange(1, d)
                cand = rng.randrange(1, M)
                if cand in S:
                    continue
                S2 = list(S)
                S2[idx] = cand
                Sa = np.array(S2, dtype=np.int64)
                c2 = _cost(Sa, inv[Sa], T, M)
                if c2 <= st['c'] or rng.random() < math.exp((st['c'] - c2) / temp):
                    st['S'] = S2
                    st['c'] = c2
                    if c2 < st['best']:
                        st['best'] = c2
                        st['stale'] = 0
                        continue
                st['stale'] += 1
                if st['stale'] > 1000:
                    st['S'] = _rand_set(d, M, rng)
                    Sa = np.array(st['S'], dtype=np.int64)
                    st['c'] = _cost(Sa, inv[Sa], T, M)
                    st['best'] = st['c']
                    st['stale'] = 0
            if st['c'] == 0:
                n, edges = _edges(st['S'], T, M, d)
                if lib.is_valid(n, edges, d, D):
                    return n, edges
                st['dead'] = True  # should not happen; keep the search safe


# ---------------------------------------------------------------- generic fallback

def _haar_fallback(d, D, rng, deadline, best):
    """Random Haar-graph search for diameters other than 3."""
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
            if found[0] > best[0] and lib.is_valid(found[0], found[1], d, D):
                best = found
            misses = 0
        else:
            misses += 1
        m += 1
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 <= D.
    kdd = lib.haar_graph(d, range(d))
    if not lib.is_valid(kdd[0], kdd[1], d, D):
        kdd = (1, [])
    best = kdd

    if D == 3:
        # Structured base: projective plane or Araujo-Pardo-Lopez record graph.
        base = None
        q = d - 1
        if q >= 2 and lib.is_prime_power(q):
            base = lib.projective_plane_incidence(q)
        elif d - 2 >= 3 and lib.is_prime_power(d - 2):
            base = lib.araujo_lopez_graph(d - 2)
        if base is not None and lib.is_valid(base[0], base[1], d, D) and base[0] > best[0]:
            best = base

        # Bold change: bi-Cayley graphs over small non-abelian groups, searched
        # for orders 2M above the structured base, ascending in M.
        m_lo = max(best[0] // 2 + 1, d)
        m_hi = lib.moore_bound(d, D) // 2
        for M in range(m_lo, m_hi + 1):
            now = time.monotonic()
            if now >= deadline:
                break
            slice_end = now + (deadline - now) / (m_hi - M + 1)
            res = _search_m(d, D, M, rng, slice_end, deadline)
            if res is not None and res[0] > best[0] and lib.is_valid(res[0], res[1], d, D):
                best = res
    else:
        best = _haar_fallback(d, D, rng, deadline, best)

    if not lib.is_valid(best[0], best[1], d, D):
        return kdd
    return best
