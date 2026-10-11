import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Multi-orbit group voltage lifts with a bipartite base, searched by annealing.
#
# Vertices: A_{i,g} = i*G + g and B_{j,h} = k*G + j*G + h, with i, j in 0..k-1
# and g, h in a group G of order G (element 0 is the identity).
# Layer L (0..d-1) is a permutation sig_L of 0..k-1 plus a voltage s_{L,i} in G
# for each i, giving the edge A_{i,g} -- B_{sig_L(i), g*s_{L,i}}.
#
# Every A and B vertex then has degree exactly d, and the graph is bipartite.
# Left multiplication by h is an automorphism, so the diameter is at most D iff
# every orbit representative (A_{i,1}, B_{j,1}) reaches all vertices within D steps.
# Simple-graph condition: for each i, the pairs (sig_L(i), s_{L,i}) over L are distinct.
# ----------------------------------------------------------------------------


def _fallback(d):
    """K_{d,d}: diameter 2, valid for every D >= 2 (and for D = 1 it is only a fallback)."""
    return lib.haar_graph(d, range(d))


def _structured(d, D):
    """Known structured candidates for D >= 3. Each is returned as (n, edges) and checked later."""
    out = []
    if D >= 3:
        try:
            if lib.is_prime_power(d - 1):
                out.append(lib.projective_plane_incidence(d - 1))
        except Exception:
            pass
        try:
            q = d - 2
            if q >= 3 and lib.is_prime_power(q):
                out.append(lib.araujo_lopez_graph(q))
        except Exception:
            pass
    return out


def _sample_group(G, rng):
    """Return (M, invG): multiplication table and inverse array of a group of order G, or None."""
    ar = np.arange(G)
    cyclic = ((ar[:, None] + ar[None, :]) % G, (-ar) % G)
    if G < 4 or rng.random() < 0.45:
        return cyclic
    divs = [k2 for k2 in range(2, G) if G % k2 == 0 and G // k2 >= 2]
    if not divs:
        return cyclic
    k2 = rng.choice(divs)
    m = G // k2
    cands = [r for r in range(2, m) if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
    if not cands:
        return cyclic
    r = rng.choice(cands)
    try:
        order, mul, inv = lib.semidirect_group(m, k2, r)
    except ValueError:
        return cyclic
    if order != G:
        return cyclic
    M = np.array([[mul(x, y) for y in range(G)] for x in range(G)], dtype=np.int64)
    invG = np.array([inv(x) for x in range(G)], dtype=np.int64)
    return M, invG


def _adj(k, G, M, invG, SIG, S, d):
    """Adjacency array (2kG, d): column L is the unique neighbour in layer L."""
    N = 2 * k * G
    ar = np.arange(G)
    adj = np.empty((N, d), dtype=np.int64)
    for L in range(d):
        sig = SIG[L]
        sinv = [0] * k
        for i in range(k):
            sinv[sig[i]] = i
        for i in range(k):
            adj[i * G:(i + 1) * G, L] = k * G + sig[i] * G + M[ar, S[L][i]]
        for j in range(k):
            i = sinv[j]
            adj[k * G + j * G:k * G + (j + 1) * G, L] = i * G + M[ar, invG[S[L][i]]]
    return adj


def _cost(adj, k, G, D):
    """Unreached (orbit representative, vertex) pairs within D steps. Zero means valid."""
    N = adj.shape[0]
    nsrc = 2 * k
    src = [i * G for i in range(k)] + [k * G + j * G for j in range(k)]
    R = np.zeros((N, nsrc), dtype=bool)
    R[src, np.arange(nsrc)] = True
    for _ in range(D):
        new = R.copy()
        for L in range(adj.shape[1]):
            new |= R[adj[:, L]]
        R = new
    return N * nsrc - int(R.sum())


def _row_ok(SIG, S, d, i):
    """True if the d pairs (sig_L(i), s_{L,i}) are distinct, so no parallel edges arise at i."""
    seen = set()
    for L in range(d):
        p = (SIG[L][i], S[L][i])
        if p in seen:
            return False
        seen.add(p)
    return True


def _swap(lst, a, b):
    lst[a], lst[b] = lst[b], lst[a]


def _anneal(d, D, k, G, M, invG, rng, deadline):
    """Simulated annealing over voltages and layer permutations. Returns (SIG, S, adj) or None."""
    SIG = []
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        SIG.append(p)
    S = [[0] * k for _ in range(d)]
    for i in range(k):
        used = set()
        for L in range(d):
            while True:
                s = rng.randrange(G)
                if (SIG[L][i], s) not in used:
                    break
            used.add((SIG[L][i], s))
            S[L][i] = s

    adj = _adj(k, G, M, invG, SIG, S, d)
    c = _cost(adj, k, G, D)
    T = 1.5
    while c > 0 and time.monotonic() < deadline:
        T = max(0.08, T * 0.9995)
        if k > 1 and rng.random() < 0.3:
            kind = 'swap'
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            _swap(SIG[L], a, b)
            if not (_row_ok(SIG, S, d, a) and _row_ok(SIG, S, d, b)):
                _swap(SIG[L], a, b)
                continue
        else:
            kind = 'volt'
            L = rng.randrange(d)
            i = rng.randrange(k)
            old = S[L][i]
            new = rng.randrange(G)
            if new == old:
                continue
            S[L][i] = new
            if not _row_ok(SIG, S, d, i):
                S[L][i] = old
                continue
        adj2 = _adj(k, G, M, invG, SIG, S, d)
        c2 = _cost(adj2, k, G, D)
        if c2 <= c or rng.random() < math.exp((c - c2) / T):
            c = c2
            adj = adj2
        else:
            if kind == 'swap':
                _swap(SIG[L], a, b)
            else:
                S[L][i] = old
    if c == 0:
        return SIG, S, adj
    return None


def _to_graph(adj, k, G):
    """Edge list of the lift: every A row lists its d neighbours (all B vertices)."""
    nA = k * G
    d = adj.shape[1]
    rows = np.repeat(np.arange(nA), d)
    cols = adj[:nA].ravel()
    return 2 * k * G, list(zip(rows.tolist(), cols.tolist()))


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + min(0.85 * time_limit, time_limit - 3.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    fb = _fallback(d)
    best_n, best_e = fb[0], fb[1]

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    if D == 2:
        return best_n, best_e

    for n_c, e_c in _structured(d, D):
        consider(n_c, e_c)

    moore = lib.moore_bound(d, D)
    if best_n >= moore or d < 3:
        return (best_n, best_e) if lib.is_valid(best_n, best_e, d, D) else fb

    try:
        ks = [1, 2, 2, 3, 3, 4, 5, 6]
        while time.monotonic() < deadline and best_n < moore:
            k = rng.choice(ks)
            base = (best_n + 2 + 2 * k - 1) // (2 * k)
            G = base + rng.randint(0, 3)
            if G < d + 2:
                G = d + 2
            grp = _sample_group(G, rng)
            if grp is None:
                continue
            M, invG = grp
            att_deadline = min(deadline, time.monotonic() + 4.0)
            res = _anneal(d, D, k, G, M, invG, rng, att_deadline)
            if res is not None:
                _, _, adj = res
                n, e = _to_graph(adj, k, G)
                consider(n, e)
    except Exception:
        pass

    if not lib.is_valid(best_n, best_e, d, D):
        return fb
    return best_n, best_e
