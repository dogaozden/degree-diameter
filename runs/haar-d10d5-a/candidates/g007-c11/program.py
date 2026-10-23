"""Bold variant for (d, D) = (10, 5): multi-base voltage lifts over metacyclic groups, with the Haar fallback kept.

NEW CONSTRUCTION.  Use a bipartite base multigraph with p vertices on each side and a finite group G of order N.
Dart (i, j, g) joins (A_i, x) to (B_j, x*g) for every x in G.  The lift has 2pN vertices and is d-regular and
bipartite.  Left multiplication by G is an automorphism, so the vertex orbits are the 2p base vertices.  The
diameter is at most 5 iff every one of the 2p representatives (A_i, e), (B_j, e) reaches all vertices within 5
steps.  That gives an exact cost, the number of uncovered (representative, vertex) pairs.  Simulated annealing
moves single voltages.  The base is circulant: each side's blocks have sizes summing to d, so the base is
connected.  Shapes are p = 2..5 with group orders chosen so that 2pN > 4000 (beating the record of 4000).
Every candidate is checked with lib.is_valid before it is returned.

FALLBACK.  The verified Haar graph over Z_199 x| Z_9 (3582 vertices), checked with lib.is_valid.
"""
import math
import time

import numpy as np

import lib

TARGET = (10, 5)


# ----------------------------------------------------------------------------- groups

def _finish(MT):
    """Return (MT, inverse array) for a table whose identity is element 0."""
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int32)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k with index a*k + j for (a, j); (a, j)(b, l) = (a + lam^j b, j + l).  Needs lam^k = 1 mod m."""
    assert pow(lam, k, m) == 1 % m
    pw = np.array([pow(lam, j, m) for j in range(k)], dtype=np.int64)
    N = m * k
    g = np.arange(N, dtype=np.int64)
    a, j = g // k, g % k
    MT = np.empty((N, N), dtype=np.int32)
    for lo in range(0, N, 256):
        hi = min(N, lo + 256)
        MT[lo:hi] = ((a[lo:hi, None] + pw[j[lo:hi], None] * a[None, :]) % m) * k + (j[lo:hi, None] + j[None, :]) % k
    return _finish(MT)


_GROUPS = {}


def get_group(key):
    """Cached (MT, inv) for the metacyclic key (m, k, lam)."""
    if key not in _GROUPS:
        _GROUPS[key] = group_meta(*key)
    return _GROUPS[key]


def metacyclic_nonabelian(N):
    """All (m, k, lam) with m*k = N, lam nontrivial, gcd(lam, m) = 1 and lam^k = 1 mod m."""
    out = []
    for k in range(2, N + 1):
        if N % k:
            continue
        m = N // k
        for lam in range(2, m):
            if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1 % m:
                out.append((m, k, lam))
    return out


def make_tasks():
    """One task per (base size p, group order N).  2pN must exceed 4000."""
    tasks = []
    for p, want in ((2, 3), (3, 2), (4, 1), (5, 1)):
        nmin = 2000 // p + 1
        got, N = 0, nmin
        while got < want and N < nmin + 300:
            groups = metacyclic_nonabelian(N)
            if groups:
                tasks.append({'p': p, 'N': N, 'groups': groups, 'best': None, 'best_cost': 10 ** 18})
                got += 1
            N += 1
    return tasks


# ----------------------------------------------------------------------------- lift model

def random_pattern(p, d, rng):
    """Positive composition of d into p parts (the circulant block pattern)."""
    cuts = sorted(int(c) for c in rng.choice(np.arange(1, d), p - 1, replace=False))
    bounds = [0] + cuts + [d]
    return [bounds[t + 1] - bounds[t] for t in range(p)]


def random_pairs(p, d, N, rng):
    """pairs[(i, j)] = list of distinct voltages; block sizes c_ij = pattern[(j - i) % p] give row/column sums d."""
    pat = random_pattern(p, d, rng)
    pairs = {}
    for i in range(p):
        for j in range(p):
            c = pat[(j - i) % p]
            pairs[(i, j)] = [int(x) for x in rng.choice(N, c, replace=False)]
    return pairs


def mutate(pairs, keys, N, rng):
    """Replace one voltage by a new one not already used on the same pair.  Returns (key, slot, old value)."""
    key = keys[int(rng.integers(len(keys)))]
    gs = pairs[key]
    t = int(rng.integers(len(gs)))
    old = gs[t]
    while True:
        g = int(rng.integers(N))
        if g not in gs:
            break
    gs[t] = g
    return key, t, old


def build_nbr(MT, inv, p, N, d, pairs):
    """Neighbour table (2pN, d).  A_i,x has index i*N + x; B_j,y has index p*N + j*N + y."""
    nbr = np.empty((2 * p * N, d), dtype=np.int64)
    ka = [0] * p
    kb = [0] * p
    for (i, j), gs in pairs.items():
        for g in gs:
            nbr[i * N:(i + 1) * N, ka[i]] = p * N + j * N + MT[:, g]
            ka[i] += 1
            nbr[p * N + j * N:p * N + (j + 1) * N, kb[j]] = i * N + MT[:, inv[g]]
            kb[j] += 1
    return nbr


def uncovered(nbr, reps, D):
    """Total number of vertices not reached within D steps, summed over the representatives."""
    V = nbr.shape[0]
    total = 0
    for s in reps:
        seen = np.zeros(V, dtype=bool)
        seen[s] = True
        frontier = np.array([s], dtype=np.int64)
        for _ in range(D):
            nb = nbr[frontier].ravel()
            nb = np.unique(nb[~seen[nb]])
            if nb.size == 0:
                break
            seen[nb] = True
            frontier = nb
        total += V - int(np.count_nonzero(seen))
    return total


def lift_graph(nbr, p, N, d):
    """(n, edges) from the neighbour table, listing each edge once from its A side."""
    V = nbr.shape[0]
    us = np.repeat(np.arange(p * N, dtype=np.int64), d)
    vs = nbr[:p * N].ravel()
    return V, list(zip(us.tolist(), vs.tolist()))


def episode(task, rng, deadline, steps, d, D, T=3.0):
    """One annealing run for a task.  Returns (n, edges) if a checked valid lift is found, else None."""
    p, N = task['p'], task['N']
    if task['best'] is not None and rng.random() < 0.5:
        gkey, start = task['best']
        pairs = {key: list(v) for key, v in start.items()}
        keys0 = list(pairs.keys())
        for _ in range(3):
            mutate(pairs, keys0, N, rng)
    else:
        gkey = task['groups'][int(rng.integers(len(task['groups'])))]
        pairs = random_pairs(p, d, N, rng)
    keys = list(pairs.keys())
    MT, inv = get_group(gkey)
    reps = [i * N for i in range(p)] + [p * N + j * N for j in range(p)]
    cur = uncovered(build_nbr(MT, inv, p, N, d, pairs), reps, D)
    for _ in range(steps):
        if time.monotonic() >= deadline:
            break
        key, t, old = mutate(pairs, keys, N, rng)
        nbr = build_nbr(MT, inv, p, N, d, pairs)
        new = uncovered(nbr, reps, D)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = new
            if cur < task['best_cost']:
                task['best_cost'] = cur
                task['best'] = (gkey, {kk: list(v) for kk, v in pairs.items()})
            if cur == 0:
                V, edges = lift_graph(nbr, p, N, d)
                if lib.is_valid(V, edges, d, D):
                    return V, edges
        else:
            pairs[key][t] = old
    return None


def run_lifts(d, D, seed, time_limit):
    """Round-robin the tasks until the budget is spent or a valid lift is found."""
    deadline = time.monotonic() + 0.72 * time_limit
    rng = np.random.default_rng(seed)
    tasks = make_tasks()
    if not tasks:
        return None
    while time.monotonic() < deadline:
        for task in tasks:
            if time.monotonic() >= deadline:
                break
            try:
                res = episode(task, rng, deadline, 1500, d, D)
            except Exception:
                res = None
            if res is not None:
                return res
    return None


# ----------------------------------------------------------------------------- fallbacks

def haar_checked(MT, S, d, D):
    """The Haar graph for S (A-vertex g is g, B-vertex g is N+g), or None if it fails lib.is_valid."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    n = 2 * N
    edges = [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


FALLBACK_S = [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


# ----------------------------------------------------------------------------- entry point

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    try:
        res = run_lifts(d, D, seed, time_limit)
    except Exception:
        res = None
    if res is not None:
        return res
    try:
        MT, _ = group_meta(199, 9, 180)
        g = haar_checked(MT, FALLBACK_S, d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)
