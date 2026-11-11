"""Semi-regular lifts of small bipartite base graphs over finite groups (diameter-5 target, d=6).

Construction: take a base multigraph with b vertices on each side, each of base degree d. Lift it over a
finite group G with dart (A_i -> B_j, g) joining (A_i, x) to (B_j, x*g). The lift is bipartite, d-regular,
and has 2*b*|G| vertices. Left multiplication by G is a group of automorphisms that is transitive on each
side class, so the diameter is at most D iff each of the 2b roots (class representative, identity) reaches
every vertex within D steps. The cost is the sum of unreached counts over those roots, one small BFS per
root, so annealing over voltages is cheap. b = 1 gives Haar graphs; b = 2 and b = 3 are new here.
Every answer is verified with lib.is_valid. The parent's valid 660-vertex Haar graph is the fallback.
"""
import itertools
import math
import time

import numpy as np

import lib

TARGET = (6, 5)


# ----------------------------------------------------------------------------------------- group tables

def _finish(MT):
    """Return (MT, inverse array) for a table whose identity is element 0."""
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k with (a, j) -> index a*k + j and (a, j)(b, l) = (a + lam^j b, j + l)."""
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


def _table_from_coords(elems, mulfun):
    """Table of a group given as an (N, c) coordinate array (element 0 = identity) and a vectorised product."""
    N, c = elems.shape
    base = int(elems.max()) + 1
    wts = base ** np.arange(c, dtype=np.int64)
    codes = elems.astype(np.int64) @ wts
    order = np.argsort(codes)
    sorted_codes = codes[order]
    MT = np.empty((N, N), dtype=np.int32)
    for i in range(N):
        prod = mulfun(elems[i][None, :], elems)
        MT[i] = order[np.searchsorted(sorted_codes, prod.astype(np.int64) @ wts)]
    return _finish(MT)


def group_sl2(p):
    """SL(2, p) for a prime p, matrices (a, b, c, d), order p(p^2-1)."""
    allm = np.array(list(itertools.product(range(p), repeat=4)), dtype=np.int64)
    allm = allm[(allm[:, 0] * allm[:, 3] - allm[:, 1] * allm[:, 2]) % p == 1]
    ident = np.nonzero((allm == np.array([1, 0, 0, 1])).all(axis=1))[0][0]
    allm = np.vstack([allm[ident:ident + 1], np.delete(allm, ident, axis=0)])

    def mul(X, Y):
        a, b, c, d = (X[..., i] for i in range(4))
        e, f, g, h = (Y[..., i] for i in range(4))
        return np.stack([(a * e + b * g) % p, (a * f + b * h) % p,
                         (c * e + d * g) % p, (c * f + d * h) % p], axis=-1)
    return _table_from_coords(allm, mul)


# ------------------------------------------------------------------------- Haar fallback (parent's check)

def haar_edges(MT, S):
    """Edges of the Haar graph: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def checked(MT, S, d, D):
    """The Haar graph for S, or None if it is not exactly valid."""
    n, edges = haar_edges(MT, S)
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        g = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(g[0], g[1], d, D):
            return g
    g = lib.haar_graph(d, range(d))  # complete bipartite K_{d,d}, diameter 1
    if lib.is_valid(g[0], g[1], d, D):
        return g
    return 2, [(0, 1)]


# ------------------------------------------------------------------------ base graphs and lift costs

def metacyclic_for(N, per=2):
    """Non-abelian metacyclic groups Z_m x|_lam Z_k of order N, at most one per k, at most `per` of them."""
    out = []
    for k in range(2, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 3:
            continue
        for lam in range(2, m):
            if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1 % m:
                out.append((m, k, lam))
                break
        if len(out) >= per:
            break
    return out


def connected(b, perms):
    """True if the base graph with edges (i, perm[i]) for each perm is connected."""
    parent = list(range(2 * b))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for p in perms:
        for i in range(b):
            parent[find(i)] = find(b + p[i])
    return len({find(x) for x in range(2 * b)}) == 1


def random_base(b, d, rng):
    """d random permutations of range(b); their sum is a d-regular bipartite base multigraph."""
    while True:
        perms = [list(map(int, rng.permutation(b))) for _ in range(d)]
        if connected(b, perms):
            return perms


def reach(adj, r, D):
    """Number of vertices within distance D of root r."""
    V = adj.shape[0]
    seen = np.zeros(V, dtype=bool)
    seen[r] = True
    fr = np.array([r], dtype=np.int64)
    cnt = 1
    for _ in range(D):
        nb = adj[fr].ravel()
        nb = np.unique(nb[~seen[nb]])
        if nb.size == 0:
            break
        seen[nb] = True
        cnt += int(nb.size)
        fr = nb
    return cnt


def lift_cost(MT, inv, b, N, d, aE, bE, Aidx, Bidx, volt, D):
    """Sum over the 2b class roots of unreached vertices (0 iff the lift has diameter <= D)."""
    xs = np.arange(N)
    nbA = (b + bE[Aidx])[:, None, :] * N + MT[xs[None, :, None], volt[Aidx][:, None, :]]
    nbB = aE[Bidx][:, None, :] * N + MT[xs[None, :, None], inv[volt[Bidx]][:, None, :]]
    adj = np.concatenate([nbA.reshape(b * N, d), nbB.reshape(b * N, d)]).astype(np.int64)
    V = 2 * b * N
    total = 0
    for r in range(2 * b):
        total += V - reach(adj, r * N, D)
    return total


def anneal(MT, inv, b, N, d, D, deadline, rng, T=1.0, patience=2500):
    """Anneal voltages over random base graphs until cost 0 or the deadline. Returns (aE, bE, volt) or None."""
    E = d * b
    while time.monotonic() < deadline:
        perms = random_base(b, d, rng)
        aE = np.array([i for t in range(d) for i in range(b)], dtype=np.int64)
        bE = np.array([perms[t][i] for t in range(d) for i in range(b)], dtype=np.int64)
        Aidx = np.arange(E, dtype=np.int64).reshape(d, b).T              # (b, d)
        Bidx = np.array([[t * b + perms[t].index(j) for t in range(d)]
                         for j in range(b)], dtype=np.int64)              # (b, d)
        volt = rng.integers(0, N, size=E).astype(np.int64)
        cur = lift_cost(MT, inv, b, N, d, aE, bE, Aidx, Bidx, volt, D)
        since = 0
        while time.monotonic() < deadline:
            if cur == 0:
                return aE, bE, volt.copy()
            e = int(rng.integers(E))
            old = int(volt[e])
            volt[e] = int(rng.integers(N))
            c = lift_cost(MT, inv, b, N, d, aE, bE, Aidx, Bidx, volt, D)
            delta = c - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cur = c
                since = 0
            else:
                volt[e] = old
                since += 1
            if since > patience:
                break
    return None


def lift_graph(MT, b, N, d, aE, bE, volt):
    """Edges of the lift: dart (A_i, B_j, g) joins (A_i, x) to (B_j, x*g) for every x."""
    edges = set()
    for e in range(len(volt)):
        i, j, g = int(aE[e]), int(bE[e]), int(volt[e])
        for x in range(N):
            u, v = i * N + x, (b + j) * N + int(MT[x, g])
            edges.add((u, v) if u < v else (v, u))
    return 2 * b * N, sorted(edges)


# ------------------------------------------------------------------------------------------- search

def candidates():
    """(order n, b, group order N, builder) sorted by n: b=2 over metacyclic groups, b=3 over groups and SL(2,5)."""
    out = []
    for N in range(172, 181):
        for m, k, lam in metacyclic_for(N, per=2):
            out.append((4 * N, 2, N, (lambda m=m, k=k, lam=lam: group_meta(m, k, lam))))
    for N in range(115, 121):
        for m, k, lam in metacyclic_for(N, per=1):
            out.append((6 * N, 3, N, (lambda m=m, k=k, lam=lam: group_meta(m, k, lam))))
    out.append((720, 3, 120, lambda: group_sl2(5)))
    out.sort(key=lambda t: t[0])
    return out


def search(d, D, seed, time_limit, best_n):
    """Try candidates in ascending order of n with adaptive time slices; return the largest verified graph."""
    t0 = time.monotonic()
    deadline = t0 + 0.7 * time_limit
    rng = np.random.default_rng(seed)
    cands = candidates()
    best = None
    for idx, (n_target, b, N, builder) in enumerate(cands):
        now = time.monotonic()
        if now >= deadline:
            break
        if n_target <= best_n:
            continue
        left = len(cands) - idx
        slice_ = min(6.0, max(1.0, (deadline - now) / left))
        try:
            MT, inv = builder()
            if MT.shape[0] != N:
                continue
            res = anneal(MT, inv, b, N, d, D, now + slice_, rng)
            if res is None:
                continue
            aE, bE, volt = res
            g = lift_graph(MT, b, N, d, aE, bE, volt)
        except Exception:
            continue
        if g[0] > best_n and lib.is_valid(g[0], g[1], d, D):
            best, best_n = g, g[0]
    return best


# ============================================================================================= build

# Valid smaller Haar graph (order 330, 660 vertices), checked at run time as the safe fallback.
FALLBACK = (lambda: group_meta(33, 10, 26), [0, 179, 116, 180, 47, 306])


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    best = None
    try:
        MT, _ = FALLBACK[0]()
        best = checked(MT, FALLBACK[1], d, D)
    except Exception:
        best = None
    best_n = best[0] if best is not None else 0
    try:
        g = search(d, D, seed, time_limit, best_n)
    except Exception:
        g = None
    if g is not None and (best is None or g[0] > best[0]):
        best = g
    return best if best is not None else trivial(d, D)
