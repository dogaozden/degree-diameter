"""Bold variant for d=10, D=5: voltage lifts of a 2+2 base multigraph over non-cyclic groups.

Base graph: A-vertices 0..B-1 and B-vertices B..2B-1, with B=2. Each base dart (i, j, g) joins fibre i to
fibre B+j through group voltage g. Left multiplication by any h in G is an automorphism of the lift, so
every vertex in a fibre looks like (e, w). The diameter is therefore at most D iff BFS from the four
representatives (e, w) reaches all vertices within D steps. The search is simulated annealing over the
voltages; the cost is the number of unreached (representative, vertex) pairs.

Safety: a candidate is returned only after lib.is_valid accepts it. If nothing is found in the budget,
the older valid Haar graph (order 1791 per side) is used, and then a small always-valid graph.
"""
import math
import time

import numpy as np

import lib

TARGET = (10, 5)
D_DEG = 10
D_DIAM = 5
B = 2               # base vertices per side
PATIENCE = 3000     # moves without improvement before a restart
TEMP = 2.0


# ----------------------------------------------------------------------------------------- group tables

def _finish(MT):
    """Return (MT, inverse array) for a table whose identity is element 0."""
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int32)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k with (a, j) -> index a*k + j.  Needs lam^k = 1 mod m and gcd(lam, m) = 1."""
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
    """Table of a group given by coordinate rows (identity first) and a vectorised product."""
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


def group_heis(p):
    """Heisenberg group mod p, order p^3, identity first."""
    e = np.array(list(__import__("itertools").product(range(p), repeat=3)), dtype=np.int64)

    def mul(X, Y):
        return np.stack([(X[..., 0] + Y[..., 0]) % p, (X[..., 1] + Y[..., 1]) % p,
                         (X[..., 2] + Y[..., 2] + X[..., 0] * Y[..., 1]) % p], axis=-1)
    return _table_from_coords(e, mul)


def group_sl2(p):
    """SL(2, p) for a prime p, order p(p^2-1), identity first."""
    import itertools
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


def group_agl(q):
    """AGL(1, q) for a prime power q, order q(q-1), identity first."""
    F = lib.GF(q)
    H = [a for a in range(1, q)]
    e = np.array([(0, 1)] + [(b, a) for b in range(q) for a in H if (b, a) != (0, 1)], dtype=np.int64)
    add, mulT = F.add_table, F.mul_table

    def mul(X, Y):
        return np.stack([add[X[..., 0], mulT[X[..., 1], Y[..., 0]]], mulT[X[..., 1], Y[..., 1]]], axis=-1)
    return _table_from_coords(e, mul)


def candidate_groups(rng):
    """Shuffled list of (name, builder) for groups of order about 1000-1340."""
    cands = [
        ("heis11", lambda: group_heis(11)),
        ("sl2_11", lambda: group_sl2(11)),
        ("agl37", lambda: group_agl(37)),
    ]
    metas = []
    for N in range(1001, 1013):
        for k in range(2, N):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            for lam in range(2, m):
                if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1:
                    metas.append((m, k, lam))
    if metas:
        for t in rng.permutation(len(metas))[:3]:
            m, k, lam = metas[int(t)]
            cands.append((f"meta{m}x{k}r{lam}",
                          lambda m=m, k=k, lam=lam: group_meta(m, k, lam)))
    order = rng.permutation(len(cands))
    return [cands[int(i)] for i in order]


# ----------------------------------------------------------------------------- lift search machinery

def lift_nb(MT, inv, P, G, N):
    """Neighbour table of the lift: row w*N+x lists the D_DEG neighbours of vertex (w, x)."""
    total = 2 * B * N
    NB = np.empty((total, D_DEG), dtype=np.int64)
    slot = [0] * (2 * B)
    x = np.arange(N, dtype=np.int64)
    for (i, j), g in zip(P.tolist(), G.tolist()):
        a = i
        bv = B + j
        gi = int(inv[g])
        NB[a * N + x, slot[a]] = bv * N + MT[x, g]
        NB[bv * N + x, slot[bv]] = a * N + MT[x, gi]
        slot[a] += 1
        slot[bv] += 1
    return NB


def ecc_cost(NB, N):
    """Unreached (representative, vertex) pairs at distance > D_DIAM, over the 2B fibre representatives."""
    total = NB.shape[0]
    cost = 0
    for w in range(2 * B):
        src = w * N
        seen = np.zeros(total, dtype=bool)
        seen[src] = True
        front = np.array([src], dtype=np.int64)
        for _ in range(D_DIAM):
            nb = NB[front].ravel()
            nb = nb[~seen[nb]]
            if nb.size == 0:
                break
            nb = np.unique(nb)
            seen[nb] = True
            front = nb
        cost += total - int(seen.sum())
    return cost


def anneal(MT, inv, N, rng, deadline):
    """Simulated annealing over voltages of a 2+2 base multigraph with block pattern [[k,10-k],[10-k,k]]."""
    k = int(rng.choice([4, 5, 6]))
    blocks = [[k, D_DEG - k], [D_DEG - k, k]]
    pairs = []
    for i in range(B):
        for j in range(B):
            pairs += [(i, j)] * blocks[i][j]
    P = np.array(pairs, dtype=np.int64)
    T = len(P)
    blk = P[:, 0] * B + P[:, 1]
    members = [np.nonzero(blk == b)[0] for b in range(B * B)]

    def fresh():
        G = np.empty(T, dtype=np.int64)
        for idx in members:
            G[idx] = rng.choice(N, size=len(idx), replace=False)
        return G

    def cost(G):
        return ecc_cost(lift_nb(MT, inv, P, G, N), N)

    G = fresh()
    cur = cost(G)
    best_c, best_G = cur, G.copy()
    since = 0
    while best_c > 0 and time.monotonic() < deadline:
        t = int(rng.integers(T))
        v = int(rng.integers(N))
        same = members[int(blk[t])]
        if np.any(G[same] == v):
            continue
        old = G[t]
        G[t] = v
        c = cost(G)
        delta = c - cur
        if delta <= 0 or rng.random() < math.exp(-delta / TEMP):
            cur = c
            if c < best_c:
                best_c, best_G = c, G.copy()
                since = 0
        else:
            G[t] = old
        since += 1
        if since > PATIENCE:
            G = fresh()
            cur = cost(G)
            since = 0
    return best_c, P, best_G


def lift_edges(MT, P, G, N):
    """Edge list of the lift: fibre i is vertices i*N..i*N+N-1, fibre B+j follows."""
    x = np.arange(N, dtype=np.int64)
    edges = []
    for (i, j), g in zip(P.tolist(), G.tolist()):
        a = i
        bv = B + j
        ys = MT[x, g].astype(np.int64)
        edges.extend(zip((a * N + x).tolist(), (bv * N + ys).tolist()))
    return 2 * B * N, edges


# --------------------------------------------------------------------- Haar fallback and trivial graphs

def haar_edges(MT, S):
    """Edges of the Haar graph: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def checked(MT, S, d, D):
    n, edges = haar_edges(MT, S)
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    try:
        if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
            n, edges = lib.projective_plane_incidence(d - 1)
            if lib.is_valid(n, edges, d, D):
                return n, edges
    except Exception:
        pass
    try:
        if D >= 2 and d >= 1:
            n, edges = lib.haar_graph(d, range(d))   # K_{d,d}, diameter 2
            if lib.is_valid(n, edges, d, D):
                return n, edges
    except Exception:
        pass
    if D >= 1 and d >= 1:
        return 2, [(0, 1)]
    return 1, []


FALLBACK_S = [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)

    t0 = time.monotonic()
    deadline = t0 + 0.75 * time_limit
    rng = np.random.default_rng(seed)
    cands = candidate_groups(rng)

    for idx, (name, builder) in enumerate(cands):
        now = time.monotonic()
        if now >= deadline:
            break
        slice_end = now + (deadline - now) / (len(cands) - idx)
        try:
            MT, inv = builder()
            N = MT.shape[0]
            c, P, G = anneal(MT, inv, N, rng, slice_end)
        except Exception:
            continue
        if c == 0:
            try:
                n, edges = lift_edges(MT, P, G, N)
                if lib.is_valid(n, edges, d, D):
                    return n, edges
            except Exception:
                pass

    # Safe fallback: valid Haar graph of order 2*1791.
    try:
        MT, _ = group_meta(199, 9, 180)
        g = checked(MT, FALLBACK_S, d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)
