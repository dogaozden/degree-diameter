"""Bold variant for d=6, D=5: multi-orbit voltage lifts over non-abelian groups, with the Haar search kept as a fallback.

THEORY.  Let G be a finite group of order N.  Take a small base bipartite multigraph with NB vertices on
each side and 6 darts per base vertex.  A dart (u, v, g) joins (x, u) to (x*g, v) for every x in G.  Each
base vertex has 6 neighbours, so the lift is 6-regular, bipartite, and has 2*NB*N vertices.  Distinct
voltages are required for darts that share the same base pair (u, v), so that no edge is doubled.

Left translation (x, u) -> (h*x, u) is an automorphism.  So the diameter is at most 5 iff a ball of radius 5
around (e, b) covers the whole graph for every base vertex b.  The cost is the number of uncovered vertices
summed over the 2*NB base representatives, and cost 0 means valid.  The search anneals the voltages with
restarts and round-robin scheduling over several groups of order 172..200 (so 4N > 684).

SAFETY.  Each returned graph is checked with lib.is_valid.  If the lift search fails, the program falls back
to the Haar-graph search (order-342+ groups, a valid smaller Haar graph as a last resort), and finally to a
trivial always-valid graph.
"""
import itertools
import math
import time

import numpy as np

import lib


TARGET = (6, 5)        # the only case that gets the lift construction
NB = 2                 # base vertices per side for the lift
LIFT_FRAC = 0.55       # share of time_limit given to the lift search
PATTERNS = [((3, 3), (3, 3)), ((4, 2), (2, 4)), ((5, 1), (1, 5))]   # regular 6-dart base multiplicities


# ----------------------------------------------------------------------------------------- group tables

def _finish(MT):
    """Return (MT, inverse array) for a table whose identity is element 0."""
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int32)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k with (a, j) -> index a*k + j and (a, j)(b, l) = (a + lam^j b, j + l).  Needs lam^k = 1 mod m."""
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
    """Table of a group given as an (N, c) integer coordinate array (element 0 = identity) and a vectorised product."""
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
    """Heisenberg group mod p, order p^3."""
    e = np.array(list(itertools.product(range(p), repeat=3)), dtype=np.int64)

    def mul(X, Y):
        return np.stack([(X[..., 0] + Y[..., 0]) % p, (X[..., 1] + Y[..., 1]) % p,
                         (X[..., 2] + Y[..., 2] + X[..., 0] * Y[..., 1]) % p], axis=-1)
    return _table_from_coords(e, mul)


def group_agl(q, k=None):
    """GF(q) x| C_k (default AGL(1, q)), q a prime power."""
    F = lib.GF(q)
    k = q - 1 if k is None else k
    H = [a for a in range(1, q) if F.pow(a, k) == 1]
    assert len(H) == k
    e = np.array([(0, 1)] + [(b, a) for b in range(q) for a in H if (b, a) != (0, 1)], dtype=np.int64)
    add, mulT = F.add_table, F.mul_table

    def mul(X, Y):
        return np.stack([add[X[..., 0], mulT[X[..., 1], Y[..., 0]]], mulT[X[..., 1], Y[..., 1]]], axis=-1)
    return _table_from_coords(e, mul)


def group_times_cyclic(grp, k):
    """Direct product of a table group (MT, inv) with Z_k; element (g, c) has index g*k + c."""
    MT0, _ = grp
    n0 = MT0.shape[0]
    c = np.arange(k, dtype=np.int64)
    MT = np.empty((n0 * k, n0 * k), dtype=np.int32)
    for g in range(n0):
        MT[g * k:(g + 1) * k] = (MT0[g][None, :, None] * k + (c[:, None, None] + c[None, None, :]) % k).reshape(k, n0 * k)
    return _finish(MT)


def metacyclic_candidates(lo, hi, limit):
    """Non-abelian metacyclic groups Z_m x|_lam Z_k with lo <= m*k <= hi, one per (m, k), smallest order first."""
    out = []
    for N in range(lo, hi + 1):
        for k in range(2, N):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            for lam in range(2, m):
                if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1 % m:
                    out.append((f"Z_{m} x| Z_{k} (lam={lam}), order {N}", N, m, k, lam))
                    break
            if len(out) >= limit:
                return out
    return out


# ================================================================================ lift construction

def make_pairs(M):
    """Dart list for a base multiplicity matrix M (NB x NB): one entry (u, v) per dart."""
    return [(u, v) for u in range(NB) for v in range(NB) for _ in range(M[u][v])]


def lift_adj(MT, inv, pairs, V):
    """Adjacency array (n, 6) of the lift.  A base u -> ids u*N + x; B base v -> ids (NB+v)*N + y."""
    N = MT.shape[0]
    n = 2 * NB * N
    deg = len(pairs) * 2 // (2 * NB)
    adj = np.empty((n, deg), dtype=np.int64)
    colA = [0] * NB
    colB = [0] * NB
    x = np.arange(N)
    for (u, v), g in zip(pairs, V):
        adj[u * N:(u + 1) * N, colA[u]] = (NB + v) * N + MT[x, g]
        colA[u] += 1
        adj[(NB + v) * N:(NB + v + 1) * N, colB[v]] = u * N + MT[x, inv[g]]
        colB[v] += 1
    return adj


def lift_cost(adj, sources, D):
    """Uncovered vertices, summed over the ball of radius D around each base representative (0 = valid)."""
    n = adj.shape[0]
    total = 0
    for s in sources:
        reach = np.zeros(n, dtype=bool)
        reach[s] = True
        frontier = np.array([s], dtype=np.int64)
        for _ in range(D):
            nb = adj[frontier].ravel()
            nb = nb[~reach[nb]]
            if nb.size == 0:
                break
            nb = np.unique(nb)
            reach[nb] = True
            frontier = nb
        total += n - int(reach.sum())
    return total


def lift_edges(MT, pairs, V):
    """Edge list of the lift for voltages V."""
    N = MT.shape[0]
    x = np.arange(N)
    edges = []
    for (u, v), g in zip(pairs, V):
        col = MT[x, g].tolist()
        for xi, yi in zip(range(N), col):
            edges.append((u * N + xi, (NB + v) * N + yi))
    return 2 * NB * N, edges


def lift_search(MT, inv, pairs, D, deadline, rng, V0):
    """Annealing over the voltages of one lift, with restarts.  Returns (best V, best cost)."""
    N = MT.shape[0]
    P = len(pairs)
    sources = [i * N for i in range(2 * NB)]
    groups = {}
    for t, key in enumerate(pairs):
        groups.setdefault(key, []).append(t)
    group_of = [groups[key] for key in pairs]

    def fresh():
        V = np.zeros(P, dtype=np.int64)
        for idx in groups.values():
            V[idx] = rng.choice(N, len(idx), replace=False)
        return V

    def score(V):
        return lift_cost(lift_adj(MT, inv, pairs, V), sources, D)

    V = fresh() if V0 is None else np.array(V0, dtype=np.int64)
    cur = score(V)
    best, bestc = V.copy(), cur
    if cur == 0:
        return best, 0
    temp, since = 1.5, 0
    while time.monotonic() < deadline:
        t = int(rng.integers(P))
        others = [int(V[s]) for s in group_of[t] if s != t]
        g = int(rng.integers(N))
        if g in others:
            continue
        W = V.copy()
        W[t] = g
        c = score(W)
        delta = c - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            V, cur = W, c
            if cur < bestc:
                best, bestc, since = V.copy(), cur, 0
            if cur == 0:
                return best, 0
        since += 1
        if since > 3000:
            V = fresh()
            cur = score(V)
            since = 0
            if cur < bestc:
                best, bestc = V.copy(), cur
            if cur == 0:
                return best, 0
    return best, bestc


def lift_run(d, D, deadline, rng):
    """Round-robin lift search over groups of order 172..200 and several base patterns.
    Returns a checked (n, edges) or None."""
    specs = []
    for _name, _N, m, k, lam in metacyclic_candidates(172, 200, 14):
        specs.append((lambda m=m, k=k, lam=lam: group_meta(m, k, lam)))
    specs.append(lambda: group_times_cyclic(group_agl(5), 9))     # order 180
    specs.append(lambda: group_times_cyclic(group_agl(5), 10))    # order 200

    states = []
    for i, builder in enumerate(specs):
        if time.monotonic() >= deadline:
            break
        try:
            MT, inv = builder()
        except Exception:
            continue
        if MT.shape[0] < 172:
            continue
        pairs = make_pairs(PATTERNS[i % len(PATTERNS)])
        states.append({"MT": MT, "inv": inv, "pairs": pairs, "best": None, "bestc": None})

    slice_t = 0.5
    while states and time.monotonic() < deadline:
        for st in states:
            now = time.monotonic()
            if now >= deadline:
                break
            end = min(deadline, now + slice_t)
            try:
                V, c = lift_search(st["MT"], st["inv"], st["pairs"], D, end, rng, st["best"])
            except Exception:
                continue
            if st["bestc"] is None or c < st["bestc"]:
                st["best"], st["bestc"] = V, c
            if c == 0:
                n, edges = lift_edges(st["MT"], st["pairs"], V)
                if lib.is_valid(n, edges, d, D):
                    return n, edges
        slice_t *= 1.5
    return None


# ================================================================================ Haar fallback

def _cover(MT, N, P):
    """Boolean array of the elements covered by the products P[i]*P[j]."""
    cov = np.zeros(N, dtype=bool)
    cov[MT[P[:, None], P[None, :]].ravel()] = True
    return cov


def _pairs(MT, inv, S):
    Si = inv[S]
    return MT[Si[:, None], S[None, :]].ravel(), MT[S[:, None], Si[None, :]].ravel()


def cost(MT, inv, S):
    N = MT.shape[0]
    return sum(N - int(_cover(MT, N, np.unique(P)).sum()) for P in _pairs(MT, inv, S))


def batch_costs(MT, inv, S, i, X):
    N = MT.shape[0]
    K = len(X)
    rest = np.delete(S, i)
    total = np.zeros(K, dtype=np.int64)
    offs = (np.arange(K, dtype=np.int64) * N)[:, None]
    ri = inv[rest]
    for side in (0, 1):
        F = np.unique(MT[ri[:, None], rest[None, :]] if side == 0 else MT[rest[:, None], ri[None, :]])
        base = _cover(MT, N, F)
        xi = inv[X]
        if side == 0:
            Q = np.concatenate([MT[xi[:, None], rest[None, :]], MT[ri[None, :], X[:, None]]], axis=1)
        else:
            Q = np.concatenate([MT[X[:, None], ri[None, :]], MT[rest[None, :], xi[:, None]]], axis=1)
        W = np.concatenate([MT[Q[:, :, None], F[None, None, :]].reshape(K, -1),
                            MT[F[None, None, :], Q[:, :, None]].reshape(K, -1),
                            MT[Q[:, :, None], Q[:, None, :]].reshape(K, -1)], axis=1)
        new = ~base[W]
        flat = (W + offs)[new]
        cnt = np.bincount(flat, minlength=K * N).reshape(K, N)
        total += N - int(base.sum()) - (cnt > 0).sum(axis=1)
    return total


def search(MT, inv, d, S0, deadline, rng, K=24, temp=0.45, patience=4000):
    N = MT.shape[0]
    S0 = None if S0 is None else np.array(S0, dtype=np.int32)
    best, bestc = None, 10 ** 9
    S, cur, since = S0.copy() if S0 is not None else None, None, 0

    def random_set():
        return np.concatenate([[0], rng.choice(np.arange(1, N), d - 1, replace=False)]).astype(np.int32)

    if S0 is not None:
        c0 = cost(MT, inv, S0)
        best, bestc = S0.copy(), c0
        if c0 == 0:
            return best, 0
    while time.monotonic() < deadline:
        if S is None:
            if S0 is not None and rng.random() < 0.5:
                S = S0.copy()
                for i in rng.choice(d, 2, replace=False):
                    S[i] = rng.integers(N)
                if len(set(S.tolist())) < d:
                    S = random_set()
            else:
                S = random_set()
        if cur is None:
            cur = cost(MT, inv, S)
            since = 0
            if cur < bestc:
                best, bestc = S.copy(), cur
            if cur == 0:
                return best, 0
        i = int(rng.integers(d))
        X = rng.integers(0, N, size=K).astype(np.int32)
        X = X[~np.isin(X, np.delete(S, i))]
        if len(X) == 0:
            continue
        cs = batch_costs(MT, inv, S, i, X)
        j = int(np.argmin(cs + rng.random(len(cs)) * 0.5))
        delta = int(cs[j]) - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            S[i] = X[j]
            cur = int(cs[j])
            if cur < bestc:
                best, bestc, since = S.copy(), cur, 0
                if cur == 0:
                    return best, 0
            elif delta < 0:
                since = 0
        since += 1
        if since > patience:
            S, cur = None, None
    return best, bestc


def haar_edges(MT, S):
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def checked(MT, S, d, D):
    n, edges = haar_edges(MT, S)
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


def run(d, D, seed, time_limit, plan, fallback):
    """Round-robin Haar search; returns a checked graph or the fallback or trivial."""
    t0 = time.monotonic()
    deadline_all = t0 + 0.80 * time_limit
    rng = np.random.default_rng(seed)

    states = []
    for name, builder, S0, w in plan:
        if time.monotonic() >= deadline_all:
            break
        try:
            MT, inv = builder()
        except Exception:
            continue
        states.append({"MT": MT, "inv": inv, "best": S0, "bestc": None})

    slice_t = 0.5
    while states and time.monotonic() < deadline_all:
        for st in states:
            now = time.monotonic()
            if now >= deadline_all:
                break
            end = min(deadline_all, now + slice_t)
            try:
                S, c = search(st["MT"], st["inv"], d, st["best"], end, rng)
            except Exception:
                continue
            if S is None:
                continue
            if st["bestc"] is None or c < st["bestc"]:
                st["best"], st["bestc"] = S, c
            if c == 0:
                g = checked(st["MT"], S, d, D)
                if g is not None:
                    return g
        slice_t *= 1.5

    try:
        MT, inv = fallback[0]()
        g = checked(MT, fallback[1], d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)


def haar_plan():
    plan = [
        ('Heis(3) x Z_13, order 351', lambda: group_times_cyclic(group_heis(3), 13), None, 1),
        ('Heis(7), order 343', lambda: group_heis(7), None, 1),
        ('AGL(1,9) x Z_5, order 360', lambda: group_times_cyclic(group_agl(9), 5), None, 1),
        ('AGL(1,5) x Z_18, order 360', lambda: group_times_cyclic(group_agl(5), 18), None, 1),
    ]
    for _name, _N, _m, _k, _lam in metacyclic_candidates(342, 372, 10):
        plan.append((_name, (lambda m=_m, k=_k, lam=_lam: group_meta(m, k, lam)), None, 1))
    return plan


FALLBACK = (lambda: group_meta(33, 10, 26), [0, 179, 116, 180, 47, 306])


# ================================================================================ entry point

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    rng = np.random.default_rng(seed)
    try:
        res = lift_run(d, D, t0 + LIFT_FRAC * time_limit, rng)
        if res is not None:
            return res
    except Exception:
        pass
    remaining = 0.8 * time_limit - (time.monotonic() - t0)
    if remaining > 0.5:
        try:
            return run(d, D, seed, remaining / 0.8, haar_plan(), FALLBACK)
        except Exception:
            pass
    return trivial(d, D)
