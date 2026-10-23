"""Two-stage search for the bipartite degree-diameter case d=6, D=5.

Stage A (Haar graphs, unchanged from the parent): search connection sets S in non-abelian groups.
The graph has 2|G| vertices, and cost 0 means diameter 5.

Stage B (new, bold): multi-orbit bi-Cayley (voltage-lift) graphs. Take a bipartite base multigraph
with k vertices on each side, each of degree 6 (a sum of 6 random permutation matrices, kept only
if connected). Assign a voltage in a group G to each dart. The lift has 2kG vertices and degree 6.
Right multiplication by any h in G is an automorphism, so the diameter is at most 5 iff a BFS of
depth 5 from (e, u) reaches every vertex, for each of the 2k base vertices u. Voltages are annealed
to make that cost zero. Haar graphs are the k = 1 special case, and k >= 2 gives more freedom.

Targets: k = 3 with |G| >= 115 (n >= 690), k = 2 with |G| >= 172 (n >= 688), k = 4 with |G| >= 86 (n >= 688).
Every returned graph is checked with lib.is_valid. The larger of the two stages' valid graphs wins,
and the trivial always-valid graph is the last resort.
"""
import itertools
import math
import time

import numpy as np

import lib


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
    """Table of a group given as an (N, c) integer coordinate array (element 0 must be the identity)
    and a vectorised product mulfun(X, Y) of two (..., c) arrays."""
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
    """Heisenberg group mod p (upper unitriangular 3x3), order p^3: (a,b,c)(a',b',c') = (a+a', b+b', c+c'+a*b')."""
    e = np.array(list(itertools.product(range(p), repeat=3)), dtype=np.int64)   # (0,0,0) is first

    def mul(X, Y):
        return np.stack([(X[..., 0] + Y[..., 0]) % p, (X[..., 1] + Y[..., 1]) % p,
                         (X[..., 2] + Y[..., 2] + X[..., 0] * Y[..., 1]) % p], axis=-1)
    return _table_from_coords(e, mul)


def group_agl(q, k=None):
    """GF(q) x| C_k: the maps t -> a*t + b on GF(q) with a in the subgroup of order k of GF(q)^* (default k = q-1,
    that is AGL(1, q)).  q a prime power (uses lib.GF).  The product is (b1, a1)(b2, a2) = (b1 + a1*b2, a1*a2)."""
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


# ------------------------------------------------------------------------------ stage A: Haar search

def _cover(MT, N, P):
    """Boolean array of the elements covered by the products P[i]*P[j] (P an int array of pair products)."""
    cov = np.zeros(N, dtype=bool)
    cov[MT[P[:, None], P[None, :]].ravel()] = True
    return cov


def _pairs(MT, inv, S):
    """(side-0 pair products S_i^-1 S_j, side-1 pair products S_i S_j^-1) as flat arrays."""
    Si = inv[S]
    return MT[Si[:, None], S[None, :]].ravel(), MT[S[:, None], Si[None, :]].ravel()


def cost(MT, inv, S):
    """Uncovered elements, both sides (cost 0 = valid diameter-5 Haar graph)."""
    N = MT.shape[0]
    return sum(N - int(_cover(MT, N, np.unique(P)).sum()) for P in _pairs(MT, inv, S))


def batch_costs(MT, inv, S, i, X):
    """cost of S with slot i replaced by x, for every x in the int array X (only slot-i words are recomputed)."""
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
    """Local search over d-subsets of the group, with restarts when stuck.
    Returns (best S, best cost)."""
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
    """Edges of the Haar graph: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def checked(MT, S, d, D):
    """The Haar graph for S, or None if it is not exactly valid (checked with lib.is_valid)."""
    n, edges = haar_edges(MT, S)
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


def trivial(d, D):
    """Always-valid small graph for any other (d, D) the evaluator may ask for."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


def run_until(d, D, rng, deadline, plan, fallback):
    """Haar stage with an absolute deadline. plan: list of (name, builder, S0, weight);
    fallback: (builder, S) of a valid smaller graph."""
    total_w = sum(w for *_, w in plan)
    for name, builder, S0, w in plan:
        now = time.monotonic()
        if now >= deadline:
            break
        end = now + (deadline - now) * w / total_w
        total_w -= w
        try:
            MT, inv = builder()
            S, c = search(MT, inv, d, S0, end, rng)
        except Exception:
            continue
        if S is not None and c == 0:
            g = checked(MT, S, d, D)
            if g is not None:
                return g
    try:
        MT, inv = fallback[0]()
        g = checked(MT, fallback[1], d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)


# ------------------------------------------------------------ stage B: multi-orbit voltage lifts

def _base_connected(c, k):
    """True if the bipartite base multigraph with k+k vertices (c[u][j] darts from A_u to B_j) is connected."""
    seen = [False] * (2 * k)
    seen[0] = True
    stack = [0]
    while stack:
        x = stack.pop()
        if x < k:
            nbrs = [k + j for j in range(k) if c[x][j] > 0]
        else:
            nbrs = [u for u in range(k) if c[u][x - k] > 0]
        for y in nbrs:
            if not seen[y]:
                seen[y] = True
                stack.append(y)
    return all(seen)


def random_base(k, rng):
    """Random k x k nonnegative integer matrix with all row and column sums 6, connected; or None."""
    for _ in range(50):
        c = np.zeros((k, k), dtype=np.int64)
        for _ in range(6):
            c[np.arange(k), rng.permutation(k)] += 1
        cl = c.tolist()
        if _base_connected(cl, k):
            return cl
    return None


def pair_list_of(k, cmat):
    """One (u, v) entry per dart: u in 0..k-1 (A side), v in k..2k-1 (B side)."""
    pairs = []
    for u in range(k):
        for j in range(k):
            pairs += [(u, k + j)] * int(cmat[u][j])
    return pairs


def build_lift(MT, inv, k, darts):
    """Neighbour table (2kG, 6) of the lift. Vertex b*G + x is base vertex b at group element x.
    Dart (u, v, g) joins (x, u) to (x*g, v); right multiplication by a group element is an automorphism."""
    G = MT.shape[0]
    x = np.arange(G)
    nbr = np.empty((2 * k * G, 6), dtype=np.int64)
    ca = [0] * k
    cb = [0] * (2 * k)
    for u, v, g in darts:
        c = ca[u]
        ca[u] += 1
        nbr[u * G:(u + 1) * G, c] = v * G + MT[x, g]
    for u, v, g in darts:
        c = cb[v]
        cb[v] += 1
        nbr[v * G:(v + 1) * G, c] = u * G + MT[x, inv[g]]
    return nbr


def lift_cost(nbr, n, srcs, D=5):
    """Number of (source, vertex) pairs at distance > D, summed over the sources (cost 0 = diameter <= D)."""
    total = 0
    for s in srcs:
        seen = np.zeros(n, dtype=bool)
        seen[s] = True
        front = np.array([s], dtype=np.int64)
        for _ in range(D):
            nxt = nbr[front].ravel()
            nxt = np.unique(nxt[~seen[nxt]])
            if nxt.size == 0:
                break
            seen[nxt] = True
            front = nxt
        total += n - int(seen.sum())
    return total


def anneal_lift(MT, inv, k, pairs, deadline, rng, K=4, T=0.8, patience=1500):
    """Anneal the voltages of the darts so that the lift has diameter <= 5. Returns (volt, best cost)."""
    G = MT.shape[0]
    n = 2 * k * G
    nD = len(pairs)
    groups = {}
    for i, p in enumerate(pairs):
        groups.setdefault(p, []).append(i)
    srcs = [b * G for b in range(2 * k)]

    def evaluate(volt):
        darts = [(u, v, int(volt[i])) for i, (u, v) in enumerate(pairs)]
        nbr = build_lift(MT, inv, k, darts)
        return lift_cost(nbr, n, srcs)

    def fresh():
        volt = np.zeros(nD, dtype=np.int64)
        for idxs in groups.values():
            volt[idxs] = rng.choice(G, len(idxs), replace=False)
        return volt

    volt = fresh()
    cur = evaluate(volt)
    bestc, bestv = cur, volt.copy()
    since = 0
    while time.monotonic() < deadline:
        if cur == 0:
            return volt, 0
        i = int(rng.integers(nD))
        p = pairs[i]
        others = {int(volt[j]) for j in groups[p] if j != i}
        cand = []
        for _ in range(K):
            g = int(rng.integers(G))
            if g not in others and g not in cand:
                cand.append(g)
        if not cand:
            continue
        best_c, best_g = None, None
        for g in cand:
            v2 = volt.copy()
            v2[i] = g
            c = evaluate(v2)
            if best_c is None or c < best_c:
                best_c, best_g = c, g
        delta = best_c - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            volt[i] = best_g
            cur = best_c
        if cur < bestc:
            bestc, bestv, since = cur, volt.copy(), 0
        else:
            since += 1
        if since > patience:
            volt = fresh()
            cur = evaluate(volt)
            since = 0
    return bestv, bestc


def lift_graph(MT, inv, k, pairs, volt):
    """Edges of the lift: A vertices are 0..kG-1, B vertices are kG..2kG-1."""
    G = MT.shape[0]
    darts = [(u, v, int(volt[i])) for i, (u, v) in enumerate(pairs)]
    nbr = build_lift(MT, inv, k, darts)
    n = 2 * k * G
    A = np.repeat(np.arange(k * G, dtype=np.int64), 6)
    B = nbr[:k * G].ravel()
    return n, list(zip(A.tolist(), B.tolist()))


# Bold pool: (k, m, k2, lam) meaning base size k, group Z_m x| Z_k2. Orders chosen so that 2kG > 684.
BOLD_SPECS = [(3, 115, 126, 4), (2, 172, 180, 3), (4, 86, 92, 2)]
BOLD_POOL = []
for _k, _lo, _hi, _lim in BOLD_SPECS:
    for _name, _N, _m, _kk, _lam in metacyclic_candidates(_lo, _hi, _lim):
        BOLD_POOL.append((_k, _m, _kk, _lam))


def bold_stage(d, D, rng, deadline, best):
    """Multi-orbit voltage-lift search. best: (n, edges) or None. Returns the best valid (n, edges) found."""
    pool = BOLD_POOL
    for idx, (k, m, kk, lam) in enumerate(pool):
        now = time.monotonic()
        if now >= deadline:
            break
        slot_end = now + (deadline - now) / (len(pool) - idx)
        try:
            MT, inv = group_meta(m, kk, lam)
        except Exception:
            continue
        G = MT.shape[0]
        if best is not None and 2 * k * G <= best[0]:
            continue
        seg = slot_end - now
        while time.monotonic() < slot_end:
            cmat = random_base(k, rng)
            if cmat is None:
                continue
            chunk_end = min(slot_end, time.monotonic() + max(1.0, seg / 3))
            pairs = pair_list_of(k, cmat)
            try:
                volt, c = anneal_lift(MT, inv, k, pairs, chunk_end, rng)
            except Exception:
                break
            if c == 0:
                try:
                    n, edges = lift_graph(MT, inv, k, pairs, volt)
                except Exception:
                    break
                if lib.is_valid(n, edges, d, D) and (best is None or n > best[0]):
                    best = (n, edges)
                break
    return best


# ======================================================================================== cell: d6D5
TARGET = (6, 5)      # the (d, D) this plan is for; every other case gets a small always-valid graph

# Fixed non-abelian Haar families just above the threshold 342.
PLAN = [
    ('Heis(3) x Z_13, order 351', lambda: group_times_cyclic(group_heis(3), 13), None, 1),
    ('Heis(7), order 343', lambda: group_heis(7), None, 1),
    ('AGL(1,9) x Z_5, order 360', lambda: group_times_cyclic(group_agl(9), 5), None, 1),
    ('AGL(1,5) x Z_18, order 360', lambda: group_times_cyclic(group_agl(5), 18), None, 1),
]

# Metacyclic groups of every order from 342 to 372 (one per (m, k)), each given an equal slice of time.
for _name, _N, _m, _k, _lam in metacyclic_candidates(342, 372, 10):
    PLAN.append((_name, (lambda m=_m, k=_k, lam=_lam: group_meta(m, k, lam)), None, 1))

# Valid smaller Haar graph; used only when no plan entry reaches cost 0.
FALLBACK = (lambda: group_meta(33, 10, 26), [0, 179, 116, 180, 47, 306])


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    budget = 0.75 * time_limit
    rng = np.random.default_rng(seed)

    # Stage A: Haar search (the parent's method), limited to the first 40% of the budget.
    haar = None
    try:
        haar = run_until(d, D, rng, t0 + 0.40 * budget, PLAN, FALLBACK)
    except Exception:
        haar = None

    # Stage B: multi-orbit voltage lifts, aiming for more than 684 vertices.
    best = None
    try:
        best = bold_stage(d, D, rng, t0 + budget, None)
    except Exception:
        best = None

    cands = [g for g in (haar, best) if g is not None]
    if not cands:
        return trivial(d, D)
    return max(cands, key=lambda g: g[0])
