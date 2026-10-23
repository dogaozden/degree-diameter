"""Bold variant for d=6, D=5: bipartite voltage lifts over non-abelian groups, searched first.

Construction: base multigraph with b vertices per side, each of degree 6 (built from 6 random permutations),
so the lift has 2*b*|G| vertices. Dart (i, j, g) joins (A,i,x) to (B,j,x*g). Left multiplication by h is an
automorphism, so every fibre is one orbit and the diameter is at most 5 iff each of the 2b base vertices
reaches everything within 5 steps. That gives a cheap cost (unreached vertices from the base vertices).
Annealing over voltages finds cost 0 for orders above the record. If that fails, the parent Haar search runs,
then a precomputed valid smaller Haar graph. Every returned graph is checked with lib.is_valid.
"""
import itertools
import math
import time

import numpy as np

import lib

TARGET = (6, 5)
VOLT_D = 6
TEMP = 1.0
PATIENCE = 1500


# ============================================================ group tables (shared with the parent)

def _finish(MT):
    """Return (MT, inverse array) for a table whose identity is element 0."""
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int32)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k with (a, j) -> index a*k + j and (a, j)(b, l) = (a + lam^j b, j + l). Needs lam^k = 1 mod m."""
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
    """GF(q) x| C_k (default AGL(1, q))."""
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
    """Direct product of a table group with Z_k."""
    MT0, _ = grp
    n0 = MT0.shape[0]
    c = np.arange(k, dtype=np.int64)
    MT = np.empty((n0 * k, n0 * k), dtype=np.int32)
    for g in range(n0):
        MT[g * k:(g + 1) * k] = (MT0[g][None, :, None] * k + (c[:, None, None] + c[None, None, :]) % k).reshape(k, n0 * k)
    return _finish(MT)


def metacyclic_candidates(lo, hi, limit):
    """Non-abelian metacyclic groups Z_m x|_lam Z_k with lo <= m*k <= hi, one per (m, k)."""
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


def nonabelian_meta(N, limit):
    """Up to `limit` triples (m, k, lam) giving non-abelian Z_m x|_lam Z_k of order N."""
    out = []
    for k in range(2, N):
        if N % k:
            continue
        m = N // k
        if m < 3:
            continue
        for lam in range(2, m):
            if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1 % m:
                out.append((m, k, lam))
                break
        if len(out) >= limit:
            break
    return out


# ============================================================ voltage lifts (new construction)

def random_base(b, rng):
    """Base bipartite multigraph on b+b vertices, every vertex of degree VOLT_D, connected.
    Darts are returned sorted by A-vertex (VOLT_D per A-vertex), with their B-endpoint J."""
    while True:
        perms = [rng.permutation(b) for _ in range(VOLT_D)]
        I = np.repeat(np.arange(b), VOLT_D).astype(np.int64)
        J = np.array([perms[t][i] for i in range(b) for t in range(VOLT_D)], dtype=np.int64)
        parent = list(range(2 * b))

        def find(x):
            while parent[x] != x:
                parent[x] = parent[parent[x]]
                x = parent[x]
            return x
        for i, j in zip(I.tolist(), J.tolist()):
            parent[find(i)] = find(b + j)
        if len({find(x) for x in range(2 * b)}) == 1:
            return I, J


def lift_nbr(b, N, MT, invs, I, J, G):
    """Neighbour array (2*b*N, VOLT_D). A-vertex (i,x) has index i*N+x; B-vertex (j,y) has index b*N+j*N+y."""
    ar = np.arange(N)
    Bidx = b * N + J[:, None] * N + MT[ar[None, :], G[:, None]]          # B-neighbour of A-fibre x along dart t
    Aidx = I[:, None] * N + MT[ar[None, :], invs[G][:, None]]            # A-neighbour of B-fibre y along dart t
    order = np.argsort(J, kind="stable")
    nA = Bidx.reshape(b, VOLT_D, N).transpose(0, 2, 1).reshape(b * N, VOLT_D)
    nB = Aidx[order].reshape(b, VOLT_D, N).transpose(0, 2, 1).reshape(b * N, VOLT_D)
    return np.vstack([nA, nB])


def lift_cost(nbr, b, N):
    """Number of (base vertex, vertex) pairs at distance > 5, over the 2b base vertices (0 = valid).
    Left translations are automorphisms, so checking the base vertices suffices."""
    V = 2 * b * N
    total = 0
    for v in range(2 * b):
        s = v * N
        reached = np.zeros(V, dtype=bool)
        reached[s] = True
        frontier = np.array([s], dtype=np.int64)
        for _ in range(5):
            nxt = nbr[frontier].ravel()
            nxt = nxt[~reached[nxt]]
            if nxt.size == 0:
                break
            nxt = np.unique(nxt)
            reached[nxt] = True
            frontier = nxt
        total += V - int(reached.sum())
    return total


def anneal_lift(b, N, MT, invs, I, J, rng, deadline):
    """Anneal voltages for a fixed base. Darts sharing an (A, B) pair get distinct voltages (keeps the lift simple)."""
    D = len(I)
    same = [[u for u in range(D) if u != t and I[u] == I[t] and J[u] == J[t]] for t in range(D)]

    def fresh():
        G = np.zeros(D, dtype=np.int64)
        for t in range(D):
            while True:
                g = int(rng.integers(N))
                if all(G[u] != g for u in same[t] if u < t):
                    G[t] = g
                    break
        return G

    G = fresh()
    cur = lift_cost(lift_nbr(b, N, MT, invs, I, J, G), b, N)
    since = 0
    while time.monotonic() < deadline:
        if cur == 0:
            return G
        t = int(rng.integers(D))
        g = int(rng.integers(N))
        if g == G[t] or any(G[u] == g for u in same[t]):
            continue
        old = G[t]
        G[t] = g
        c = lift_cost(lift_nbr(b, N, MT, invs, I, J, G), b, N)
        delta = c - cur
        if delta <= 0 or rng.random() < math.exp(-delta / TEMP):
            cur = c
            since = 0 if delta < 0 else since + 1
        else:
            G[t] = old
            since += 1
        if since > PATIENCE:
            G = fresh()
            cur = lift_cost(lift_nbr(b, N, MT, invs, I, J, G), b, N)
            since = 0
    return None


def lift_edges(b, N, MT, I, J, G):
    """Edge list of the lift: (A,i,x) ~ (B,j,MT[x,g]) for each dart (i,j,g)."""
    edges = []
    for t in range(len(I)):
        i, j, g = int(I[t]), int(J[t]), int(G[t])
        for x in range(N):
            edges.append((i * N + x, b * N + j * N + int(MT[x, g])))
    return 2 * b * N, edges


# (b, N): base vertices per side and group order; 2*b*N > 684 so any success beats the record.
VOLT_CONFIGS = [(2, 172), (2, 174), (2, 176), (2, 178), (3, 116), (4, 86), (5, 70), (6, 58)]


def volt_stage(deadline, rng, configs):
    remaining = len(configs)
    for b, N in configs:
        now = time.monotonic()
        if now >= deadline:
            break
        end = now + (deadline - now) / remaining
        remaining -= 1
        groups = nonabelian_meta(N, 1)
        if not groups:
            continue
        m, k, lam = groups[0]
        try:
            MT, invs = group_meta(m, k, lam)
        except Exception:
            continue
        while time.monotonic() < end:
            try:
                I, J = random_base(b, rng)
                per = min(end, time.monotonic() + 2.0)
                G = anneal_lift(b, N, MT, invs, I, J, rng, per)
                if G is not None:
                    n, edges = lift_edges(b, N, MT, I, J, G)
                    if lib.is_valid(n, edges, 6, 5):
                        return n, edges
            except Exception:
                continue
    return None


# ============================================================ Haar search (parent, kept as second stage)

def _cover(MT, N, P):
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
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


PLAN = [
    ('Heis(3) x Z_13, order 351', lambda: group_times_cyclic(group_heis(3), 13), None, 1),
    ('Heis(7), order 343', lambda: group_heis(7), None, 1),
    ('AGL(1,9) x Z_5, order 360', lambda: group_times_cyclic(group_agl(9), 5), None, 1),
    ('AGL(1,5) x Z_18, order 360', lambda: group_times_cyclic(group_agl(5), 18), None, 1),
]
for _name, _N, _m, _k, _lam in metacyclic_candidates(342, 372, 10):
    PLAN.append((_name, (lambda m=_m, k=_k, lam=_lam: group_meta(m, k, lam)), None, 1))

FALLBACK = (lambda: group_meta(33, 10, 26), [0, 179, 116, 180, 47, 306])


def haar_stage(d, D, rng, deadline, plan):
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
    return None


# ============================================================ entry point

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    budget = 0.85 * time_limit
    rng = np.random.default_rng(seed)
    try:
        g = volt_stage(t0 + 0.55 * budget, rng, VOLT_CONFIGS)
        if g is not None:
            return g
    except Exception:
        pass
    try:
        g = haar_stage(d, D, rng, t0 + budget, PLAN)
        if g is not None:
            return g
    except Exception:
        pass
    try:
        MT, inv = FALLBACK[0]()
        g = checked(MT, FALLBACK[1], d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)
