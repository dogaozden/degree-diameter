"""Mixed search for the bipartite degree-diameter problem, diameter 5, degree 6 (numpy only).

Two constructions share one time budget:

1. Lifts of small bipartite base multigraphs (a A-vertices, a B-vertices, 6-regular base) over a finite
   group G. The lift has 2*a*|G| vertices. Left multiplication by G is an automorphism, so the diameter is
   at most 5 iff every base vertex reaches all vertices within distance 5. Cost = unreached counts from
   the 2a base representatives, plus a penalty for duplicate darts. Annealing runs on the voltages.
2. Haar graphs (the previous approach): cost(S) = uncovered elements of (S^-1 S)^2 and (S S^-1)^2.

Every returned graph is checked with lib.is_valid. The largest valid graph wins. If nothing valid is
found, the previous fallback Haar graph is used, and then a trivial graph.
"""
import itertools
import math
import time

import numpy as np

import lib

TARGET = (6, 5)
DEG = 6
DIAM = 5


# ----------------------------------------------------------------------------------- group tables

def _finish(MT):
    """Return (MT, inverse array) for a table whose identity is element 0."""
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int32)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k with (a, j) -> a*k + j and (a, j)(b, l) = (a + lam^j b, j + l)."""
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
    """Table of a group given by an (N, c) coordinate array (element 0 = identity) and a vectorised product."""
    N, c = elems.shape
    base = int(elems.max()) + 1
    wts = base ** np.arange(c, dtype=np.int64)
    codes = elems.astype(np.int64) @ wts
    order = np.argsort(codes)
    sc = codes[order]
    MT = np.empty((N, N), dtype=np.int32)
    for i in range(N):
        prod = mulfun(elems[i][None, :], elems)
        MT[i] = order[np.searchsorted(sc, prod.astype(np.int64) @ wts)]
    return _finish(MT)


def group_heis(p):
    """Heisenberg group mod p, order p^3, identity (0,0,0) first."""
    e = np.array(list(itertools.product(range(p), repeat=3)), dtype=np.int64)

    def mul(X, Y):
        return np.stack([(X[..., 0] + Y[..., 0]) % p, (X[..., 1] + Y[..., 1]) % p,
                         (X[..., 2] + Y[..., 2] + X[..., 0] * Y[..., 1]) % p], axis=-1)
    return _table_from_coords(e, mul)


def group_times_cyclic(grp, k):
    """Direct product of a table group with Z_k; element (g, c) has index g*k + c."""
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


# ------------------------------------------------------------------------ Haar-graph search (old)

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
    """Local search over d-subsets of the group. Returns (best S, best cost)."""
    N = MT.shape[0]
    best, bestc = None, 10 ** 9
    S, cur = None, None

    def random_set():
        return np.concatenate([[0], rng.choice(np.arange(1, N), d - 1, replace=False)]).astype(np.int32)

    while time.monotonic() < deadline:
        if S is None:
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


# ------------------------------------------------------------- voltage lifts of small base graphs

def _lift_nb(MT, inv, P, V, a):
    """Neighbour array (2*a*N, DEG). A-vertex (i, x) = i*N + x; B-vertex (j, y) = (a+j)*N + y.
    Dart k joins A_i to B_{P[k,i]} with voltage V[k,i]: (i, x) ~ (P[k,i], x*g)."""
    N = MT.shape[0]
    X = np.arange(N)
    Q = np.argsort(P, axis=1)
    nb = np.empty((2 * a * N, DEG), dtype=np.int64)
    for k in range(DEG):
        for i in range(a):
            nb[i * N:(i + 1) * N, k] = (a + P[k, i]) * N + MT[X, V[k, i]]
        for j in range(a):
            i = Q[k, j]
            nb[(a + j) * N:(a + j + 1) * N, k] = i * N + MT[X, inv[V[k, i]]]
    return nb


def _bad_from(nb, src, nv):
    """Number of vertices not within DIAM of src."""
    seen = np.zeros(nv, dtype=bool)
    seen[src] = True
    front = np.array([src], dtype=np.int64)
    for _ in range(DIAM):
        nxt = nb[front].ravel()
        nxt = np.unique(nxt[~seen[nxt]])
        if nxt.size == 0:
            break
        seen[nxt] = True
        front = nxt
    return nv - int(seen.sum())


def _dups(P, V, a):
    """Count pairs of darts from the same A-vertex that would give the same edge."""
    c = 0
    for i in range(a):
        for k1 in range(DEG):
            for k2 in range(k1 + 1, DEG):
                if P[k1, i] == P[k2, i] and V[k1, i] == V[k2, i]:
                    c += 1
    return c


def _lift_cost(nb, a, N, P, V):
    nv = nb.shape[0]
    c = sum(_bad_from(nb, s * N, nv) for s in range(2 * a))
    return c + 50 * _dups(P, V, a)


def lift_search(MT, inv, a, deadline, rng, patience=2500, temp=2.0):
    """Anneal the voltages of a random 6-regular bipartite base on a copies of A and a of B.
    Returns (cost, P, V) of the best state found."""
    N = MT.shape[0]
    best = None
    best_c = 10 ** 9
    while time.monotonic() < deadline:
        P = np.array([rng.permutation(a) for _ in range(DEG)], dtype=np.int64)
        V = rng.integers(0, N, size=(DEG, a)).astype(np.int64)
        cur = _lift_cost(_lift_nb(MT, inv, P, V, a), a, N, P, V)
        if cur < best_c:
            best_c, best = cur, (P.copy(), V.copy())
        if cur == 0:
            return best_c, best[0], best[1]
        since = 0
        while since < patience and time.monotonic() < deadline:
            k = int(rng.integers(DEG))
            i = int(rng.integers(a))
            old = V[k, i]
            V[k, i] = rng.integers(N)
            c = _lift_cost(_lift_nb(MT, inv, P, V, a), a, N, P, V)
            delta = c - cur
            if delta <= 0 or rng.random() < math.exp(-delta / temp):
                cur = c
                if c < best_c:
                    best_c, best = c, (P.copy(), V.copy())
                    if c == 0:
                        return best_c, best[0], best[1]
                since = 0 if delta < 0 else since + 1
            else:
                V[k, i] = old
                since += 1
    if best is None:
        return None
    return best_c, best[0], best[1]


def lift_graph(MT, inv, a, P, V):
    N = MT.shape[0]
    nb = _lift_nb(MT, inv, P, V, a)
    edges = [(u, int(v)) for u in range(a * N) for v in nb[u]]
    return 2 * a * N, edges


# ----------------------------------------------------------------------------------------- plans

def trivial(d, D):
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


def _lift_plan():
    plan = [("lift a=3 Heis(5)", 3, lambda: group_heis(5))]
    for _name, _N, m, k, lam in metacyclic_candidates(115, 124, 4):
        plan.append((_name, 3, (lambda m=m, k=k, lam=lam: group_meta(m, k, lam))))
    for _name, _N, m, k, lam in metacyclic_candidates(172, 180, 3):
        plan.append((_name, 2, (lambda m=m, k=k, lam=lam: group_meta(m, k, lam))))
    return plan


def _haar_plan():
    plan = [("Haar Heis(7)", lambda: group_heis(7)),
            ("Haar Heis(3) x Z13", lambda: group_times_cyclic(group_heis(3), 13))]
    for _name, _N, m, k, lam in metacyclic_candidates(342, 342, 1):
        plan.append((_name, (lambda m=m, k=k, lam=lam: group_meta(m, k, lam))))
    return plan


FALLBACK = (lambda: group_meta(33, 10, 26), [0, 179, 116, 180, 47, 306])


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    deadline_all = t0 + 0.80 * time_limit
    rng = np.random.default_rng(seed)

    entries = [("lift", a, b) for _name, a, b in _lift_plan()]
    entries += [("haar", None, b) for _name, b in _haar_plan()]
    total_w = float(len(entries))
    best = None

    for kind, a, builder in entries:
        now = time.monotonic()
        if now >= deadline_all:
            break
        end = now + (deadline_all - now) / total_w
        total_w -= 1.0
        try:
            MT, inv = builder()
            if kind == "lift":
                res = lift_search(MT, inv, a, end, rng)
                if res is not None and res[0] == 0:
                    n, edges = lift_graph(MT, inv, a, res[1], res[2])
                    if lib.is_valid(n, edges, d, D) and (best is None or n > best[0]):
                        best = (n, edges)
            else:
                S, c = search(MT, inv, d, None, end, rng)
                if S is not None and c == 0:
                    g = checked(MT, S, d, D)
                    if g is not None and (best is None or g[0] > best[0]):
                        best = g
        except Exception:
            continue

    if best is None:
        try:
            MT, inv = FALLBACK[0]()
            g = checked(MT, FALLBACK[1], d, D)
            if g is not None:
                best = g
        except Exception:
            pass
    return best if best is not None else trivial(d, D)
