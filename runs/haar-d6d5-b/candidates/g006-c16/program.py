"""Haar and lift search for the bipartite degree-diameter problem at diameter 5 (numpy only).

THEORY.  A Haar graph over a finite group G with connection set S (|S| = d) has vertices (g, A), (g, B) and
edges (g, A) ~ (s*g, B).  It has diameter <= 5 iff (S^-1 S)^2 = G and (S S^-1)^2 = G, so the search for a valid
S is a covering problem over the group.

NEW CONSTRUCTION (tried first for the target).  A 2-orbit-per-side lift.  Base vertices A0, A1, B0, B1 each have
3 darts to each vertex on the other side, so every base vertex has degree 6.  A dart (u, v, s) joins (u, x) to
(v, x*s) for all x in G.  Each dart pair (u, v) uses three distinct voltages, so the lift has 4|G| vertices, is
bipartite and 6-regular, and has no duplicate edges.  Left multiplication by any h in G is an automorphism, so
the graph's diameter is at most 5 iff a radius-5 BFS from each of the 4 orbit representatives reaches every
vertex.  The cost is the total number of unreached vertices over those 4 BFS runs.  Cost 0 means valid.
Four orbits of order >= 172 give order >= 688 > 684.  Voltages are found by annealing with random restarts over
metacyclic groups Z_m x| Z_k of order 172..190.

FALLBACK.  If the lift search fails, the original Haar search runs on the remaining budget, using the parent's
plan and its checked smaller graph (order 660).  Every returned graph passes lib.is_valid.
"""
import math
import time

import numpy as np

import lib


TARGET = (6, 5)
PAIRS = ((0, 2), (0, 3), (1, 2), (1, 3))   # (A-base, B-base) index pairs of the lift


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


def _is_prime(n):
    if n < 2:
        return False
    i = 2
    while i * i <= n:
        if n % i == 0:
            return False
        i += 1
    return True


def meta_candidates(lo, hi, kmin=3, kmax=7):
    """Metacyclic parameters (m, k, lam) with m prime, k | m-1, lo <= m*k <= hi, lam of order k mod m."""
    out = []
    for k in range(kmin, kmax + 1):
        for m in range(3, hi // k + 1):
            if m * k < lo or not _is_prime(m) or (m - 1) % k:
                continue
            lam = next((r for r in range(2, m) if pow(r, k, m) == 1), None)
            if lam is None:
                continue
            out.append((m, k, lam))
    out.sort(key=lambda t: (t[0] * t[1], t[1]))
    return out


def lift_candidates(lo, hi, kmax=12):
    """Metacyclic Z_m x| Z_k groups of order N = m*k in [lo, hi] (any m, k <= kmax), one lam per (m, k).
    Sorted by order, so the smallest order that beats the record comes first."""
    out = []
    for N in range(lo, hi + 1):
        for k in range(2, kmax + 1):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            for lam in range(2, m):
                if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1 % m:
                    out.append((m, k, lam))
                    break
    return out


# ------------------------------------------------------------------------------- 4-orbit lift search

def _lift_adj(MTl, N, volt):
    """Adjacency lists of the lift: orbit u*N + x (u in {0,1}) and v*N + y (v in {2,3})."""
    adj = [[] for _ in range(4 * N)]
    for p, (u, v) in enumerate(PAIRS):
        for s in volt[p]:
            s = int(s)
            for x in range(N):
                a = u * N + x
                b = v * N + MTl[x][s]
                adj[a].append(b)
                adj[b].append(a)
    return adj


def _lift_cost(adj, V, reps, D=5):
    """Total number of vertices not reached within D steps from the orbit representatives.  0 iff valid."""
    tot = 0
    for r in reps:
        seen = bytearray(V)
        seen[r] = 1
        frontier = [r]
        cnt = 1
        for _ in range(D):
            nxt = []
            for a in frontier:
                for b in adj[a]:
                    if not seen[b]:
                        seen[b] = 1
                        nxt.append(b)
            cnt += len(nxt)
            frontier = nxt
            if not frontier:
                break
        tot += V - cnt
    return tot


def lift_search(MTl, N, rng, deadline, patience=2500, T=0.6):
    """Anneal the 12 voltages (3 distinct per base pair) until the lift has diameter <= 5. Returns volt or None."""
    V = 4 * N
    reps = [0, N, 2 * N, 3 * N]

    def rnd():
        v = np.zeros((4, 3), dtype=np.int64)
        for p in range(4):
            v[p] = rng.choice(N, 3, replace=False)
        return v

    volt = rnd()
    cur = _lift_cost(_lift_adj(MTl, N, volt), V, reps)
    best, since = cur, 0
    while time.monotonic() < deadline:
        if cur == 0:
            return volt
        p = int(rng.integers(4))
        j = int(rng.integers(3))
        new = int(rng.integers(N))
        if new in volt[p]:
            continue
        old = int(volt[p, j])
        volt[p, j] = new
        c = _lift_cost(_lift_adj(MTl, N, volt), V, reps)
        if c <= cur or rng.random() < math.exp(-(c - cur) / T):
            cur = c
        else:
            volt[p, j] = old
        if cur < best:
            best, since = cur, 0
        else:
            since += 1
        if since > patience:
            volt = rnd()
            cur = _lift_cost(_lift_adj(MTl, N, volt), V, reps)
            best, since = cur, 0
    return volt if cur == 0 else None


def lift_graph(MTl, N, volt):
    """Edge list of the 4-orbit lift for the voltages volt (all pairs are A-to-B, so a < b)."""
    edges = set()
    for p, (u, v) in enumerate(PAIRS):
        for s in volt[p]:
            s = int(s)
            for x in range(N):
                edges.add((u * N + x, v * N + MTl[x][s]))
    return 4 * N, sorted(edges)


def lift_phase(rng, deadline, lo=172, hi=190, max_groups=8):
    """Try lift searches on the smallest groups that beat the record. Returns a checked (n, edges) or None."""
    cands = lift_candidates(lo, hi)[:max_groups]
    for idx, (m, k, lam) in enumerate(cands):
        now = time.monotonic()
        if now >= deadline:
            break
        end = now + (deadline - now) / (len(cands) - idx)
        try:
            MT, _ = group_meta(m, k, lam)
            N = m * k
            MTl = MT.tolist()
            volt = lift_search(MTl, N, rng, end)
            if volt is None:
                continue
            n, edges = lift_graph(MTl, N, volt)
            if lib.is_valid(n, edges, TARGET[0], TARGET[1]):
                return n, edges
        except Exception:
            continue
    return None


# ------------------------------------------------------------------------------- Haar search (fallback)

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


def one_swap_scan(MT, inv, S, deadline, chunk=512):
    """Score EVERY single-slot replacement of S.  Returns (best cost, best S)."""
    N = MT.shape[0]
    best, bestS = 10 ** 9, None
    for i in range(len(S)):
        rest = np.delete(S, i)
        for lo in range(0, N, chunk):
            if time.monotonic() >= deadline:
                return best, bestS
            X = np.arange(lo, min(N, lo + chunk), dtype=np.int32)
            X = X[~np.isin(X, rest)]
            cs = batch_costs(MT, inv, S, i, X)
            j = int(np.argmin(cs))
            if cs[j] < best:
                best, bestS = int(cs[j]), S.copy()
                bestS[i] = X[j]
    return best, bestS


def search(MT, inv, d, S0, deadline, rng, K=24, temp=0.45, patience=4000):
    """Local search over d-subsets of the group.  Returns (best S, best cost)."""
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
        c1, S1 = one_swap_scan(MT, inv, S0, time.monotonic() + 0.25 * (deadline - time.monotonic()))
        if S1 is not None and c1 < bestc:
            best, bestc, S = S1.copy(), c1, S1.copy()
            if c1 == 0:
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
    """The Haar graph for S, or None if it is not exactly valid."""
    n, edges = haar_edges(MT, S)
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


def run(d, D, seed, time_limit, plan, fallback):
    """plan: list of (name, builder, S0 or None, weight); fallback: (builder, S) of a valid smaller graph."""
    t0 = time.monotonic()
    deadline_all = t0 + 0.85 * time_limit
    rng = np.random.default_rng(seed)
    total_w = sum(w for *_, w in plan)
    for name, builder, S0, w in plan:
        now = time.monotonic()
        if now >= deadline_all:
            break
        end = now + (deadline_all - now) * w / total_w
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


def _target_plan():
    """Random-start Haar searches on metacyclic groups of order just above 342, then near-miss entries."""
    fresh = []
    for m, k, lam in meta_candidates(344, 372):
        fresh.append((f'meta {m}/{k}/{lam}, random start',
                      (lambda m=m, k=k, lam=lam: group_meta(m, k, lam)), None, 1))
        if len(fresh) == 4:
            break
    near = [
        ('meta 117/3/16, order 351, 2 short', lambda: group_meta(117, 3, 16), [0, 184, 47, 48, 65, 21], 2),
        ('meta 71/5/5, order 355, 2 short', lambda: group_meta(71, 5, 5), [0, 92, 218, 269, 205, 88], 2),
    ]
    return fresh + near


# Valid smaller Haar graph (order 330, 660 vertices), checked at run time.
FALLBACK = (lambda: group_meta(33, 10, 26), [0, 179, 116, 180, 47, 306])


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    rng = np.random.default_rng(seed)
    res = lift_phase(rng, t0 + 0.55 * time_limit)
    if res is not None:
        return res
    return run(d, D, seed, 0.3 * time_limit, _target_plan(), FALLBACK)
