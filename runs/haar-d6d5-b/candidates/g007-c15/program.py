"""Bold variant: 4-vertex Z_m x| Z_k voltage lifts (new construction) tried first, then the Haar-graph search.

NEW CONSTRUCTION.  The parent used Haar graphs, which are lifts of a 2-vertex base with d parallel darts. Here the base
has 2 A-vertices and 2 B-vertices with 12 darts (6 per A-vertex, 3 to each B-vertex), so each A and B vertex has degree 6.
A dart (a, b, g) joins (a, x) to (b, x*g) for every x in G, giving 4|G| vertices. A 4-vertex lift on a group of order
N >= 172 gives at least 688 vertices, which beats 684. Left multiplication by G is an automorphism, so the
diameter check only needs BFS from the four class representatives. The annealer minimises the number of unordered
pairs at distance > 5 and returns only graphs that pass lib.is_valid.

SAFETY.  If the lift stage finds nothing, the parent's Haar-graph plan runs with its own fallback. Every return path is
a graph that passed lib.is_valid, or the small trivial graph.
"""
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


# ------------------------------------------------------------------------------------ Haar-graph search

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
    """Score every single-slot replacement of S.  Returns (best cost, best S)."""
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


def meta_candidates(lo, hi, exclude, limit):
    """Metacyclic Z_m x|_lam Z_k (non-abelian) with order N in (lo, hi], largest orders first."""
    out = []
    for N in range(hi, lo, -1):
        for k in range(2, N):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            for lam in range(2, m):
                if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1 and (m, k, lam) not in exclude:
                    out.append((m, k, lam))
                    if len(out) >= limit:
                        return out
    return out


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


# ============================================================================ 4-vertex lift tier (new)

LIFT_LO = 172   # 4 * 172 = 688 > 684 (record)


def _valid_dart(darts, a, b, g, skip):
    """True if (a, b, g) is not already a dart from a, ignoring the darts whose index is in skip."""
    for i, (a2, b2, g2) in enumerate(darts):
        if i not in skip and a2 == a and b2 == b and g2 == g:
            return False
    return True


def _lift_bad(MT, N, darts, D):
    """Unordered pairs at distance > D in the 4-vertex lift.  By left-multiplication symmetry, only four
    representatives (A0, A1, B0, B1 at group identity) need a BFS; each class has N vertices."""
    n = 4 * N
    adj = [[] for _ in range(n)]
    for a, b, g in darts:
        col = MT[:, g].tolist()
        for x in range(N):
            u = a * N + x
            v = 2 * N + b * N + col[x]
            adj[u].append(v)
            adj[v].append(u)
    total = 0
    for rep in (0, N, 2 * N, 3 * N):
        seen = {rep}
        frontier = [rep]
        for _ in range(D):
            nxt = []
            for u in frontier:
                for w in adj[u]:
                    if w not in seen:
                        seen.add(w)
                        nxt.append(w)
            if not nxt:
                break
            frontier = nxt
        total += n - len(seen)
    return total * N // 2


def _lift_edges(MT, N, darts):
    """Edges of the lift: A-vertex (a, x) = a*N + x, B-vertex (b, y) = 2N + b*N + y, dart (a, b, g) gives (a,x)~(b,x*g)."""
    edges = set()
    for a, b, g in darts:
        col = MT[:, g].tolist()
        for x in range(N):
            edges.add((a * N + x, 2 * N + b * N + col[x]))
    return 4 * N, sorted(edges)


def _lift_anneal(MT, N, D, deadline, rng, T=3.0, stale_limit=1500):
    """Anneal 12 darts (per A-vertex: 3 to B0, 3 to B1) to make the lift have diameter <= D."""
    darts = []
    for a in (0, 1):
        for b in (0, 0, 0, 1, 1, 1):
            while True:
                g = int(rng.integers(N))
                if _valid_dart(darts, a, b, g, ()):
                    break
            darts.append((a, b, g))
    cur = _lift_bad(MT, N, darts, D)
    best, bestc = list(darts), cur
    stale = 0
    while cur > 0 and time.monotonic() < deadline:
        i = int(rng.integers(len(darts)))
        a, b, g = darts[i]
        new = list(darts)
        if rng.random() < 0.5:
            g2 = int(rng.integers(N))
            if not _valid_dart(darts, a, b, g2, (i,)):
                continue
            new[i] = (a, b, g2)
        else:
            js = [j for j in range(len(darts)) if j != i and darts[j][0] == a and darts[j][1] != b]
            if not js:
                continue
            j = js[int(rng.integers(len(js)))]
            _, b2, g2 = darts[j]
            if not (_valid_dart(darts, a, b2, g, (i, j)) and _valid_dart(darts, a, b, g2, (i, j))):
                continue
            new[i] = (a, b2, g)
            new[j] = (a, b, g2)
        c = _lift_bad(MT, N, new, D)
        delta = c - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            darts, cur = new, c
            if cur < bestc:
                best, bestc, stale = list(darts), cur, 0
            else:
                stale += 1
        else:
            stale += 1
        if stale > stale_limit:
            break
    return best, bestc


def _lift_groups(lo, hi):
    """Metacyclic Z_m x|_lam Z_k (lam != 1) with order N in [lo, hi], smallest orders first."""
    out = []
    for N in range(lo, hi + 1):
        for k in range(2, N):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            for lam in range(2, m):
                if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1:
                    out.append((m, k, lam))
    return out


def _lift_stage(d, D, rng, deadline):
    """Try 4-vertex lifts over metacyclic groups of order >= LIFT_LO.  Returns a checked graph or None."""
    groups = _lift_groups(LIFT_LO, LIFT_LO + 28)
    if not groups:
        return None
    gi = 0
    while time.monotonic() < deadline:
        m, k, lam = groups[gi % len(groups)]
        gi += 1
        N = m * k
        try:
            MT, _ = group_meta(m, k, lam)
        except Exception:
            continue
        dl = min(deadline, time.monotonic() + 2.5)
        darts, c = _lift_anneal(MT, N, D, dl, rng)
        if c == 0:
            n, edges = _lift_edges(MT, N, darts)
            if lib.is_valid(n, edges, d, D):
                return n, edges
    return None


# ======================================================================================== target plan

TARGET = (6, 5)

PLAN = [
    ('meta 117/3/16, order 351, 2 short', lambda: group_meta(117, 3, 16), [0, 184, 47, 48, 65, 21], 4),
    ('meta 71/5/5, order 355, 2 short', lambda: group_meta(71, 5, 5), [0, 92, 218, 269, 205, 88], 4),
]


def _extra_plan():
    """Random-start tier: metacyclic groups of order 331..342 not already used above."""
    used = {(117, 3, 16), (71, 5, 5)}
    entries = []
    for m, k, lam in meta_candidates(330, 342, used, 6):
        entries.append((f'meta {m}/{k}/{lam} random', (lambda m=m, k=k, lam=lam: group_meta(m, k, lam)), None, 2))
    return entries


FALLBACK = (lambda: group_meta(33, 10, 26), [0, 179, 116, 180, 47, 306])


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    rng = np.random.default_rng(seed)
    try:
        got = _lift_stage(d, D, rng, t0 + 0.45 * time_limit)
    except Exception:
        got = None
    if got is not None:
        return got
    return run(d, D, seed, 0.5 * time_limit, PLAN + _extra_plan(), FALLBACK)
