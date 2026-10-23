"""Bound-pruned metacyclic sweep with greedy coverage seeding for the bipartite degree-diameter problem.

NEW IDEAS THIS VERSION.
1. Greedy coverage seeding: instead of a random starting connection set, grow S one element at a time,
   always adding the candidate that leaves the fewest uncovered group elements (ties broken at random).
   A set with cost 0 needs far fewer annealing steps when it starts from a high-coverage seed.
2. Bound-pruned sweep: a Haar graph on group G has 2|G| vertices. Every metacyclic group Z_m x|_lam Z_k
   (m prime, lam of prime-power order t | gcd(k, m-1), so lam != 1 and the group is non-abelian) with
   |G| in [lo, 2100] is a candidate. Candidates are tried in ascending order of |G|, starting just above the
   order of the current best valid graph. Any valid hit raises the bar and prunes everything smaller.

Haar graph theory: vertices (g, A) = g and (g, B) = N + g, edges (g, A) ~ (s*g, B) for s in S.
Diameter <= 5 iff (S^-1 S)^2 = G and (S S^-1)^2 = G. Every result is checked with lib.is_valid.
"""
import math
import time

import numpy as np

import lib

TARGET = (10, 5)          # the only (d, D) this program searches for
SLICE = 4.0               # seconds per candidate group per pass
FRAC = 0.72               # fraction of time_limit used for search
HI_ORDER = 2100           # largest group order considered
FALLBACK_GROUP = (199, 9, 180)
FALLBACK_S = [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]   # valid, group order 1791


# ------------------------------------------------------------------ group tables

def _finish(MT):
    """Return (MT, inverse array) for a table whose identity is element 0."""
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int32)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k, element (a, j) -> index a*k + j, (a, j)(b, l) = (a + lam^j b, j + l). Needs lam^k = 1 mod m."""
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
    return n >= 2 and all(n % q for q in range(2, int(n ** 0.5) + 1))


def _primitive_root(p):
    """A primitive root mod the prime p (p >= 3)."""
    n = p - 1
    fac, x, q = [], n, 2
    while q * q <= x:
        if x % q == 0:
            fac.append(q)
            while x % q == 0:
                x //= q
        q += 1
    if x > 1:
        fac.append(x)
    for g in range(2, p):
        if all(pow(g, n // f, p) != 1 for f in fac):
            return g
    return 1


def meta_candidates(lo, hi):
    """(order, m, k, lam) for non-abelian metacyclic groups Z_m x|_lam Z_k of order m*k in [lo, hi].
    m is prime, lam has order tp > 1 with tp | gcd(k, m-1), so lam^k = 1 and lam != 1."""
    out = []
    for m in range(3, hi // 2 + 1):
        if not _is_prime(m):
            continue
        g = _primitive_root(m)
        for k in range(max(2, -(-lo // m)), hi // m + 1):
            t = math.gcd(k, m - 1)
            for tp in range(2, t + 1):
                if t % tp == 0:
                    out.append((m * k, m, k, pow(g, (m - 1) // tp, m)))
    out.sort(key=lambda c: (c[0], c[1]))
    return out


# ------------------------------------------------------------------ cost machinery

def _cover(MT, N, P):
    """Boolean array of the elements covered by the products P[i]*P[j]."""
    cov = np.zeros(N, dtype=bool)
    cov[MT[P[:, None], P[None, :]].ravel()] = True
    return cov


def cost(MT, inv, S):
    """Uncovered elements over both sides (0 means diameter 5). Works for partial sets too."""
    N = MT.shape[0]
    Si = inv[S]
    total = 0
    for P in (MT[Si[:, None], S[None, :]].ravel(), MT[S[:, None], Si[None, :]].ravel()):
        total += N - int(_cover(MT, N, np.unique(P)).sum())
    return total


def batch_costs(MT, inv, S, i, X):
    """cost of S with slot i replaced by each x in X (only the words that involve the slot are recomputed)."""
    N = MT.shape[0]
    K = len(X)
    rest = np.delete(S, i)
    total = np.zeros(K, dtype=np.int64)
    offs = (np.arange(K, dtype=np.int64) * N)[:, None]
    ri = inv[rest]
    xi = inv[X]
    for side in (0, 1):
        if side == 0:
            F = np.unique(MT[ri[:, None], rest[None, :]])
            Q = np.concatenate([MT[xi[:, None], rest[None, :]], MT[ri[None, :], X[:, None]]], axis=1)
        else:
            F = np.unique(MT[rest[:, None], ri[None, :]])
            Q = np.concatenate([MT[X[:, None], ri[None, :]], MT[rest[None, :], xi[:, None]]], axis=1)
        base = _cover(MT, N, F)
        W = np.concatenate([MT[Q[:, :, None], F[None, None, :]].reshape(K, -1),
                            MT[F[None, None, :], Q[:, :, None]].reshape(K, -1),
                            MT[Q[:, :, None], Q[:, None, :]].reshape(K, -1)], axis=1)
        new = ~base[W]
        flat = (W + offs)[new]
        cnt = np.bincount(flat, minlength=K * N).reshape(K, N)
        total += N - int(base.sum()) - (cnt > 0).sum(axis=1)
    return total


# ------------------------------------------------------------------ NEW: greedy coverage seed

def greedy_seed(MT, inv, d, rng, cand_n=300):
    """Grow S from {identity} by adding, each step, a random candidate that minimises the uncovered count.
    WLOG the identity lies in S (left or right translation does not change validity)."""
    N = MT.shape[0]
    S = [0]
    while len(S) < d:
        pool = rng.choice(np.arange(1, N), size=min(cand_n, N - 1), replace=False)
        pool = [int(x) for x in pool if int(x) not in S]
        if not pool:
            break
        vals = np.array([cost(MT, inv, np.array(S + [x], dtype=np.int32)) for x in pool])
        ties = np.flatnonzero(vals == vals.min())
        S.append(pool[int(rng.choice(ties))])
    while len(S) < d:  # only reached in degenerate tiny groups
        x = int(rng.integers(1, N))
        if x not in S:
            S.append(x)
    return np.array(S, dtype=np.int32)


def anneal(MT, inv, d, S0, end, rng, K=24, temp=0.45, patience=3000):
    """Metropolis annealing on S: each step scores K random replacements of one slot."""
    N = MT.shape[0]
    S = S0.copy()
    cur = cost(MT, inv, S)
    best, bestc = S.copy(), cur
    since = 0
    while bestc > 0 and time.monotonic() < end and since <= patience:
        i = int(rng.integers(d))
        X = rng.integers(0, N, size=K).astype(np.int32)
        X = np.unique(X[~np.isin(X, np.delete(S, i))])
        if len(X) == 0:
            continue
        cs = batch_costs(MT, inv, S, i, X)
        j = int(np.argmin(cs + rng.random(len(cs)) * 0.5))
        delta = int(cs[j]) - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            S[i] = X[j]
            cur = int(cs[j])
        since += 1
        if cur < bestc:
            best, bestc, since = S.copy(), cur, 0
    return best, bestc


# ------------------------------------------------------------------ graph

def haar_edges(MT, S):
    """A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def checked(MT, S, d, D):
    """The Haar graph for S, or None unless lib.is_valid accepts it."""
    n, edges = haar_edges(MT, S)
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


def attack(MT, inv, d, D, rng, end):
    """Repeated greedy-seeded (or random-seeded) annealing restarts until a valid S or the time ends."""
    N = MT.shape[0]
    while time.monotonic() < end:
        if rng.random() < 0.7:
            S = greedy_seed(MT, inv, d, rng)
        else:
            S = np.concatenate([[0], rng.choice(np.arange(1, N), d - 1, replace=False)]).astype(np.int32)
        S, c = anneal(MT, inv, d, S, end, rng)
        if c == 0:
            g = checked(MT, S, d, D)
            if g is not None:
                return g
    return None


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


# ------------------------------------------------------------------ entry point

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    deadline = t0 + FRAC * time_limit
    rng = np.random.default_rng(seed)

    best = None
    try:
        MT, _ = group_meta(*FALLBACK_GROUP)
        best = checked(MT, FALLBACK_S, d, D)
    except Exception:
        best = None
    if best is None:
        best = trivial(d, D)

    cands = meta_candidates(best[0] // 2 + 1, HI_ORDER)
    while time.monotonic() < deadline:
        pass_start = time.monotonic()
        attempted = False
        for N, m, k, lam in cands:
            now = time.monotonic()
            if now >= deadline:
                break
            if 2 * N <= best[0]:
                continue
            attempted = True
            try:
                MT, inv = group_meta(m, k, lam)
            except Exception:
                continue
            g = attack(MT, inv, d, D, rng, min(deadline, now + SLICE))
            if g is not None and g[0] > best[0]:
                best = g
        if not attempted or time.monotonic() - pass_start < 1e-3:
            break
    return best
