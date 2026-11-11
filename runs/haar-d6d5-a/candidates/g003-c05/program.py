"""Combined seed for the d=6, D=5 target (numpy and lib only).

Two search families, both scored by exact or BFS-based cost, then checked with lib.is_valid:

1. Haar graphs (base p=1, r=6) over groups of order G >= 343. The graph has 2G vertices.
   Annealing uses the incremental word-counting cost (cost 0 iff both covering conditions hold).
2. K_{p,p} voltage lifts with r parallel darts per pair (p*r = 6): (p, r) in {(2,3), (3,2), (6,1)}.
   The lift has 2pG vertices. Annealing uses a BFS cost from the 2p identity sheets, which is exact
   because left multiplication by the group is an automorphism.

Groups: metacyclic Z_a x| Z_b, Heisenberg mod p, AGL(1,q) x| subgroup, and direct products with Z_c.
Candidates are tried in order of vertex count, starting just above the record of 684. Smaller
valid graphs are the fallback, and calibration cases return instantly.
"""
import itertools
import math
import time

import numpy as np

import lib

TARGET = (6, 5)
RECORD = 684
FALLBACK_SPEC = (33, 10, 26)            # Z_33 x| Z_10, order 330 (valid Haar graph, 660 vertices)
FALLBACK_S = [0, 179, 116, 180, 47, 306]
D_HAAR = 6
K_HAAR = 24
TEMP_HAAR = 0.45
PATIENCE_HAAR = 4000
TEMP_LIFT = 1.0
PATIENCE_LIFT = 2000


# ----------------------------------------------------------------------------- group tables

def _finish(MT):
    """Return (MT, inverse array) for a table whose identity is element 0."""
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int32)
    return MT, inv


def _is_prime(p):
    return p >= 2 and all(p % x for x in range(2, int(p ** 0.5) + 1))


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k, element (a, j) coded as a*k + j, product (a, j)(b, l) = (a + lam^j b, j + l)."""
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
    """Table of a group given as (N, c) integer coordinates (identity first) and a vectorised product."""
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
    """Heisenberg group mod prime p, order p^3."""
    e = np.array(list(itertools.product(range(p), repeat=3)), dtype=np.int64)

    def mul(X, Y):
        return np.stack([(X[..., 0] + Y[..., 0]) % p, (X[..., 1] + Y[..., 1]) % p,
                         (X[..., 2] + Y[..., 2] + X[..., 0] * Y[..., 1]) % p], axis=-1)
    return _table_from_coords(e, mul)


def group_agl(q, k):
    """GF(q) x| H where H is the subgroup of order k of GF(q)^*; order q*k."""
    F = lib.GF(q)
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
        MT[g * k:(g + 1) * k] = (MT0[g][None, :, None] * k
                                 + (c[:, None, None] + c[None, None, :]) % k).reshape(k, n0 * k)
    return _finish(MT)


def base_specs(H):
    """Candidate group specs of order H (non-abelian metacyclic, Heisenberg, AGL)."""
    out = []
    for b in range(2, H + 1):
        if H % b:
            continue
        a = H // b
        if a < 3:
            continue
        for s in range(2, a):
            if math.gcd(s, a) == 1 and pow(s, b, a) == 1:
                out.append(('meta', a, b, s))
                break
    for p in range(2, 20):
        if p ** 3 == H and _is_prime(p):
            out.append(('heis', p))
    for q in range(3, H + 1):
        if H % q == 0 and lib.is_prime_power(q):
            k = H // q
            if k >= 2 and (q - 1) % k == 0:
                out.append(('agl', q, k))
    return out


def specs_for(G):
    """A few diverse group specs of order G."""
    out = []
    for c in (1, 2, 3, 4, 5, 6, 9, 13, 18):
        if G % c:
            continue
        H = G // c
        if H < 6:
            continue
        bs = base_specs(H)
        if not bs:
            continue
        for base in bs[::max(1, len(bs) // 2)][:2]:
            out.append(base if c == 1 else ('tc', base, c))
    return out[:5]


def make_group(spec):
    kind = spec[0]
    if kind == 'meta':
        return group_meta(spec[1], spec[2], spec[3])
    if kind == 'heis':
        return group_heis(spec[1])
    if kind == 'agl':
        return group_agl(spec[1], spec[2])
    return group_times_cyclic(make_group(spec[1]), spec[2])


# ----------------------------------------------------------------------------- Haar cost and search

def _cover(MT, N, P):
    cov = np.zeros(N, dtype=bool)
    cov[MT[P[:, None], P[None, :]].ravel()] = True
    return cov


def _pairs(MT, inv, S):
    Si = inv[S]
    return MT[Si[:, None], S[None, :]].ravel(), MT[S[:, None], Si[None, :]].ravel()


def cost(MT, inv, S):
    """Uncovered elements over both sides (0 = valid diameter-5 Haar graph)."""
    N = MT.shape[0]
    return sum(N - int(_cover(MT, N, np.unique(P)).sum()) for P in _pairs(MT, inv, S))


def batch_costs(MT, inv, S, i, X):
    """Cost of S with slot i replaced by each x in X (only the slot-i words are recomputed)."""
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


def haar_search(MT, inv, d, deadline, rng):
    """Anneal a d-subset of the group until cost 0 or the deadline. Returns (S, cost) or (None, big)."""
    N = MT.shape[0]
    best, bestc = None, 10 ** 9
    S, cur, since = None, None, 0
    while time.monotonic() < deadline:
        if S is None:
            S = np.concatenate([[0], rng.choice(np.arange(1, N), d - 1, replace=False)]).astype(np.int32)
            cur = cost(MT, inv, S)
            since = 0
            if cur < bestc:
                best, bestc = S.copy(), cur
            if cur == 0:
                return best, 0
        i = int(rng.integers(d))
        X = rng.integers(0, N, size=K_HAAR).astype(np.int32)
        X = X[~np.isin(X, np.delete(S, i))]
        if len(X) == 0:
            continue
        cs = batch_costs(MT, inv, S, i, X)
        j = int(np.argmin(cs + rng.random(len(cs)) * 0.5))
        delta = int(cs[j]) - cur
        if delta <= 0 or rng.random() < math.exp(-delta / TEMP_HAAR):
            S[i] = X[j]
            cur = int(cs[j])
            if cur < bestc:
                best, bestc, since = S.copy(), cur, 0
                if cur == 0:
                    return best, 0
        since += 1
        if since > PATIENCE_HAAR:
            S, cur = None, None
    return best, bestc


def haar_edges(MT, S):
    """Haar graph: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B) for s in S."""
    N = MT.shape[0]
    g = np.arange(N)
    edges = []
    for s in sorted({int(x) for x in S}):
        edges.extend((int(a), int(N + b)) for a, b in zip(g, MT[s]))
    return 2 * N, edges


# ----------------------------------------------------------------------------- voltage lifts

def lift_nb(MT, inv, p, r, VOL):
    """Neighbour table of the lift. A-vertex i*m+x, B-vertex (p+j)*m+x."""
    m = MT.shape[0]
    nb = np.empty((2 * p * m, p * r), dtype=np.int64)
    for i in range(p):
        cols = [(p + j) * m + MT[:, VOL[i, j, t]] for j in range(p) for t in range(r)]
        nb[i * m:(i + 1) * m] = np.stack(cols, axis=1)
    for j in range(p):
        cols = [i * m + MT[:, inv[VOL[i, j, t]]] for i in range(p) for t in range(r)]
        nb[(p + j) * m:(p + j + 1) * m] = np.stack(cols, axis=1)
    return nb


def lift_cost(nb, m, p):
    """Vertices missed within distance 5 over the 2p identity sheets (0 = diameter <= 5)."""
    n = nb.shape[0]
    total = 0
    for u in range(2 * p):
        src = u * m
        seen = np.zeros(n, dtype=bool)
        seen[src] = True
        front = np.array([src], dtype=np.int64)
        for _ in range(5):
            nxt = nb[front].ravel()
            nxt = np.unique(nxt[~seen[nxt]])
            if nxt.size == 0:
                break
            seen[nxt] = True
            front = nxt
        total += n - int(seen.sum())
    return total


def lift_graph(nb, p, m):
    edges = set()
    for a in range(p * m):
        for b in nb[a].tolist():
            edges.add((a, b))
    return 2 * p * m, sorted(edges)


def anneal_lift(MT, inv, p, r, rng, deadline):
    """Anneal voltages until cost 0 (return VOL) or the deadline (return None)."""
    m = MT.shape[0]

    def fresh():
        VOL = rng.integers(0, m, size=(p, p, r))
        return VOL, lift_cost(lift_nb(MT, inv, p, r, VOL), m, p)

    VOL, cur = fresh()
    best, since = cur, 0
    while cur > 0 and time.monotonic() < deadline:
        i, j, t = int(rng.integers(p)), int(rng.integers(p)), int(rng.integers(r))
        old = int(VOL[i, j, t])
        new = int(rng.integers(m))
        if new == old:
            continue
        VOL[i, j, t] = new
        c = lift_cost(lift_nb(MT, inv, p, r, VOL), m, p)
        if c <= cur or rng.random() < math.exp(-(c - cur) / TEMP_LIFT):
            cur = c
            if cur < best:
                best, since = cur, 0
            else:
                since += 1
        else:
            VOL[i, j, t] = old
            since += 1
        if since > PATIENCE_LIFT:
            VOL, cur = fresh()
            best, since = cur, 0
    return VOL if cur == 0 else None


# ----------------------------------------------------------------------------- job plan

def make_jobs():
    """(vertex count, p, r, group spec) for every candidate, smallest vertex count above the record first."""
    jobs = []
    for p, r in ((1, 6), (2, 3), (3, 2), (6, 1)):
        lo = RECORD // (2 * p) + 1
        for G in range(lo, lo + 3):
            for spec in specs_for(G):
                jobs.append((2 * p * G, p, r, spec))
    jobs.sort(key=lambda j: j[0])
    return jobs


def run_job(job, MT, inv, rng, deadline):
    """Return (n, edges) for a found cost-0 candidate, or None."""
    _, p, r, _ = job
    if p == 1:
        S, c = haar_search(MT, inv, D_HAAR, deadline, rng)
        if S is None or c != 0:
            return None
        return haar_edges(MT, S)
    VOL = anneal_lift(MT, inv, p, r, rng, deadline)
    if VOL is None:
        return None
    return lift_graph(lift_nb(MT, inv, p, r, VOL), p, MT.shape[0])


# ----------------------------------------------------------------------------- fallbacks

def safe_small(d, D):
    """Small always-valid graph for any other (d, D)."""
    cands = []
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        cands.append(lib.projective_plane_incidence(d - 1))
    if D >= 2 and d >= 1:
        cands.append((2 * d, [(i, d + j) for i in range(d) for j in range(d)]))
    if D >= 1 and d >= 1:
        cands.append((2, [(0, 1)]))
    cands.append((1, []))
    for n, edges in cands:
        try:
            if lib.is_valid(n, edges, d, D):
                return n, edges
        except Exception:
            pass
    return 1, []


def fallback_haar(d, D):
    try:
        MT, inv = make_group(('meta',) + FALLBACK_SPEC)
        n, edges = haar_edges(MT, FALLBACK_S)
        if lib.is_valid(n, edges, d, D):
            return n, edges
    except Exception:
        pass
    return None


# ----------------------------------------------------------------------------- entry point

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return safe_small(d, D)

    t0 = time.monotonic()
    budget = max(0.5, min(0.72 * time_limit, time_limit - 10.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)

    jobs = make_jobs()
    cache = {}
    best = None
    for idx, job in enumerate(jobs):
        now = time.monotonic()
        if now >= deadline:
            break
        if best is not None and job[0] <= best[0]:
            continue
        share = (deadline - now) / max(1, min(len(jobs) - idx, 12))
        try:
            spec = job[3]
            if spec not in cache:
                cache[spec] = make_group(spec)
            MT, inv = cache[spec]
            g = run_job(job, MT, inv, rng, now + share)
            if g is not None:
                n, edges = g
                if lib.is_valid(n, edges, d, D) and (best is None or n > best[0]):
                    best = (n, edges)
        except Exception:
            continue

    if best is not None:
        return best
    g = fallback_haar(d, D)
    if g is not None:
        return g
    return safe_small(d, D)
