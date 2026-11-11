"""Combined seed for the bipartite degree-diameter target (d=6, D=5).

Two searches, one shared validity check:
  A. Haar graphs over non-abelian groups of order >= 343: annealed connection sets S, with near-miss
     starts from the metacyclic and SL(2,5) x Z_3 groups. A Haar graph on group G has 2|G| vertices.
  B. Voltage lifts of small K_{p,p} multigraphs (p*r = 6) over semidirect, Heisenberg and cyclic
     groups, annealed on the voltages.

Every candidate is checked with lib.is_valid and the largest valid graph is returned. Other cases get
a small always-valid graph (for (3,3) that is the Petersen-free PG(2,2) incidence graph, 14 vertices).
"""
import itertools
import math
import time

import numpy as np

import lib

TARGET = (6, 5)
RECORD = 684
TEMP_HAAR = 0.45
PATIENCE_HAAR = 4000
TEMP_LIFT = 1.0
PATIENCE_LIFT = 2000


# ============================================================ Haar graphs: group tables

def _finish(MT):
    """Return (MT, inverse array) for a table whose identity is element 0."""
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int32)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k with (a, j) -> a*k + j and (a, j)(b, l) = (a + lam^j b, j + l). Needs lam^k = 1 mod m."""
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
    """Table of a group given by an (N, c) coordinate array (identity first) and a vectorised product."""
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


def group_sl2(p):
    """SL(2, p) for a prime p, order p(p^2-1)."""
    allm = np.array(list(itertools.product(range(p), repeat=4)), dtype=np.int64)
    allm = allm[(allm[:, 0] * allm[:, 3] - allm[:, 1] * allm[:, 2]) % p == 1]
    ident = np.nonzero((allm == np.array([1, 0, 0, 1])).all(axis=1))[0][0]
    allm = np.vstack([allm[ident:ident + 1], np.delete(allm, ident, axis=0)])

    def mul(X, Y):
        a, b, c, d = (X[..., i] for i in range(4))
        e, f, g, h = (Y[..., i] for i in range(4))
        return np.stack([(a * e + b * g) % p, (a * f + b * h) % p, (c * e + d * g) % p, (c * f + d * h) % p], axis=-1)
    return _table_from_coords(allm, mul)


def group_agl(q, k=None):
    """GF(q) x| C_k, the affine maps t -> a*t + b with a of order k (default AGL(1, q))."""
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


# ============================================================ Haar graphs: connection-set search

def _cover(MT, N, P):
    cov = np.zeros(N, dtype=bool)
    cov[MT[P[:, None], P[None, :]].ravel()] = True
    return cov


def _pairs(MT, inv, S):
    Si = inv[S]
    return MT[Si[:, None], S[None, :]].ravel(), MT[S[:, None], Si[None, :]].ravel()


def cost(MT, inv, S):
    """Uncovered elements, both sides (0 = valid diameter-5 Haar graph)."""
    N = MT.shape[0]
    return sum(N - int(_cover(MT, N, np.unique(P)).sum()) for P in _pairs(MT, inv, S))


def batch_costs(MT, inv, S, i, X):
    """Cost of S with slot i replaced by each x in X (only slot-i words are recomputed)."""
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
    """Score every single-slot replacement of S. Returns (best cost, best S)."""
    N = MT.shape[0]
    best, bestS = 10 ** 9, None
    for i in range(len(S)):
        rest = np.delete(S, i)
        for lo in range(0, N, chunk):
            if time.monotonic() >= deadline:
                return best, bestS
            X = np.arange(lo, min(N, lo + chunk), dtype=np.int32)
            X = X[~np.isin(X, rest)]
            if len(X) == 0:
                continue
            cs = batch_costs(MT, inv, S, i, X)
            j = int(np.argmin(cs))
            if cs[j] < best:
                best, bestS = int(cs[j]), S.copy()
                bestS[i] = X[j]
    return best, bestS


def search(MT, inv, d, S0, deadline, rng, K=24, temp=TEMP_HAAR, patience=PATIENCE_HAAR):
    """Anneal a d-subset of the group. Optional start S0 (one-swap scan first). Returns (S, cost)."""
    N = MT.shape[0]
    S0 = None if S0 is None else np.array(S0, dtype=np.int32)
    best, bestc = None, 10 ** 9
    S, cur, since = (S0.copy() if S0 is not None else None), None, 0

    def random_set():
        return np.concatenate([[0], rng.choice(np.arange(1, N), d - 1, replace=False)]).astype(np.int32)

    if S0 is not None:
        c0 = cost(MT, inv, S0)
        best, bestc = S0.copy(), c0
        if c0 == 0:
            return best, 0
        c1, S1 = one_swap_scan(MT, inv, S0, time.monotonic() + 0.25 * max(0.0, deadline - time.monotonic()))
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
    """Haar graph edges: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


# ============================================================ voltage lifts of K_{p,p}

def group_table(order, mul):
    """Multiplication table (identity index 0) and inverse array for a group given by mul(x, y)."""
    MT = np.empty((order, order), dtype=np.int64)
    for x in range(order):
        MT[x] = [mul(x, y) for y in range(order)]
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
    return MT, inv


def heis_mul(p):
    """Heisenberg group mod p, element (a, b, c) coded as a*p^2 + b*p + c."""
    q2 = p * p

    def mul(x, y):
        a1, rest1 = divmod(x, q2)
        b1, c1 = divmod(rest1, p)
        a2, rest2 = divmod(y, q2)
        b2, c2 = divmod(rest2, p)
        return ((a1 + a2) % p) * q2 + ((b1 + b2) % p) * p + (c1 + c2 + a1 * b2) % p
    return mul


def make_lift_group(spec):
    """(MT, inv) for a lift-group spec: ('sd', m, k, r), ('heis', p) or ('cyc', G)."""
    if spec[0] == 'sd':
        _, a, b, s = spec
        order, mul, _ = lib.semidirect_group(a, b, s)
        return group_table(order, mul)
    if spec[0] == 'heis':
        p = spec[1]
        return group_table(p ** 3, heis_mul(p))
    G = spec[1]
    return group_table(G, lambda x, y: (x + y) % G)


def specs_of_order(G):
    """A few non-abelian metacyclic groups of order G, Heisenberg if applicable, then cyclic."""
    sd = []
    for b in range(2, G):
        if G % b:
            continue
        a = G // b
        if a < 3:
            continue
        for s in range(2, a):
            if math.gcd(s, a) == 1 and pow(s, b, a) == 1:
                sd.append(('sd', a, b, s))
    picked = sd[::max(1, len(sd) // 3)][:4]
    p = round(G ** (1.0 / 3.0))
    if p >= 2 and p ** 3 == G and lib.is_prime_power(p):
        picked.append(('heis', p))
    picked.append(('cyc', G))
    return picked


def lift_nb(MT, inv, p, r, VOL):
    """Neighbour table: A-vertex i*m+x, B-vertex (p+j)*m+x. Dart (i, j, t) with voltage g: A x ~ B x*g."""
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
    """Vertices missed within distance 5 by the 2p identity-sheet BFS. 0 means diameter <= 5."""
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
    n = 2 * p * m
    edges = set()
    for a in range(p * m):
        for b in nb[a].tolist():
            edges.add((a, b))
    return n, sorted(edges)


def anneal_lift(MT, inv, p, r, rng, deadline):
    """Anneal voltages to cost 0 (return VOL) or until the deadline (return None)."""
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


# ============================================================ plans and fallbacks

# (name, group builder, start S0 or None, weight). Near-miss starts are element indices of the table.
HAAR_PLAN = [
    ('meta 117/3/16, order 351, 2 short', lambda: group_meta(117, 3, 16), [0, 184, 47, 48, 65, 21], 3),
    ('meta 71/5/5, order 355, 2 short', lambda: group_meta(71, 5, 5), [0, 92, 218, 269, 205, 88], 3),
    ('SL(2,5) x Z_3, order 360, 4 short', lambda: group_times_cyclic(group_sl2(5), 3), [0, 246, 216, 211, 99, 132], 2),
    ('Heis(3) x Z_13, order 351', lambda: group_times_cyclic(group_heis(3), 13), None, 2),
    ('meta 49/7/8, order 343', lambda: group_meta(49, 7, 8), None, 1),
    ('Heis(7), order 343', lambda: group_heis(7), None, 1),
    ('AGL(1,9) x Z_5, order 360', lambda: group_times_cyclic(group_agl(9), 5), None, 1),
    ('AGL(1,5) x Z_18, order 360', lambda: group_times_cyclic(group_agl(5), 18), None, 1),
]

FALLBACK_HAAR = (lambda: group_meta(33, 10, 26), [0, 179, 116, 180, 47, 306])


def safe_small(d, D):
    """Small graph that is valid for (d, D), chosen among a few simple constructions."""
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


def _target(seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.75 * time_limit, time_limit - 10.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)
    d, D = TARGET
    best = [None]

    def best_n():
        return best[0][0] if best[0] is not None else RECORD

    def consider(n, edges):
        if (best[0] is None or n > best[0][0]) and lib.is_valid(n, edges, d, D):
            best[0] = (n, edges)

    # Phase A: Haar graphs (about half the budget).
    haar_end = t0 + 0.5 * budget
    total_w = sum(entry[3] for entry in HAAR_PLAN)
    for name, builder, S0, w in HAAR_PLAN:
        now = time.monotonic()
        if now >= haar_end:
            break
        end = now + (haar_end - now) * w / total_w
        total_w -= w
        try:
            MT, inv = builder()
            if 2 * MT.shape[0] <= best_n():
                continue
            S, c = search(MT, inv, d, S0, end, rng)
            if S is not None and c == 0:
                n, edges = haar_edges(MT, S)
                consider(n, edges)
        except Exception:
            continue

    # Phase B: voltage lifts of small base multigraphs, smallest candidate sizes first.
    jobs = []
    for p, r in ((6, 1), (3, 2), (2, 3), (1, 6)):
        g_lo = RECORD // (2 * p) + 1
        for G in range(g_lo, g_lo + 3):
            for spec in specs_of_order(G):
                jobs.append((2 * p * G, p, r, spec))
    jobs.sort(key=lambda x: x[0])

    cache = {}
    for idx, (n_target, p, r, spec) in enumerate(jobs):
        now = time.monotonic()
        if now >= deadline:
            break
        if n_target <= best_n():
            continue
        share = (deadline - now) / max(1, min(len(jobs) - idx, 12))
        try:
            if spec not in cache:
                cache[spec] = make_lift_group(spec)
            MT, inv = cache[spec]
            VOL = anneal_lift(MT, inv, p, r, rng, now + share)
            if VOL is None:
                continue
            nb = lift_nb(MT, inv, p, r, VOL)
            n, edges = lift_graph(nb, p, MT.shape[0])
            consider(n, edges)
        except Exception:
            continue

    if best[0] is None:
        try:
            MT, inv = FALLBACK_HAAR[0]()
            n, edges = haar_edges(MT, FALLBACK_HAAR[1])
            consider(n, edges)
        except Exception:
            pass
    if best[0] is None:
        return safe_small(d, D)
    return best[0]


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return safe_small(d, D)
    return _target(seed, time_limit)
