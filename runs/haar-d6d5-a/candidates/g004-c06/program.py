"""Combined degree-6, diameter-5 search.

Voltage lifts of small bipartite base graphs over non-abelian groups (from g001-c02), with the group
catalogue of g000-i01 (Heisenberg, AGL(1,q) x Z_k, metacyclic, and products with cyclic groups).

Base graph: p A-vertices and p B-vertices, each pair joined by r parallel darts, p*r = 6. A lift over a group G of
order m has 2*p*m vertices. Dart (i, j, t) with voltage g joins A-vertex (i, x) to B-vertex (j, x*g).
Left multiplication is an automorphism, so the diameter is at most 5 iff, for each of the 2p base vertices, a BFS
from its identity sheet reaches every vertex within 5 steps. cost = number of vertices missed (0 means valid).

Search: annealing over the voltages with several proposals per step, for candidate (base shape, group) pairs,
sorted by vertex count starting just above the record. Every returned graph is checked with lib.is_valid. If
nothing beats the record, a valid Haar fallback (660 vertices) is returned, then a tiny always-valid graph.
"""
import itertools
import math
import time

import numpy as np

import lib

TARGET = (6, 5)
RECORD = 684
TEMP = 1.0          # annealing temperature, in units of uncovered vertices
PATIENCE = 1500     # steps without improvement before a random restart
PROPOSALS = 3       # replacement values tried per annealing step (best one is kept)

FALLBACK_SPEC = (33, 10, 26)            # semidirect Z_33 x| Z_10, order 330
FALLBACK_S = [0, 179, 116, 180, 47, 306]


# ----------------------------------------------------------------------------- group tables

def _finish(MT):
    """Return (MT, inverse array) for a table whose identity is element 0."""
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int32)
    return MT, inv


def _table_from_coords(elems, mulfun):
    """Table of a group given as an (N, c) coordinate array (identity first) and a vectorised product."""
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


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k, element (a, j) coded as a*k + j, (a, j)(b, l) = (a + lam^j b, j + l). Needs lam^k = 1 mod m."""
    pw = np.array([pow(lam, j, m) for j in range(k)], dtype=np.int64)
    N = m * k
    g = np.arange(N, dtype=np.int64)
    a, j = g // k, g % k
    MT = np.empty((N, N), dtype=np.int32)
    for lo in range(0, N, 256):
        hi = min(N, lo + 256)
        MT[lo:hi] = ((a[lo:hi, None] + pw[j[lo:hi], None] * a[None, :]) % m) * k \
            + (j[lo:hi, None] + j[None, :]) % k
    return _finish(MT)


def group_heis(p):
    """Heisenberg group mod prime p, order p^3."""
    e = np.array(list(itertools.product(range(p), repeat=3)), dtype=np.int64)

    def mul(X, Y):
        return np.stack([(X[..., 0] + Y[..., 0]) % p, (X[..., 1] + Y[..., 1]) % p,
                         (X[..., 2] + Y[..., 2] + X[..., 0] * Y[..., 1]) % p], axis=-1)
    return _table_from_coords(e, mul)


def group_agl(q, k):
    """GF(q) x| C_k: maps t -> a*t + b with a in the order-k subgroup of GF(q)^*. Order q*k."""
    F = lib.GF(q)
    H = [a for a in range(1, q) if F.pow(a, k) == 1]
    e = np.array([(0, 1)] + [(b, a) for b in range(q) for a in H if (b, a) != (0, 1)], dtype=np.int64)
    add, mulT = F.add_table, F.mul_table

    def mul(X, Y):
        return np.stack([add[X[..., 0], mulT[X[..., 1], Y[..., 0]]], mulT[X[..., 1], Y[..., 1]]], axis=-1)
    return _table_from_coords(e, mul)


def group_times_cyclic(grp, k):
    """Direct product of a table group with Z_k; element (g, c) has index g*k + c."""
    MT0, _ = grp
    n0 = MT0.shape[0]
    c = np.arange(k, dtype=np.int64)
    MT = np.empty((n0 * k, n0 * k), dtype=np.int32)
    for g in range(n0):
        block = MT0[g][None, :, None].astype(np.int64) * k + (c[:, None, None] + c[None, None, :]) % k
        MT[g * k:(g + 1) * k] = block.reshape(k, n0 * k)
    return _finish(MT)


def group_cyc(G):
    ar = np.arange(G, dtype=np.int64)
    return _finish((ar[:, None] + ar[None, :]) % G)


def make_group(spec):
    """Build (MT, inv) for a group spec."""
    kind = spec[0]
    if kind == 'sd':
        return group_meta(spec[1], spec[2], spec[3])
    if kind == 'heis':
        return group_heis(spec[1])
    if kind == 'agl':
        return group_agl(spec[1], spec[2])
    if kind == 'prod':
        return group_times_cyclic(make_group(spec[1]), spec[2])
    if kind == 'cyc':
        return group_cyc(spec[1])
    raise ValueError(spec)


def _is_prime(n):
    return n >= 2 and all(n % i for i in range(2, int(n ** 0.5) + 1))


def sd_specs(G):
    """Metacyclic Z_a x| Z_b specs of order G with a >= 3 and nontrivial action."""
    out = []
    for b in range(2, G):
        if G % b:
            continue
        a = G // b
        if a < 3:
            continue
        for s in range(2, a):
            if math.gcd(s, a) == 1 and pow(s, b, a) == 1:
                out.append(('sd', a, b, s))
    return out


def specs_for_order(G):
    """Candidate group specs of order G: non-abelian families first, cyclic last."""
    out = []
    sd = sd_specs(G)
    if sd:
        step = max(1, len(sd) // 4)
        out += sd[::step][:4]
    for pp in range(2, 20):
        if pp ** 3 == G and _is_prime(pp):
            out.append(('heis', pp))
    for q in range(3, min(G, 64) + 1):
        if G % q == 0 and lib.is_prime_power(q):
            k = G // q
            if 2 <= k < q and (q - 1) % k == 0:
                out.append(('agl', q, k))
    for c in range(2, 13):
        if G % c == 0 and G // c >= 6:
            base = sd_specs(G // c)
            if base:
                out.append(('prod', base[len(base) // 2], c))
    out.append(('cyc', G))
    return out


# ----------------------------------------------------------------------------- lifts

def lift_nb(MT, inv, p, r, VOL):
    """Neighbour table: row v lists the neighbours of vertex v (A-vertex i*m+x, B-vertex (p+j)*m+y)."""
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
    """Vertices at distance > 5 from the identity sheet of each base vertex, summed. 0 means diameter <= 5."""
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
    """Edge list of the lift, read from the A-rows."""
    n = 2 * p * m
    edges = set()
    for a in range(p * m):
        for b in nb[a].tolist():
            edges.add((a, b))
    return n, sorted(edges)


def anneal_lift(MT, inv, p, r, rng, deadline):
    """Anneal voltages until cost 0 (return VOL) or the deadline (return None)."""
    m = MT.shape[0]

    def cost_of(V):
        return lift_cost(lift_nb(MT, inv, p, r, V), m, p)

    VOL = rng.integers(0, m, size=(p, p, r))
    cur = cost_of(VOL)
    best, since = cur, 0
    while cur > 0 and time.monotonic() < deadline:
        if since > PATIENCE:
            VOL = rng.integers(0, m, size=(p, p, r))
            cur = cost_of(VOL)
            best, since = cur, 0
            continue
        i, j, t = int(rng.integers(p)), int(rng.integers(p)), int(rng.integers(r))
        old = int(VOL[i, j, t])
        bestc, bestv = None, None
        for v in rng.integers(0, m, size=PROPOSALS):
            v = int(v)
            if v == old:
                continue
            VOL[i, j, t] = v
            c = cost_of(VOL)
            if bestc is None or c < bestc:
                bestc, bestv = c, v
        VOL[i, j, t] = old
        if bestc is None:
            since += 1
            continue
        if bestc <= cur or rng.random() < math.exp(-(bestc - cur) / TEMP):
            VOL[i, j, t] = bestv
            cur = bestc
        if cur < best:
            best, since = cur, 0
        else:
            since += 1
    return VOL if cur == 0 else None


# ----------------------------------------------------------------------------- fallbacks

def haar(MT, S):
    """Haar graph: A-vertex g ~ B-vertex s*g for s in S; returns (2N, edges)."""
    N = MT.shape[0]
    S = sorted(set(int(s) for s in S))
    edges = [(g, N + int(MT[s, g])) for s in S for g in range(N)]
    return 2 * N, edges


def safe_small(d, D):
    """Small graph valid for (d, D), chosen among a few simple constructions."""
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


# ----------------------------------------------------------------------------- entry point

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return safe_small(d, D)

    t0 = time.monotonic()
    budget = max(0.5, min(0.75 * time_limit, time_limit - 10.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)

    # Jobs: (vertex count, p, r, group spec), smallest vertex counts above the record first.
    jobs = []
    for p, r in ((1, 6), (2, 3), (3, 2), (6, 1)):
        g_lo = RECORD // (2 * p) + 1          # 2*p*G > RECORD
        for G in range(g_lo, g_lo + 3):
            for spec in specs_for_order(G):
                jobs.append((2 * p * G, p, r, spec))
    jobs.sort(key=lambda x: x[0])

    best = None
    cache = {}
    for idx, (n_target, p, r, spec) in enumerate(jobs):
        now = time.monotonic()
        if now >= deadline:
            break
        if best is not None and n_target <= best[0]:
            continue
        share = (deadline - now) / max(1, min(len(jobs) - idx, 12))
        try:
            if spec not in cache:
                cache[spec] = make_group(spec)
            MT, inv = cache[spec]
            VOL = anneal_lift(MT, inv, p, r, rng, now + share)
            if VOL is None:
                continue
            nb = lift_nb(MT, inv, p, r, VOL)
            n, edges = lift_graph(nb, p, MT.shape[0])
            if lib.is_valid(n, edges, d, D):
                best = (n, edges)
        except Exception:
            continue

    if best is not None:
        return best

    try:
        MT, inv = group_meta(*FALLBACK_SPEC)
        n, edges = haar(MT, FALLBACK_S)
        if lib.is_valid(n, edges, d, D):
            return n, edges
    except Exception:
        pass
    return safe_small(d, D)
