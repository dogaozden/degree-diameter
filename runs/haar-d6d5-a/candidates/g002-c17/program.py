"""Combined d=6, D=5 search: bipartite voltage lifts of small base graphs over metacyclic and Heisenberg groups.

Base graph: P base vertices per side, with a 6-regular multiplicity pattern M (row and column sums 6). Patterns:
P=1 (one A and one B vertex, six parallel darts, a Haar-type lift), P=2 ([[a,6-a],[6-a,a]]), P=3 (circulant
with at least two nonzero entries), and P=6 (K_{6,6} with single darts). Dart (a, b, g) joins (a, x) to (P+b, x*g)
for all x in G. The lift has 2P|G| vertices, is bipartite, and has max degree 6.

Check: left multiplication is an automorphism, so the diameter is at most 5 iff each of the 2P base identity sheets
reaches all vertices within 5 steps. The cost is the total number of uncovered (source, vertex) pairs, and the
search anneals voltages until the cost is 0. Every candidate is rebuilt explicitly and checked with lib.is_valid.
A checked Haar graph of order 660 is the fallback, and a tiny always-valid graph backs that up.

Jobs are (base shape, group, pattern) with 2P|G| above the record of 684. They are scheduled roughly by vertex
count, with abelian groups deprioritised and non-abelian groups (including Heisenberg mod 7 for P=1) preferred.
"""
import math
import time

import numpy as np

import lib

TARGET = (6, 5)
RECORD = 684
DEG = 6
DIAM = 5
SLICE = 1.5          # seconds per (job) attempt
STALL_LIMIT = 1500   # moves without improvement before a random restart inside one attempt
PAIR_TEMP = 0.7

FALLBACK_SPEC = (33, 10, 26)          # Z_33 x| Z_10 with r = 26, order 330
FALLBACK_S = [0, 179, 116, 180, 47, 306]


# ----------------------------------------------------------------------------- non-target and fallback graphs

def trivial(d, D):
    """Small always-valid graph for any (d, D) other than the target."""
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


# ----------------------------------------------------------------------------- groups (vectorised tables)

def meta_table(a, k, r):
    """Z_a x|_r Z_k, element (x, j) coded as x*k+j, (x,j)(y,l) = (x + r^j y, j + l). Needs r^k = 1 mod a."""
    N = a * k
    pw = np.array([pow(r, j, a) for j in range(k)], dtype=np.int64)
    g = np.arange(N, dtype=np.int64)
    ga, gj = g // k, g % k
    MT = ((ga[:, None] + pw[gj][:, None] * ga[None, :]) % a) * k + (gj[:, None] + gj[None, :]) % k
    return MT.astype(np.int64)


def heis_table(p):
    """Heisenberg group mod p, (a,b,c)(a',b',c') = (a+a', b+b', c+c'+a*b'), coded a*p^2+b*p+c."""
    q2 = p * p
    g = np.arange(p ** 3, dtype=np.int64)
    A, B, C = g // q2, (g // p) % p, g % p
    MT = (((A[:, None] + A[None, :]) % p) * q2
          + ((B[:, None] + B[None, :]) % p) * p
          + (C[:, None] + C[None, :] + A[:, None] * B[None, :]) % p)
    return MT.astype(np.int64)


def inverse_table(MT):
    return np.argmax(MT == 0, axis=1).astype(np.int64)


def get_group(spec, cache):
    if spec not in cache:
        if spec[0] == 'meta':
            MT = meta_table(spec[1], spec[2], spec[3])
        else:
            MT = heis_table(spec[1])
        cache[spec] = (MT, inverse_table(MT))
    return cache[spec]


def meta_specs(m):
    """All Z_a x|_r Z_k with a*k = m, a >= 2 (k = 1 gives cyclic groups)."""
    out = []
    for k in range(1, m + 1):
        if m % k:
            continue
        a = m // k
        if a < 2:
            continue
        for r in range(1, a):
            if math.gcd(r, a) == 1 and pow(r, k, a) == 1 % a:
                out.append(('meta', a, k, r))
    return out


# ----------------------------------------------------------------------------- base patterns

def patterns(P):
    """6-regular multiplicity matrices (row and column sums 6) for P base vertices per side."""
    if P == 1:
        return [[[6]]]
    if P == 2:
        return [[[a, 6 - a], [6 - a, a]] for a in (1, 2, 3)]
    if P == 3:
        out = []
        for r0 in range(7):
            for r1 in range(7 - r0):
                r = (r0, r1, 6 - r0 - r1)
                if sum(1 for x in r if x) < 2:      # fewer than two shifts is disconnected
                    continue
                out.append([[r[(j - i) % 3] for j in range(3)] for i in range(3)])
        return out
    if P == 6:
        return [[[1] * 6 for _ in range(6)]]
    return []


def darts_of(M, P):
    return [(a, b) for a in range(P) for b in range(P) for _ in range(M[a][b])]


# ----------------------------------------------------------------------------- lifts and cost

def lift_nb(MT, INV, P, m, darts, V):
    """Neighbour table (N, 6). A-vertex of base a is a*m+x, B-vertex of base b is (P+b)*m+y."""
    N = 2 * P * m
    nb = np.empty((N, DEG), dtype=np.int64)
    ca = [0] * P
    cb = [0] * P
    for (a, b), g in zip(darts, V):
        g = int(g)
        nb[a * m:(a + 1) * m, ca[a]] = (P + b) * m + MT[:, g]
        ca[a] += 1
        nb[(P + b) * m:(P + b + 1) * m, cb[b]] = a * m + MT[:, INV[g]]
        cb[b] += 1
    return nb


def cost(nb, P, m):
    """Uncovered (source, vertex) pairs over the 2P identity sheets. Zero means diameter <= 5."""
    N = nb.shape[0]
    total = 0
    for s in range(2 * P):
        seen = np.zeros(N, dtype=bool)
        seen[s * m] = True
        front = np.array([s * m], dtype=np.int64)
        for _ in range(DIAM):
            mark = np.zeros(N, dtype=bool)
            mark[nb[front].ravel()] = True
            mark &= ~seen
            front = np.flatnonzero(mark)
            if front.size == 0:
                break
            seen |= mark
        total += N - int(seen.sum())
    return total


def anneal(MT, INV, P, m, darts, rng, deadline):
    """Anneal voltages to cost 0. Returns V, or None at the deadline."""
    D = len(darts)
    V = rng.integers(0, m, size=D)
    cur = cost(lift_nb(MT, INV, P, m, darts, V), P, m)
    stall = 0
    while True:
        if cur == 0:
            return V
        if time.monotonic() >= deadline:
            return None
        t = int(rng.integers(D))
        old = int(V[t])
        V[t] = int(rng.integers(m))
        c = cost(lift_nb(MT, INV, P, m, darts, V), P, m)
        if c <= cur or rng.random() < math.exp(-(c - cur) / PAIR_TEMP):
            stall = 0 if c < cur else stall + 1
            cur = c
        else:
            V[t] = old
            stall += 1
        if stall > STALL_LIMIT:
            V = rng.integers(0, m, size=D)
            cur = cost(lift_nb(MT, INV, P, m, darts, V), P, m)
            stall = 0


def nb_to_graph(nb):
    N = nb.shape[0]
    edges = set()
    for v, row in enumerate(nb.tolist()):
        for w in row:
            if v != w:
                edges.add((v, w) if v < w else (w, v))
    return N, sorted(edges)


# ----------------------------------------------------------------------------- jobs and fallback

def build_jobs(rng):
    """(sort key, vertex count, P, m, darts, group spec) for every candidate above the record."""
    windows = {1: range(343, 352), 2: range(172, 179), 3: range(115, 119), 6: range(58, 61)}
    jobs = []
    for P, ms in windows.items():
        pats = [darts_of(M, P) for M in patterns(P)]
        for m in ms:
            n_target = 2 * P * m
            if n_target <= RECORD:
                continue
            specs = meta_specs(m)
            if P == 1 and m == 343:
                specs.append(('heis', 7))
            for spec in specs:
                abelian = spec[0] == 'meta' and spec[3] == 1
                for darts in pats:
                    key = n_target + rng.uniform(0, 16) + (40 if abelian else 0)
                    jobs.append((key, n_target, P, m, darts, spec))
    jobs.sort(key=lambda j: j[0])
    return jobs


def fallback(d, D):
    """Checked Haar graph of order 660; trivial graph if anything goes wrong."""
    try:
        MT = meta_table(*FALLBACK_SPEC)
        N = MT.shape[0]
        S = sorted(set(FALLBACK_S))
        edges = [(g, N + int(MT[s, g])) for s in S for g in range(N)]
        if lib.is_valid(2 * N, edges, d, D):
            return 2 * N, edges
    except Exception:
        pass
    return trivial(d, D)


# ----------------------------------------------------------------------------- entry point

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)

    t0 = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 5.0))
    end = t0 + budget
    rng = np.random.default_rng(seed)

    best = fallback(d, D)
    best_n = best[0]
    jobs = build_jobs(rng)
    cache = {}

    while time.monotonic() < end and jobs:
        progressed = False
        for job in jobs:
            now = time.monotonic()
            if now >= end:
                break
            _, n_target, P, m, darts, spec = job
            if n_target <= best_n:
                continue
            progressed = True
            try:
                MT, INV = get_group(spec, cache)
                if MT.shape[0] != m:
                    continue
                V = anneal(MT, INV, P, m, darts, rng, min(end, now + SLICE))
                if V is None:
                    continue
                nb = lift_nb(MT, INV, P, m, darts, V)
                n, edges = nb_to_graph(nb)
                if n > best_n and lib.is_valid(n, edges, d, D):
                    best = (n, edges)
                    best_n = n
            except Exception:
                continue
        if not progressed:
            break
    return best
