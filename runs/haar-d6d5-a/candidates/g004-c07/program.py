"""Degree-6, diameter-5 target: voltage lifts of small bipartite base graphs over non-abelian groups.

Base graph: K_{p,p} where every pair is joined by r parallel darts, with p*r = 6, so every base vertex has degree 6.
A voltage lift over a group G of order m has 2*p*m vertices. Dart (i, j, t) with voltage g joins A-vertex (i, x)
to B-vertex (j, x*g) for every x in G. The lift is bipartite with max degree 6.

Left multiplication by any h in G is an automorphism, so dist((u,x),(v,y)) = dist((u,e),(v,x^-1 y)). The diameter
is therefore at most 5 iff, for each of the 2p base vertices, the BFS from its identity sheet reaches every vertex
within 5 steps. cost(VOL) = total number of vertices missed by those 2p searches (0 means valid).

Search: simulated annealing over the voltages, per candidate (base shape, group). Phase 1 searches sizes above the
record, smallest first, to try to beat it. Phase 2, run only if phase 1 finds nothing, searches sizes between the
Haar fallback (660) and the record, largest first, so a near-record graph is returned instead of the fallback.
Every returned graph is checked with lib.is_valid. If nothing is found, the Haar fallback (660 vertices) is returned,
and a tiny always-valid graph backs that up.
"""
import math
import time

import numpy as np

import lib

TARGET = (6, 5)
RECORD = 684
FALLBACK_N = 660    # order of the Haar fallback graph below
TEMP = 1.0          # annealing temperature in units of uncovered vertices
PATIENCE = 2000     # steps without improvement before a restart
ABOVE_FRAC = 0.6    # share of the search budget given to sizes above the record
PR_SHAPES = ((6, 1), (3, 2), (2, 3), (1, 6))

FALLBACK_SPEC = (33, 10, 26)            # semidirect Z_33 x| Z_10, order 330
FALLBACK_S = [0, 179, 116, 180, 47, 306]


# ----------------------------------------------------------------------------- groups

def group_table(order, mul):
    """Multiplication table MT[x, y] = mul(x, y) (identity must be index 0) and the inverse array."""
    MT = np.empty((order, order), dtype=np.int64)
    for x in range(order):
        MT[x] = [mul(x, y) for y in range(order)]
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
    return MT, inv


def heis_mul(p):
    """Heisenberg group mod p, element (a, b, c) coded as a*p^2 + b*p + c, (a,b,c)(a',b',c') = (a+a', b+b', c+c'+a*b')."""
    q2 = p * p

    def mul(x, y):
        a1, rest1 = divmod(x, q2)
        b1, c1 = divmod(rest1, p)
        a2, rest2 = divmod(y, q2)
        b2, c2 = divmod(rest2, p)
        return ((a1 + a2) % p) * q2 + ((b1 + b2) % p) * p + (c1 + c2 + a1 * b2) % p
    return mul


def make_group(spec):
    """Build (MT, inv) for a group spec."""
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
    """Candidate groups of order G: a few non-abelian metacyclic ones, Heisenberg if applicable, then cyclic."""
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


# ----------------------------------------------------------------------------- lifts

def lift_nb(MT, inv, p, r, VOL):
    """Neighbour table: row v lists the neighbours of vertex v (A-vertex i*m+x, B-vertex (p+j)*m+x)."""
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
    """Number of (source, vertex) pairs at distance > 5 over the 2p identity sheets. 0 means diameter <= 5."""
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
    """Edge list of the lift (A-rows determine all edges)."""
    n = 2 * p * m
    edges = set()
    for a in range(p * m):
        for b in nb[a].tolist():
            edges.add((a, b))
    return n, sorted(edges)


def anneal_lift(MT, inv, p, r, rng, deadline):
    """Anneal voltages until cost 0 (return VOL) or the deadline (return None)."""
    m = MT.shape[0]

    def fresh():
        VOL = rng.integers(0, m, size=(p, p, r))
        nb = lift_nb(MT, inv, p, r, VOL)
        return VOL, lift_cost(nb, m, p)

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
        if c <= cur or rng.random() < math.exp(-(c - cur) / TEMP):
            cur = c
            if cur < best:
                best, since = cur, 0
            else:
                since += 1
        else:
            VOL[i, j, t] = old
            since += 1
        if since > PATIENCE:
            VOL, cur = fresh()
            best, since = cur, 0
    return VOL if cur == 0 else None


# ----------------------------------------------------------------------------- job search

def make_jobs(lo, hi=None):
    """Jobs (vertex count, p, r, group spec) with vertex count > lo.

    hi is None: the three smallest group orders above lo (the sizes that try to beat the record).
    hi given:   the largest group orders with count in (lo, hi] (the sizes that beat the fallback).
    """
    jobs = []
    for p, r in PR_SHAPES:
        half = 2 * p
        g_lo = lo // half + 1
        if hi is None:
            g_range = range(g_lo, g_lo + 3)
        else:
            g_hi = hi // half
            g_range = range(max(g_lo, g_hi - 3), g_hi + 1)
        for G in g_range:
            for spec in specs_of_order(G):
                jobs.append((half * G, p, r, spec))
    return jobs


def run_jobs(jobs, deadline, rng, cache, d, D, descending):
    """Anneal each job in turn and return the first valid graph (descending) or the largest valid one (ascending)."""
    jobs = sorted(jobs, key=lambda x: x[0], reverse=descending)
    best = None
    for idx, (n_target, p, r, spec) in enumerate(jobs):
        now = time.monotonic()
        if now >= deadline:
            break
        if best is not None and (descending or n_target <= best[0]):
            if descending:
                break
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
    return best


# ----------------------------------------------------------------------------- fallbacks

def haar(MT, S):
    """Haar graph: A-vertex g ~ B-vertex s*g for s in S; returns (2N, edges)."""
    N = MT.shape[0]
    S = sorted(set(int(s) for s in S))
    edges = [(g, N + int(MT[s, g])) for s in S for g in range(N)]
    return 2 * N, edges


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


# ----------------------------------------------------------------------------- entry point

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return safe_small(d, D)

    t0 = time.monotonic()
    budget = max(0.5, min(0.75 * time_limit, time_limit - 10.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)
    cache = {}

    # Phase 1: sizes above the record, smallest first.
    now = time.monotonic()
    phase1_deadline = now + ABOVE_FRAC * (deadline - now)
    best = run_jobs(make_jobs(RECORD), phase1_deadline, rng, cache, d, D, descending=False)

    # Phase 2: sizes between the fallback and the record, largest first.
    if best is None:
        best = run_jobs(make_jobs(FALLBACK_N, RECORD), deadline, rng, cache, d, D, descending=True)

    if best is not None:
        return best

    try:
        MT, inv = group_table(*lib.semidirect_group(*FALLBACK_SPEC)[:2])
        n, edges = haar(MT, FALLBACK_S)
        if lib.is_valid(n, edges, d, D):
            return n, edges
    except Exception:
        pass
    return safe_small(d, D)
