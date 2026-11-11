"""Degree-6, diameter-5 target: Haar-style lifts over non-abelian groups with a multi-vertex base.

Construction: a 6-regular bipartite base with k A-vertices and k B-vertices, given by six permutations
sig[t] (dart t joins A_i to B_{sig[t][i]}). Each dart carries a voltage V[t][i] in a finite group G.
The lift has 2kG vertices: A(i,x) ~ B(sig[t][i], x*g) for every dart. Left multiplication is an
automorphism, so the diameter is at most 5 iff the BFS from the identity of each of the 2k base
sheets reaches every vertex within 5 steps. Annealing minimises the number of missed vertices over
the voltages and the permutations. k = 1 is a Haar graph, and k >= 2 is the new multi-vertex base.
Targets use 2kG >= 686, so a success beats the record of 684. Every result is checked with lib.is_valid.
Fallback: the 660-vertex Haar graph, then a small valid graph.
"""
import math
import time

import numpy as np

import lib

TARGET = (6, 5)
RECORD = 684
DEG = 6
DIAM = 5
TEMP = 0.6
PATIENCE = 1500
SLICE = 1.5

FALLBACK_SPEC = ('sd', 33, 10, 26)
FALLBACK_S = [0, 179, 116, 180, 47, 306]


# ----------------------------------------------------------------------------- groups

def heis_mul(p):
    """Heisenberg group mod p, element (a, b, c) coded as a*p^2 + b*p + c; identity is index 0."""
    q2 = p * p

    def mul(x, y):
        a1, rest1 = divmod(x, q2)
        b1, c1 = divmod(rest1, p)
        a2, rest2 = divmod(y, q2)
        b2, c2 = divmod(rest2, p)
        return ((a1 + a2) % p) * q2 + ((b1 + b2) % p) * p + (c1 + c2 + a1 * b2) % p
    return mul


def group_table(order, mul):
    """Multiplication table MT[x, y] = x*y (identity index 0) and the inverse array."""
    MT = np.empty((order, order), dtype=np.int64)
    for x in range(order):
        MT[x] = [mul(x, y) for y in range(order)]
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
    return MT, inv


def make_group(spec):
    if spec[0] == 'sd':
        order, mul, _ = lib.semidirect_group(spec[1], spec[2], spec[3])
        return group_table(order, mul)
    if spec[0] == 'heis':
        p = spec[1]
        return group_table(p ** 3, heis_mul(p))
    G = spec[1]
    return group_table(G, lambda x, y: (x + y) % G)


def specs_for(G):
    """Up to two non-abelian metacyclic groups of order G, a Heisenberg group if applicable, else cyclic."""
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
    picked = sd[::max(1, len(sd) // 2)][:2]
    p = round(G ** (1.0 / 3.0))
    if p >= 2 and p ** 3 == G and lib.is_prime_power(p):
        picked.append(('heis', p))
    if not picked:
        picked = [('cyc', G)]
    return picked


# ----------------------------------------------------------------------------- lifts

def build_nb(MT, inv, k, sig, V):
    """Neighbour table (2kG x 6). A(i,x) = i*G+x, B(j,y) = (k+j)*G+y. Dart (t,i) joins A(i,x) to B(sig[t,i], x*g)."""
    G = MT.shape[0]
    nb = np.empty((2 * k * G, DEG), dtype=np.int64)
    for t in range(DEG):
        for i in range(k):
            j = int(sig[t, i])
            g = int(V[t, i])
            nb[i * G:(i + 1) * G, t] = (k + j) * G + MT[:, g]
            nb[(k + j) * G:(k + j + 1) * G, t] = i * G + MT[:, int(inv[g])]
    return nb


def sheet_cost(nb, G, k):
    """Total number of vertices missed within distance 5 over the 2k identity sheets. 0 means diameter <= 5."""
    n = nb.shape[0]
    total = 0
    for u in range(2 * k):
        src = u * G
        seen = np.zeros(n, dtype=bool)
        seen[src] = True
        front = np.array([src], dtype=np.int64)
        for _ in range(DIAM):
            nxt = nb[front].ravel()
            nxt = np.unique(nxt[~seen[nxt]])
            if nxt.size == 0:
                break
            seen[nxt] = True
            front = nxt
        total += n - int(seen.sum())
    return total


def edges_from(nb):
    n = nb.shape[0]
    a = np.repeat(np.arange(n, dtype=np.int64), nb.shape[1])
    b = nb.ravel()
    keys = np.unique(np.minimum(a, b) * n + np.maximum(a, b))
    lo = (keys // n).tolist()
    hi = (keys % n).tolist()
    return n, [(int(x), int(y)) for x, y in zip(lo, hi) if x != y]


def search_job(MT, inv, k, rng, deadline):
    """Anneal permutations and voltages until cost 0 (return (sig, V)) or the deadline (return None)."""
    G = MT.shape[0]
    sig = np.array([rng.permutation(k) for _ in range(DEG)], dtype=np.int64)
    V = rng.integers(0, G, size=(DEG, k), dtype=np.int64)

    def cost():
        return sheet_cost(build_nb(MT, inv, k, sig, V), G, k)

    cur = cost()
    best, since = cur, 0
    while cur > 0 and time.monotonic() < deadline:
        if k > 1 and rng.random() < 0.3:
            t = int(rng.integers(DEG))
            i, i2 = (int(x) for x in rng.choice(k, 2, replace=False))
            sig[t, i], sig[t, i2] = sig[t, i2], sig[t, i]
            c = cost()
            if c <= cur or rng.random() < math.exp(-(c - cur) / TEMP):
                cur = c
            else:
                sig[t, i], sig[t, i2] = sig[t, i2], sig[t, i]
        else:
            t = int(rng.integers(DEG))
            i = int(rng.integers(k))
            new = int(rng.integers(G))
            old = int(V[t, i])
            if new == old:
                continue
            V[t, i] = new
            c = cost()
            if c <= cur or rng.random() < math.exp(-(c - cur) / TEMP):
                cur = c
            else:
                V[t, i] = old
        if cur < best:
            best, since = cur, 0
        else:
            since += 1
        if since > PATIENCE and cur > 0:
            sig = np.array([rng.permutation(k) for _ in range(DEG)], dtype=np.int64)
            V = rng.integers(0, G, size=(DEG, k), dtype=np.int64)
            cur = cost()
            best, since = cur, 0
    if cur == 0:
        return sig.copy(), V.copy()
    return None


def make_jobs():
    """(vertex count, k, group spec) with 2kG just above the record, smallest first."""
    jobs = []
    for k in range(1, 7):
        g_lo = -(-(RECORD + 2) // (2 * k))
        for G in (g_lo, g_lo + 1):
            for spec in specs_for(G):
                jobs.append((2 * k * G, k, spec))
    jobs.sort(key=lambda j: (j[0], j[1]))
    return jobs


# ----------------------------------------------------------------------------- fallbacks

def haar_fallback(d, D):
    MT, _ = make_group(FALLBACK_SPEC)
    N = MT.shape[0]
    edges = [(g, N + int(MT[s, g])) for s in FALLBACK_S for g in range(N)]
    edges = sorted(set(edges))
    if lib.is_valid(2 * N, edges, d, D):
        return 2 * N, edges
    return None


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
    budget = max(1.0, min(0.7 * time_limit, time_limit - 12.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)

    best = None
    try:
        jobs = make_jobs()
        cache = {}
        while time.monotonic() < deadline:
            searched = False
            for n_t, k, spec in jobs:
                if time.monotonic() >= deadline:
                    break
                if best is not None and n_t <= best[0]:
                    continue
                searched = True
                try:
                    if spec not in cache:
                        cache[spec] = make_group(spec)
                    MT, inv = cache[spec]
                    until = min(deadline, time.monotonic() + SLICE)
                    res = search_job(MT, inv, k, rng, until)
                    if res is None:
                        continue
                    sig, V = res
                    n, edges = edges_from(build_nb(MT, inv, k, sig, V))
                    if lib.is_valid(n, edges, d, D) and (best is None or n > best[0]):
                        best = (n, edges)
                except Exception:
                    continue
            if not searched:
                break
    except Exception:
        pass

    if best is not None:
        return best

    try:
        fb = haar_fallback(d, D)
        if fb is not None:
            return fb
    except Exception:
        pass
    return safe_small(d, D)
