"""Degree-6, diameter-5 target: Haar-graph search over non-abelian groups.

Construction: for a finite group G of order N and a 6-element set S, the Haar graph has vertices A_g and B_g (g in G)
and edges A_g ~ B_{s*g} for s in S. It is bipartite, 6-regular, and has 2N vertices.

Left multiplication by G is an automorphism, so the diameter is at most 5 iff
    (S^-1 S)^2 = G   (A-A distances up to 4)   and   (S S^-1)^2 = G   (B-B distances up to 4).
The A-B condition S(S^-1 S)^2 = G follows from the second one. So cost(S) = missing(A) + missing(B) counts uncovered
group elements, and cost 0 means the graph is valid. Each candidate is still checked with lib.is_valid before it
is returned.

To beat the record (684 vertices) we need N >= 343. The search runs annealing with K candidate single-slot
replacements per step, round-robin over several groups of order 343..360 (Heisenberg mod 7 first). Once a group
yields a valid graph, only strictly larger groups keep being searched. If nothing is found, a valid Haar graph of
order 330 (660 vertices) is returned, and a tiny always-valid graph backs that up.
"""
import math
import time

import numpy as np

import lib

TARGET = (6, 5)
RECORD = 684
K_MOVES = 4         # candidate single-slot replacements per annealing step (best one is kept)
TEMP = 0.5          # Metropolis temperature in units of uncovered elements
PATIENCE = 2000     # steps without improvement before a random restart
CHUNK = 150         # steps per group per round-robin turn
MAX_GROUPS = 16
LO_N, HI_N = 343, 360   # group orders giving 2N > RECORD, plus a few above

FALLBACK_SPEC = ('sd', 33, 10, 26)      # semidirect Z_33 x| Z_10, order 330
FALLBACK_S = [0, 179, 116, 180, 47, 306]


# ----------------------------------------------------------------------------- groups

def group_table(order, mul):
    """Multiplication table MT[x, y] = mul(x, y) (identity is index 0) and the inverse array."""
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


def build_group(spec):
    """Return (MT, inv) for a group spec."""
    if spec[0] == 'heis':
        p = spec[1]
        return group_table(p ** 3, heis_mul(p))
    _, m, k, r = spec
    order, mul, _ = lib.semidirect_group(m, k, r)
    return group_table(order, mul)


def candidate_specs(lo, hi, cap):
    """Heisenberg groups and a few metacyclic semidirect groups for each order in [lo, hi], smallest orders first."""
    specs = []
    for N in range(lo, hi + 1):
        p = round(N ** (1.0 / 3.0))
        if p >= 2 and p ** 3 == N and lib.is_prime_power(p):
            specs.append(('heis', p))
        cands = []
        for k in range(2, N):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            for r in range(2, m):
                if math.gcd(r, m) == 1 and pow(r, k, m) == 1:
                    cands.append(('sd', m, k, r))
        if cands:
            step = max(1, len(cands) // 2)
            specs.extend(cands[::step][:2])
    return specs[:cap]


# ----------------------------------------------------------------------------- Haar search

def cost(MT, inv, S):
    """Uncovered elements: N - |(S^-1 S)^2| plus N - |(S S^-1)^2|. Zero means diameter <= 5."""
    N = MT.shape[0]
    Si = inv[S]
    a = np.unique(MT[Si[:, None], S[None, :]].ravel())
    c1 = N - np.unique(MT[a[:, None], a[None, :]].ravel()).size
    b = np.unique(MT[S[:, None], Si[None, :]].ravel())
    c2 = N - np.unique(MT[b[:, None], b[None, :]].ravel()).size
    return int(c1 + c2)


def step(st, rng):
    """One annealing step: try K random single-slot replacements, keep the best, accept by Metropolis."""
    MT, inv, S, N = st['MT'], st['inv'], st['S'], st['N']
    best_c, best_T = None, None
    for _ in range(K_MOVES):
        i = int(rng.integers(6))
        x = int(rng.integers(N))
        if np.any(S == x):
            continue
        T = S.copy()
        T[i] = x
        c = cost(MT, inv, T)
        if best_c is None or c < best_c:
            best_c, best_T = c, T
    if best_T is None:
        return
    cur = st['cur']
    if best_c <= cur or rng.random() < math.exp(-(best_c - cur) / TEMP):
        st['S'], st['cur'] = best_T, best_c
        if best_c < st['best']:
            st['best'], st['since'] = best_c, 0
        else:
            st['since'] += 1
    else:
        st['since'] += 1
    if st['since'] > PATIENCE:
        S2 = rng.choice(N, size=6, replace=False).astype(np.int64)
        st['S'] = S2
        st['cur'] = cost(MT, inv, S2)
        st['best'] = st['cur']
        st['since'] = 0


def haar_edges(MT, S):
    """Haar graph: A-vertex g ~ B-vertex s*g for s in S. A-vertex g is g, B-vertex g is N + g. Returns (2N, edges)."""
    N = MT.shape[0]
    edges = []
    for s in S.tolist():
        row = MT[s].tolist()
        edges.extend((g, N + row[g]) for g in range(N))
    return 2 * N, edges


def verify(MT, S, d, D):
    """Return (n, edges) if the Haar graph passes lib.is_valid, else None."""
    try:
        n, edges = haar_edges(MT, S)
        if lib.is_valid(n, edges, d, D):
            return n, edges
    except Exception:
        pass
    return None


# ----------------------------------------------------------------------------- fallbacks

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

    best = None  # (n, edges) of the largest valid graph found so far

    states = []
    for spec in candidate_specs(LO_N, HI_N, MAX_GROUPS):
        if time.monotonic() >= deadline:
            break
        try:
            MT, inv = build_group(spec)
            N = MT.shape[0]
            S = rng.choice(N, size=6, replace=False).astype(np.int64)
            c = cost(MT, inv, S)
            states.append({'N': N, 'MT': MT, 'inv': inv, 'S': S,
                           'cur': c, 'best': c, 'since': 0})
        except Exception:
            continue

    while states and time.monotonic() < deadline:
        for st in list(states):
            if best is not None and 2 * st['N'] <= best[0]:
                states.remove(st)
                continue
            for _ in range(CHUNK):
                if st['cur'] == 0:
                    break
                step(st, rng)
            if st['cur'] == 0:
                res = verify(st['MT'], st['S'], d, D)
                states.remove(st)
                if res is not None and (best is None or res[0] > best[0]):
                    best = res
            if time.monotonic() >= deadline:
                break

    if best is not None:
        return best

    try:
        MT, _ = build_group(FALLBACK_SPEC)
        res = verify(MT, np.array(FALLBACK_S, dtype=np.int64), d, D)
        if res is not None:
            return res
    except Exception:
        pass
    return safe_small(d, D)
