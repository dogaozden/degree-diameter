"""Degree-6, diameter-5 target: Haar graphs over non-abelian groups with annealed connection sets.

Construction (a different family from the parent's voltage lifts): the Haar graph H(G, S) on two copies of a finite
group G, with A-vertex g adjacent to B-vertex s*g for each s in S, |S| = 6. It is bipartite, 6-regular, and has
2|G| vertices. Put X = S^-1 S and Y = S S^-1. Then:
  - A-A and B-B pairs are within distance 4 when X*X = G and Y*Y = G,
  - A-B pairs are within distance 5 because (Y*Y)*S = G whenever Y*Y = G.
So cost(S) = 2|G| - |X*X| - |Y*Y| is 0 exactly when the sufficient condition holds. Every candidate is still
verified with lib.is_valid before it is returned.

Search: groups of order 343..370 (343 is the smallest order giving more than the record 684 vertices). These are
non-abelian metacyclic groups plus Heisenberg mod 7. Each group keeps resumable annealing state, and time slices are
cycled round-robin. Groups that cannot beat the current best are skipped, and weak groups are pruned periodically.

Fallback: the parent's Haar graph over Z_33 x| Z_10 (660 vertices), then a small always-valid graph.
"""
import math
import time

import numpy as np

import lib

TARGET = (6, 5)
RECORD = 684
TEMP = 1.0            # annealing temperature in units of uncovered elements
PATIENCE = 3000       # steps without restart-local improvement before a restart
SLICE = 1.5           # seconds per group per round-robin turn
NMIN = RECORD // 2 + 1   # 343: smallest group order whose Haar graph beats 684 vertices
NMAX = 370
GROUPS_PER_ORDER = 2

FALLBACK_SPEC = (33, 10, 26)            # semidirect Z_33 x| Z_10, order 330
FALLBACK_S = [0, 179, 116, 180, 47, 306]


# ----------------------------------------------------------------------------- group tables

def semidirect_table(m, k, r):
    """Multiplication table of Z_m x|_r Z_k, element (a, b) coded as a*k+b; (a,b)(c,d) = (a + r^b c, b + d)."""
    N = m * k
    powers = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    x = np.arange(N, dtype=np.int64)
    a, b = x // k, x % k
    A = (a[:, None] + powers[b][:, None] * a[None, :]) % m
    B = (b[:, None] + b[None, :]) % k
    return A * k + B


def heis_table(p):
    """Multiplication table of the Heisenberg group mod p, element (a, b, c) coded as a*p^2+b*p+c."""
    N = p ** 3
    x = np.arange(N, dtype=np.int64)
    a = x // (p * p)
    b = (x // p) % p
    c = x % p
    A = (a[:, None] + a[None, :]) % p
    B = (b[:, None] + b[None, :]) % p
    C = (c[:, None] + c[None, :] + a[:, None] * b[None, :]) % p
    return A * p * p + B * p + C


def inverse_of(MT):
    """inv[x] is the element y with x*y = identity (index 0)."""
    return np.argmax(MT == 0, axis=1).astype(np.int64)


def build_table(spec):
    if spec[0] == 'sd':
        return semidirect_table(spec[1], spec[2], spec[3])
    return heis_table(spec[1])


def group_specs(N):
    """A few non-abelian candidate groups of order N (metacyclic, plus Heisenberg mod 7 at 343)."""
    specs = []
    for b in range(2, N):
        if N % b:
            continue
        a = N // b
        if a < 3:
            continue
        for r in range(2, a):
            if math.gcd(r, a) == 1 and pow(r, b, a) == 1:   # r != 1, so the action is nontrivial
                specs.append(('sd', a, b, r))
    picked = []
    if specs:
        step = max(1, len(specs) // GROUPS_PER_ORDER)
        picked = specs[::step][:GROUPS_PER_ORDER]
    if N == 343:
        picked.append(('heis', 7))
    return picked


def make_candidates():
    cands = []
    for N in range(NMIN, NMAX + 1):
        for spec in group_specs(N):
            cands.append({'N': N, 'spec': spec, 'MT': None, 'inv': None, 'S': None,
                          'cur': None, 'rbest': None, 'gbest': float('inf'),
                          'since': 0, 'dead': False})
    return cands


# ----------------------------------------------------------------------------- Haar search

def haar_cost(MT, inv, S):
    """2N - |(S^-1 S)^2| - |(S S^-1)^2|; zero means the Haar graph H(G, S) has diameter <= 5."""
    N = MT.shape[0]
    si = inv[S]
    X = MT[si[:, None], S[None, :]].ravel()
    Y = MT[X[:, None], X[None, :]].ravel()
    mark = np.zeros(N, dtype=bool)
    mark[Y] = True
    cA = int(mark.sum())
    Z = MT[S[:, None], si[None, :]].ravel()
    W = MT[Z[:, None], Z[None, :]].ravel()
    mark[:] = False
    mark[W] = True
    cB = int(mark.sum())
    return 2 * N - cA - cB


def restart(c, rng):
    N = c['N']
    others = rng.choice(np.arange(1, N), size=5, replace=False).astype(np.int64)
    S = np.concatenate([np.zeros(1, dtype=np.int64), others])   # WLOG 0 is in S
    cur = haar_cost(c['MT'], c['inv'], S)
    c['S'] = S
    c['cur'] = cur
    c['rbest'] = cur
    c['gbest'] = min(c['gbest'], cur)
    c['since'] = 0


def anneal_slice(c, rng, until):
    """Anneal the candidate's connection set until the deadline; return True once the cost reaches 0."""
    MT, inv, N = c['MT'], c['inv'], c['N']
    if c['S'] is None:
        restart(c, rng)
    S, cur = c['S'], c['cur']
    while cur > 0 and time.monotonic() < until:
        if rng.random() < 0.5:
            i, j = rng.integers(0, 6, size=2)
            new = int(MT[S[i], S[j]])          # product move: stays inside the group's closure
        else:
            new = int(rng.integers(1, N))
        if new == 0 or (S == new).any():
            continue
        k = int(rng.integers(1, 6))
        old = int(S[k])
        S[k] = new
        cand_cost = haar_cost(MT, inv, S)
        if cand_cost <= cur or rng.random() < math.exp(-(cand_cost - cur) / TEMP):
            cur = cand_cost
            c['gbest'] = min(c['gbest'], cur)
            if cur < c['rbest']:
                c['rbest'] = cur
                c['since'] = 0
            else:
                c['since'] += 1
        else:
            S[k] = old
            c['since'] += 1
        if c['since'] > PATIENCE and cur > 0:
            restart(c, rng)
            S, cur = c['S'], c['cur']
    c['cur'] = cur
    return cur == 0


def haar_graph(MT, S):
    """Haar graph: A-vertex g ~ B-vertex s*g for s in S; vertices are A = g, B = N + g."""
    N = MT.shape[0]
    edges = []
    for s in np.asarray(S).tolist():
        row = MT[s].tolist()
        edges.extend((g, N + row[g]) for g in range(N))
    return 2 * N, edges


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


def fallback_target(d, D):
    try:
        MT = semidirect_table(*FALLBACK_SPEC)
        n, edges = haar_graph(MT, np.array(FALLBACK_S, dtype=np.int64))
        if lib.is_valid(n, edges, d, D):
            return n, edges
    except Exception:
        pass
    return safe_small(d, D)


# ----------------------------------------------------------------------------- entry point

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return safe_small(d, D)

    t0 = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 8.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)

    cands = make_candidates()
    best = None
    best_n = 0
    rounds = 0

    while time.monotonic() < deadline:
        active = [c for c in cands if not c['dead'] and 2 * c['N'] > best_n]
        if not active:
            break
        for c in active:
            now = time.monotonic()
            if now >= deadline:
                break
            if c['dead'] or 2 * c['N'] <= best_n:
                continue
            try:
                if c['MT'] is None:
                    c['MT'] = build_table(c['spec'])
                    c['inv'] = inverse_of(c['MT'])
                done = anneal_slice(c, rng, min(deadline, now + SLICE))
            except Exception:
                c['dead'] = True
                continue
            if done:
                c['dead'] = True
                try:
                    n, edges = haar_graph(c['MT'], c['S'])
                    if n > best_n and lib.is_valid(n, edges, d, D):
                        best, best_n = (n, edges), n
                except Exception:
                    pass
        rounds += 1
        if rounds % 3 == 0:
            live = [c for c in cands if not c['dead'] and c['MT'] is not None]
            if len(live) > 8:
                live.sort(key=lambda c: c['gbest'])
                for c in live[len(live) // 2:]:
                    c['dead'] = True

    if best is not None:
        return best
    return fallback_target(d, D)
