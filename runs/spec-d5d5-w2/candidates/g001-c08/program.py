"""Cayley bipartite lifts over small groups, certified by two BFS runs.

Construction: for a finite group G of order N and a generator multiset S of size d,
the bipartite graph has parts A = G and B = G, with a_x adjacent to b_{x*g} for g in S.
Left multiplication is an automorphism that is transitive on each part, so the diameter
is at most D iff the BFS balls of radius D around a_e and b_e cover everything.
Search runs simulated annealing over S, minimising the number of uncovered vertices.
Groups are cyclic or semidirect products Z_m x| Z_k, and the order N grows adaptively.
"""
import math
import random
import time

import numpy as np

import lib


def _group_specs(N):
    """Cyclic group and all semidirect products Z_m x| Z_k (k >= 2, m >= 2) of order N."""
    specs = [("c", N)]
    for k in range(2, N):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1:
                specs.append(("s", m, k, r))
    return specs


def _tables(spec, N):
    """Right-multiplication permutations R[g][x] = x*g and inverse table I[g] = g^-1."""
    if spec[0] == "c":
        _, mul, inv = lib.cyclic_group(N)
    else:
        _, mul, inv = lib.semidirect_group(spec[1], spec[2], spec[3])
    R = [np.array([mul(x, g) for x in range(N)], dtype=np.int64) for g in range(N)]
    I = [inv(g) for g in range(N)]
    return R, I


def _bad(S, R, I, N, D):
    """Number of vertices NOT within distance D of a_e or of b_e (0 means diameter <= D)."""
    Sa = [R[g] for g in S]                 # A -> B moves: a_x -> b_{x g}
    Sb = [R[I[g]] for g in S]              # B -> A moves: b_y -> a_{y g^-1}
    total = 0
    for start in (0, 1):
        vis = [np.zeros(N, dtype=bool), np.zeros(N, dtype=bool)]
        vis[start][0] = True
        side = start
        front = np.zeros(1, dtype=np.int64)
        for _ in range(D):
            arrs = Sa if side == 0 else Sb
            idx = np.concatenate([a[front] for a in arrs])
            nside = 1 - side
            mask = np.zeros(N, dtype=bool)
            mask[idx] = True
            mask &= ~vis[nside]
            vis[nside] |= mask
            front = np.flatnonzero(mask)
            side = nside
            if front.size == 0:
                break
        total += 2 * N - int(vis[0].sum()) - int(vis[1].sum())
    return total


def _search(N, specs, d, D, rng, end, cache):
    """Simulated annealing over generator sets, restarting and resampling groups until end.

    Returns (S, R) for a zero-cost set S (diameter <= D), or None on timeout.
    """
    steps = 2500
    while time.monotonic() < end:
        spec = rng.choice(specs)
        if spec not in cache:
            cache[spec] = _tables(spec, N)
        R, I = cache[spec]
        S = rng.sample(range(N), d)
        c = _bad(S, R, I, N, D)
        T = 1.0
        for it in range(steps):
            if c == 0:
                return S, R
            if (it & 31) == 0 and time.monotonic() >= end:
                return None
            i = rng.randrange(d)
            e = rng.randrange(N)
            if e in S:
                continue
            S2 = S[:]
            S2[i] = e
            c2 = _bad(S2, R, I, N, D)
            delta = c2 - c
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                S, c = S2, c2
            T = max(0.3, T * 0.998)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if D <= 0 or d <= 0:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)

    budget = max(0.5 * time_limit, min(0.8 * time_limit, time_limit - 5.0))
    deadline = t0 + budget
    rng = random.Random(seed)

    # Baseline: K_{d,d} (Cayley graph of Z_d with S = all of Z_d), diameter 2.
    best_N = d
    best_edges = [(x, d + (x + g) % d) for x in range(d) for g in range(d)]

    # Each part of a valid graph has at most Moore/2 vertices.
    ub = lib.moore_bound(d, D) // 2
    target = best_N + max(1, (ub - best_N) // 2)

    while best_N < target <= ub:
        now = time.monotonic()
        remaining = deadline - now
        if remaining < 0.5:
            break
        slice_len = min(remaining, max(2.0, 0.12 * budget))
        end = now + slice_len
        N = target
        specs = _group_specs(N)
        res = _search(N, specs, d, D, rng, end, {})
        ok = False
        if res is not None:
            S, R = res
            edges = [(x, N + int(R[g][x])) for x in range(N) for g in S]
            if lib.is_valid(2 * N, edges, d, D):
                best_N, best_edges = N, edges
                ok = True
        if ok:
            target = best_N + max(1, (ub - best_N) // 2)
        else:
            target = best_N + max(1, (target - best_N) // 2)

    return 2 * best_N, best_edges
