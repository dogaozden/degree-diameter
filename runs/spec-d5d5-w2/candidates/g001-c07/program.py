import math
import random
import time

import lib

# Construction idea (new relative to the parent): bi-Cayley lifts over random
# NON-abelian groups Z_m x|_r Z_k with a random bipartite base multigraph.
#
# Base: s vertices on side A and s on side B, with d perfect matchings between
# them (each matching a random permutation). Every base vertex has degree d.
# Each base dart gets a random group voltage. Lifting over a group G of order N
# gives 2*s*N vertices, all of degree <= d and bipartite by construction.
#
# Search: for each part size s in {1, 2, 3} we climb the group order N. Each
# success raises N for that s, and a per-N attempt budget ends the climb. Any
# candidate larger than the current best is checked with lib.is_valid before it
# is accepted. Non-abelian groups avoid the short cycles that limit cyclic
# Haar lifts (the parent's approach).

_GROUP_CACHE = {}


def _groups(N):
    """All semidirect groups Z_m x|_r Z_k of order N = m*k, as (m, k, r). Cyclic ones (r = 1) included."""
    if N in _GROUP_CACHE:
        return _GROUP_CACHE[N]
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    _GROUP_CACHE[N] = out
    return out


def _random_lift(rng, s, d, m, k, r):
    """Random bi-Cayley-type lift: base 2s vertices, d random matchings, random voltages."""
    order, mul, _ = lib.semidirect_group(m, k, r)
    darts = []
    for _ in range(d):
        perm = list(range(s))
        rng.shuffle(perm)
        for i in range(s):
            darts.append((i, s + perm[i], rng.randrange(order)))
    return lib.group_lift(2 * s, darts, order, mul)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    q = d - 1
    if D == 3 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)

    best_n, best_edges = 0, None

    # Calibration-style fallback: complete bipartite K_{d,d} (valid for D >= 2).
    n0, e0 = lib.haar_graph(d, range(d))
    if lib.is_valid(n0, e0, d, D):
        best_n, best_edges = n0, e0

    # D = 3 with d-2 a prime power >= 3: Araujo-Pardo & Lopez record graph.
    if D == 3 and d >= 5 and lib.is_prime_power(d - 2):
        try:
            n, e = lib.araujo_lopez_graph(d - 2)
            if n > best_n and lib.is_valid(n, e, d, D):
                best_n, best_edges = n, e
        except Exception:
            pass

    moore = lib.moore_bound(d, D)
    LIMIT = 300  # failed attempts allowed at one group order before giving up

    states = {s: {"N": 2, "tries": 0, "alive": True} for s in (1, 2, 3)}

    while time.monotonic() < deadline and any(st["alive"] for st in states.values()):
        for s, st in states.items():
            if not st["alive"]:
                continue
            if time.monotonic() >= deadline:
                break
            N = max(st["N"], best_n // (2 * s) + 1)
            if N != st["N"]:
                st["N"] = N
                st["tries"] = 0
            if 2 * s * N > moore:
                st["alive"] = False
                continue

            m, k, r = rng.choice(_groups(N))
            n, edges = _random_lift(rng, s, d, m, k, r)
            st["tries"] += 1

            if n > best_n and lib.is_valid(n, edges, d, D):
                best_n, best_edges = n, edges
                st["N"] = N + 1
                st["tries"] = 0
            elif st["tries"] >= LIMIT:
                st["alive"] = False

    if best_edges is None:
        return 1, []
    return best_n, best_edges
