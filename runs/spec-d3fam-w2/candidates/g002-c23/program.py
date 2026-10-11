import math
import random
import time

import lib


def _fallback(d, D):
    """Safe, verified-by-construction graphs used whenever the search fails."""
    if d <= 0 or D <= 0:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]
    if D == 2:
        return lib.haar_graph(d, range(d))          # K_{d,d}, diameter 2
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)  # Moore-extremal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            return lib.araujo_lopez_graph(d - 2)    # record construction
        except Exception:
            pass
    return lib.haar_graph(d, range(d))


# ------------------------------------------------------------------
# New construction: two-orbit group lifts.
#
# Base graph: A-side vertices a_0, a_1 and B-side vertices b_0, b_1, over a
# finite group G of order N. Block (i, j) carries a voltage set S_ij, and
# (a_i, x) is adjacent to (b_j, x*s) for each s in S_ij. Left multiplication
# is an automorphism that fixes each base vertex, so distances from the four
# representatives (a_i, e), (b_j, e) determine the diameter exactly.
#
# Degrees: block sizes are (k, d-k, d-k, k), so every vertex has degree d.
# Order is 4N, which beats the record when N > record/4.
# Search: simulated annealing over the voltage sets, minimising the number of
# (representative, vertex) pairs at distance > 3.
# ------------------------------------------------------------------

_T = 1.0
_SLICE = 60
_STALE_LIMIT = 1500


def _groups_of_order(N, rng):
    """Cyclic group of order N plus up to two semidirect products Z_m x| Z_k (r = 1 gives a direct product)."""
    out = [lib.cyclic_group(N)]
    cands = []
    for k in range(2, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        rs = [r for r in range(1, m)
              if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        rng.shuffle(rs)
        for r in rs[:2]:
            cands.append((m, k, r))
    rng.shuffle(cands)
    for m, k, r in cands[:2]:
        try:
            out.append(lib.semidirect_group(m, k, r))
        except ValueError:
            pass
    return out


def _adjacency(job):
    """Adjacency lists of the 4N-vertex lift for the job's current voltages."""
    N = job["N"]
    M = job["M"]
    adj = [[] for _ in range(4 * N)]
    for i, j, S in job["blocks"]:
        ab = i * N
        bb = (2 + j) * N
        for s in S:
            for x in range(N):
                a = ab + x
                b = bb + M[x][s]
                adj[a].append(b)
                adj[b].append(a)
    return adj


def _cost(adj, n, N):
    """Number of (representative, vertex) pairs at distance > 3, using bitmask balls of radius 3."""
    R = [1 << v for v in range(n)]
    for _ in range(3):
        nxt = []
        for v in range(n):
            r = R[v]
            for w in adj[v]:
                r |= R[w]
            nxt.append(r)
        R = nxt
    return sum(n - R[r].bit_count() for r in (0, N, 2 * N, 3 * N))


def _random_blocks(d, N, k, rng):
    sizes = [(0, 0, k), (0, 1, d - k), (1, 0, d - k), (1, 1, k)]
    return [[i, j, rng.sample(range(N), sz)] for i, j, sz in sizes]


def _new_job(d, N, grp, k, rng):
    _order, mul, _inv = grp
    M = [[mul(x, y) for y in range(N)] for x in range(N)]
    job = {"N": N, "M": M, "k": k, "stale": 0, "done": False}
    job["blocks"] = _random_blocks(d, N, k, rng)
    job["cur"] = _cost(_adjacency(job), 4 * N, N)
    job["best"] = job["cur"]
    return job


def _reinit(job, d, rng):
    job["blocks"] = _random_blocks(d, job["N"], job["k"], rng)
    job["cur"] = _cost(_adjacency(job), 4 * job["N"], job["N"])
    job["best"] = job["cur"]
    job["stale"] = 0


def _run(job, steps, d, rng, deadline):
    """Run up to `steps` annealing moves on one job."""
    N = job["N"]
    n = 4 * N
    for _ in range(steps):
        if job["cur"] == 0 or time.monotonic() > deadline:
            return
        S = job["blocks"][rng.randrange(4)][2]
        idx = rng.randrange(len(S))
        x = rng.randrange(N)
        if x in S:
            continue
        old = S[idx]
        S[idx] = x
        new = _cost(_adjacency(job), n, N)
        cur = job["cur"]
        if new <= cur or rng.random() < math.exp(-(new - cur) / _T):
            job["cur"] = new
            if new < job["best"]:
                job["best"] = new
                job["stale"] = 0
            else:
                job["stale"] += 1
        else:
            S[idx] = old
            job["stale"] += 1
        if job["stale"] > _STALE_LIMIT:
            _reinit(job, d, rng)


def _edges_of(job):
    N = job["N"]
    M = job["M"]
    edges = set()
    for i, j, S in job["blocks"]:
        for s in S:
            for x in range(N):
                edges.add((i * N + x, (2 + j) * N + M[x][s]))
    return sorted(edges)


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, min(0.8 * time_limit, time_limit - 6.0))
    rng = random.Random(seed)

    base_n, base_e = _fallback(d, D)
    if not lib.is_valid(base_n, base_e, d, D):
        return 1, []

    # Only the diameter-3 regime with non-Moore degree is searched.
    if D != 3 or d < 3 or lib.is_prime_power(d - 1):
        return base_n, base_e

    # Order 4N must exceed the current best.
    Nlo = base_n // 4 + 1
    # Same-side vertices lie within distance 2 of a vertex: 2N <= 1 + (d-1) + (d-1)^2.
    Nhi = (1 + (d - 1) + (d - 1) ** 2) // 2
    if Nlo > Nhi:
        return base_n, base_e

    ks = sorted(range(1, d), key=lambda k: (abs(2 * k - d), k))[:2]

    specs = []
    for N in range(Nlo, Nhi + 1):
        for grp in _groups_of_order(N, rng):
            for k in ks:
                if k <= N and d - k <= N:
                    specs.append((N, grp, k))

    active = []
    for N, grp, k in specs:
        if time.monotonic() > deadline:
            break
        active.append(_new_job(d, N, grp, k, rng))

    best = None
    best_n = base_n
    while active and time.monotonic() < deadline:
        for job in list(active):
            if time.monotonic() >= deadline:
                break
            if job["done"] or 4 * job["N"] <= best_n:
                job["done"] = True
                continue
            _run(job, _SLICE, d, rng, deadline)
            if job["cur"] == 0:
                job["done"] = True
                n = 4 * job["N"]
                edges = _edges_of(job)
                if n > best_n and lib.is_valid(n, edges, d, D):
                    best = (n, edges)
                    best_n = n
        active = [j for j in active if not j["done"] and 4 * j["N"] > best_n]

    if best is not None:
        return best
    return base_n, base_e
