"""Bold variant: for D >= 5, search bi-Cayley graphs over non-abelian groups
with a tabu search on connection sets, instead of voltage-lift annealing.

Construction: vertices A_x and B_y for x, y in a group G of order N.
Connection set S = {s_1..s_d} (distinct). Edges A_x -- B_{x*s} for x in G, s in S.
Left multiplication is an automorphism, so the diameter is <= D iff every vertex
is within distance D of A_e and of B_e. The cost counts unreached vertices from
those two sources, so cost 0 means a valid graph.

Fallbacks: K_{d,d} (diameter 2) and PG(2,q) incidence (diameter 3) are always
checked with lib.is_valid before being returned.
"""
import math
import random
import time

import numpy as np

import lib


_SAMPLES = 48     # random single-element moves evaluated per tabu step
_TENURE = 8       # steps a removed connection element stays forbidden
_STALL = 120      # steps without improvement before a partial kick


def _is_prime(p):
    if p < 2:
        return False
    i = 2
    while i * i <= p:
        if p % i == 0:
            return False
        i += 1
    return True


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _tables(spec, rng):
    """Return (M, inv) with M[x, y] = x*y for a group of order N, or None if the group fails checks."""
    try:
        if spec[0] == "aff":
            p = spec[1]
            N = p * (p - 1)
            X = np.arange(N, dtype=np.int64)
            U = X // p + 1
            Bc = X % p
            M = ((U[:, None] * U[None, :]) % p - 1) * p + (U[:, None] * Bc[None, :] + Bc[:, None]) % p
        else:
            _, m, k, r = spec
            N = m * k
            X = np.arange(N, dtype=np.int64)
            a = X // k
            b = X % k
            pw = np.array([pow(r, bb, m) for bb in range(k)], dtype=np.int64)
            M = ((a[:, None] + pw[b][:, None] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
        M = np.asarray(M, dtype=np.int64)
    except Exception:
        return None

    X = np.arange(N)
    if not (np.array_equal(M[0], X) and np.array_equal(M[:, 0], X)):
        return None
    inv = np.argmax(M == 0, axis=1)
    if not np.all(M[X, inv] == 0):
        return None
    for _ in range(300):
        x = rng.randrange(N)
        y = rng.randrange(N)
        z = rng.randrange(N)
        if M[M[x, y], z] != M[x, M[y, z]]:
            return None
    return M, inv


def _cost(M, inv, S, N, D):
    """Unreached (vertex) count from A_e (node 0) and B_e (node N) within D steps. Zero means valid."""
    Sa = np.asarray(S, dtype=np.int64)
    iS = inv[Sa]
    adj = np.vstack([N + M[:, Sa], M[:, iS]])
    tot = 0
    for src in (0, N):
        seen = np.zeros(2 * N, dtype=bool)
        seen[src] = True
        frontier = np.array([src], dtype=np.int64)
        for _ in range(D):
            nb = adj[frontier].ravel()
            nb = nb[~seen[nb]]
            if nb.size == 0:
                break
            nb = np.unique(nb)
            seen[nb] = True
            frontier = nb
        tot += 2 * N - int(seen.sum())
    return tot


def _tabu(M, inv, N, d, D, deadline, rng):
    """Tabu search over connection sets S (|S| = d) minimising the reach cost."""
    S = rng.sample(range(N), d)
    c = _cost(M, inv, S, N, D)
    best_c = c
    stall = 0
    tabu = {}
    step = 0
    while c != 0 and time.monotonic() < deadline:
        step += 1
        bm = None
        bv = None
        for _ in range(_SAMPLES):
            i = rng.randrange(d)
            x = rng.randrange(N)
            if x in S or tabu.get(x, -1) >= step:
                continue
            T = S[:]
            T[i] = x
            v = _cost(M, inv, T, N, D)
            if bv is None or v < bv or (v == bv and rng.random() < 0.5):
                bv, bm = v, (i, x)
        if bm is None:
            continue
        i, x = bm
        tabu[S[i]] = step + _TENURE
        S[i] = x
        c = bv
        if c < best_c:
            best_c = c
            stall = 0
        else:
            stall += 1
        if stall > _STALL and c != 0:
            for _ in range(2):
                i = rng.randrange(d)
                x = rng.randrange(N)
                while x in S:
                    x = rng.randrange(N)
                S[i] = x
            c = _cost(M, inv, S, N, D)
            best_c = c
            stall = 0
    return list(S) if c == 0 else None


def _edges(M, S, N):
    return [(x, N + int(M[x, s])) for x in range(N) for s in S]


def _specs(lo, hi, rng, cap=40):
    """Affine groups AGL(1,p) and semidirect products Z_m x| Z_k (k >= 2, r != 1), orders in [lo, hi]."""
    specs = []
    for p in range(3, hi + 2):
        o = p * (p - 1)
        if lo <= o <= hi and _is_prime(p):
            specs.append((o, ("aff", p)))
    for k in range(2, 13):
        for m in range(3, hi // k + 1):
            o = m * k
            if o < lo or o > hi:
                continue
            rs = [r for r in range(2, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1]
            if rs:
                specs.append((o, ("sd", m, k, rs[rng.randrange(len(rs))])))
    specs.sort(key=lambda t: (t[0], rng.random()))
    return specs[:cap]


def _bicayley_phase(d, D, deadline, rng, state, consider):
    """Round-based search: per round, groups are tried in increasing order with growing budgets."""
    moore_half = lib.moore_bound(d, D) // 2
    budget = 0.8
    while time.monotonic() < deadline:
        lo = max(state["n"] // 2 + 1, int(0.4 * moore_half))
        hi = lo + 80
        specs = _specs(lo, hi, rng)
        if not specs:
            break
        for o, spec in specs:
            if time.monotonic() >= deadline:
                return
            if o <= state["n"] // 2:
                continue
            tables = _tables(spec, rng)
            if tables is None:
                continue
            M, inv = tables
            sub = min(deadline, time.monotonic() + budget)
            S = _tabu(M, inv, o, d, D, sub, rng)
            if S is not None:
                consider(2 * o, _edges(M, S, o))
        budget = min(budget * 2, 6.4)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    rng = random.Random(seed)

    # Safe fallback: K_{d,d}, diameter 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    state = {"n": best_n, "e": best_e}

    def consider(n, e):
        if n > state["n"] and lib.is_valid(n, e, d, D):
            state["n"], state["e"] = n, e
            return True
        return False

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if D >= 5 and d >= 3:
        _bicayley_phase(d, D, deadline, rng, state, consider)

    n, e = state["n"], state["e"]
    if not lib.is_valid(n, e, d, D):
        return lib.haar_graph(d, range(d))
    return n, e
