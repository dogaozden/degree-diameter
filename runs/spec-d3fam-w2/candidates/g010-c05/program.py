import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe fallbacks: Araujo-Pardo/Lopez record family, projective plane incidence,
# and K_{d,d}.
#
# Bi-Cayley search (D = 3 target): a_x ~ b_{x s} for s in S, |S| = d, 1 in S.
# Same-side distance 2 needs BOTH covers:
#   cover1 = S S^-1 (a-side pairs), cover2 = S^-1 S (b-side pairs).
# For abelian groups these coincide; for non-abelian groups both are needed.
# The search counts uncovered elements in both covers jointly, so it no longer
# proposes sets that only work by accident on abelian groups.
# Groups: cyclic, abelian Z_a x Z_b (non-cyclic), and semidirect Z_a x| Z_k.
# ----------------------------------------------------------------------------


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _bump(c, y, sign):
    """Change cover count c[y] by sign; return the change in number of uncovered elements."""
    if sign > 0:
        c[y] += 1
        return -1 if c[y] == 1 else 0
    c[y] -= 1
    return 1 if c[y] == 0 else 0


def _delta(c1, c2, S, skip, v, sign, Q, R):
    """Add (sign>0) or remove (sign<0) element v against every S[j], j != skip, in both covers.

    Returns the change in the total number of uncovered non-identity elements.
    """
    change = 0
    for j, b in enumerate(S):
        if j == skip:
            continue
        change += _bump(c1, Q[v][b], sign)
        change += _bump(c1, Q[b][v], sign)
        change += _bump(c2, R[v][b], sign)
        change += _bump(c2, R[b][v], sign)
    return change


def _anneal(N, d, Q, R, rng, deadline, moves):
    """Find S (size d, containing identity 0) covering G in both covers; None on failure or timeout."""
    S = [0] + rng.sample(range(1, N), d - 1)
    c1 = [0] * N
    c2 = [0] * N
    unc = 2 * (N - 1)
    T = []
    for s in S:
        unc += _delta(c1, c2, T, -1, s, 1, Q, R)
        T.append(s)
    if unc == 0:
        return S
    for it in range(moves):
        if (it & 255) == 0 and time.monotonic() >= deadline:
            return None
        temp = 0.5 * (0.02 ** (it / moves))
        idx = rng.randrange(1, d)
        x = rng.randrange(1, N)
        if x in S:
            continue
        old = S[idx]
        delta = _delta(c1, c2, S, idx, old, -1, Q, R) + _delta(c1, c2, S, idx, x, 1, Q, R)
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            S[idx] = x
            unc += delta
            if unc == 0:
                return S
        else:
            _delta(c1, c2, S, idx, x, -1, Q, R)
            _delta(c1, c2, S, idx, old, 1, Q, R)
    return None


def _specs(N, rng, cap=40):
    """Candidate groups of order N: cyclic, abelian Z_a x Z_b (a | b), and sampled semidirect products."""
    cyc = [("cyc",)]
    ab = []
    for a in range(2, N + 1):
        if N % a == 0:
            b = N // a
            if b >= a and b % a == 0:
                ab.append(("ab", a, b))
    sd = []
    for k in range(2, N + 1):
        if N % k:
            continue
        a = N // k
        if a == 1:
            continue
        for r in range(1, a):
            if math.gcd(r, a) == 1 and pow(r, k, a) == 1:
                sd.append(("sd", a, k, r))
    rng.shuffle(sd)
    specs = cyc + ab + sd[:cap]
    rng.shuffle(specs)
    return specs


def _group(spec, N):
    """Return (M, Q, R): M[x][y] = x*y, Q[x][y] = x*y^-1, R[x][y] = x^-1*y."""
    if spec[0] == "cyc":
        _, mul, inv = lib.cyclic_group(N)
    elif spec[0] == "ab":
        _, a, b = spec

        def mul(x, y):
            x1, y1 = divmod(x, b)
            x2, y2 = divmod(y, b)
            return ((x1 + x2) % a) * b + (y1 + y2) % b

        def inv(x):
            x1, y1 = divmod(x, b)
            return ((-x1) % a) * b + (-y1) % b
    else:
        _, a, k, r = spec
        _, mul, inv = lib.semidirect_group(a, k, r)
    M = [[mul(x, y) for y in range(N)] for x in range(N)]
    I = [inv(x) for x in range(N)]
    Q = [[M[x][I[y]] for y in range(N)] for x in range(N)]
    R = [[M[I[x]][y] for y in range(N)] for x in range(N)]
    return M, Q, R


def _search_N(N, d, rng, deadline):
    """Search for a valid S over several groups of order N before the deadline. Returns (S, M) or None."""
    specs = _specs(N, rng)
    cache = {}
    rounds = 0
    while time.monotonic() < deadline and specs:
        spec = specs[rounds % len(specs)]
        rounds += 1
        if spec not in cache:
            try:
                cache[spec] = _group(spec, N)
            except Exception:
                cache[spec] = None
        tab = cache[spec]
        if tab is None:
            continue
        M, Q, R = tab
        S = _anneal(N, d, Q, R, rng, deadline, 40000)
        if S is not None:
            return S, M
    return None


def _edges_from(N, S, M):
    """Bi-Cayley edges: a_x = x joins b_y = N + x*s for s in S."""
    return [(x, N + M[x][s]) for x in range(N) for s in S]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.7 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    if D < 3 or d < 2:
        return best

    try:
        # Known record family for d = q + 2, q a prime power.
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                n_a, e_a = lib.araujo_lopez_graph(d - 2)
                if n_a > best[0] and lib.is_valid(n_a, e_a, d, D):
                    best = (n_a, e_a)
            except Exception:
                pass
        pg = _best_pg(d)
        if pg is not None and pg[0] > best[0] and lib.is_valid(pg[0], pg[1], d, D):
            best = pg

        # Bi-Cayley search over a wider family of groups, aiming above the current best.
        max_N = d * (d - 1) + 1
        N = best[0] // 2 + 1
        while N <= max_N and N >= d and time.monotonic() < deadline:
            rem = deadline - time.monotonic()
            res = _search_N(N, d, rng, time.monotonic() + 0.6 * rem)
            if res is None:
                break
            S, M = res
            n, e = 2 * N, _edges_from(N, S, M)
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
            N += 1
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
