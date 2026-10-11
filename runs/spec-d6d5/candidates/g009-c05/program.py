import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Known algebraic baselines: projective plane incidence and Araujo-Pardo-Lopez.
# ----------------------------------------------------------------------------

def _pg_baseline(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo_baseline(d):
    """Araujo-Pardo-Lopez graph for d = q + 2 with q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        return lib.araujo_lopez_graph(q)
    return None


# ----------------------------------------------------------------------------
# New family: bi-Cayley graphs Bi(G, S) over a non-abelian group G.
#
# Vertices: (g, 0) -> index g, and (h, 1) -> index N + h.
# Edges: (g, 0) ~ (g*s, 1) for every g in G and s in S, |S| = d.
#
# Left multiplication by G is an automorphism that is transitive on each side,
# so the diameter is at most D iff every vertex lies within distance D of the
# two representatives (e, 0) and (e, 1). Each evaluation is therefore two BFS
# runs, which keeps the annealing cheap.
#
# Groups: semidirect products Z_m x| Z_k (via lib.semidirect_group), and the
# Heisenberg group over F_p when the order is p^3.
# ----------------------------------------------------------------------------

def _is_prime(p):
    return p >= 2 and all(p % q for q in range(2, int(p ** 0.5) + 1))


def _group_specs(N, rng):
    """Candidate group descriptions of order N, shuffled."""
    specs = []
    for k in range(2, N):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        rs = [r for r in range(2, m)
              if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if not rs:
            continue
        rng.shuffle(rs)
        for r in rs[:3]:
            specs.append(("sd", m, k, r))
    p = round(N ** (1.0 / 3.0))
    for q in (p - 1, p, p + 1):
        if q >= 3 and q ** 3 == N and _is_prime(q):
            specs.append(("heis", q))
    rng.shuffle(specs)
    return specs


def _build_group(spec):
    """Return (N, M, Mc, inv): multiplication table M, its transpose Mc, and inverses.

    Identity is index 0 in every encoding used here.
    """
    if spec[0] == "sd":
        _, m, k, r = spec
        N, mul, _ = lib.semidirect_group(m, k, r)
    else:
        p = spec[1]
        pp = p * p
        N = p ** 3

        def mul(x, y):
            a, rem = divmod(x, pp)
            b, c = divmod(rem, p)
            a2, rem2 = divmod(y, pp)
            b2, c2 = divmod(rem2, p)
            return ((a + a2) % p) * pp + ((b + b2) % p) * p + (c + c2 + a * b2) % p

    M = [[mul(x, y) for y in range(N)] for x in range(N)]
    inv = [row.index(0) for row in M]
    Mc = [[M[g][s] for g in range(N)] for s in range(N)]
    return N, M, Mc, inv


def _cost(S, grp, D):
    """Vertices not within distance D of (e,0) or (e,1). Zero means diameter <= D."""
    N, M, Mc, inv = grp
    tot = 2 * N
    invS = [inv[s] for s in S]
    cols = [Mc[s] for s in S]
    total = 0
    for src in (0, N):
        seen = bytearray(tot)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < N:
                    for c in cols:
                        v = N + c[u]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    row = M[u - N]
                    for t in invS:
                        v = row[t]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            if not nxt:
                break
            cnt += len(nxt)
            frontier = nxt
        total += tot - cnt
    return total


def _anneal(grp, d, D, rng, deadline):
    """Simulated annealing over S (|S| = d). Returns S with cost 0, or None."""
    N = grp[0]
    if N <= d:
        return None
    S = rng.sample(range(N), d)
    c = _cost(S, grp, D)
    T = 2.0
    while c > 0 and time.monotonic() < deadline:
        i = rng.randrange(d)
        x = rng.randrange(N)
        if x in S:
            continue
        old = S[i]
        S[i] = x
        c2 = _cost(S, grp, D)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
            c = c2
        else:
            S[i] = old
        T = max(0.05, T * 0.998)
    return list(S) if c == 0 else None


def _edges(grp, S):
    N, M, _, _ = grp
    edges = [(g, N + M[g][s]) for g in range(N) for s in S]
    return 2 * N, edges


def _cayley_search(d, D, rng, deadline, state, consider):
    """Search bi-Cayley graphs over groups of increasing order N, with N in [N_start, moore/2]."""
    moore = lib._moore_bound(d, D)
    nmax = moore // 2
    N = max(state["best"][0] // 2 + 1, int(0.4 * nmax), 2)
    per_N = 3.0
    while N <= nmax and time.monotonic() < deadline:
        budget_end = min(deadline, time.monotonic() + per_N)
        for spec in _group_specs(N, rng):
            if time.monotonic() >= budget_end:
                break
            try:
                grp = _build_group(spec)
            except (ValueError, IndexError):
                continue
            S = _anneal(grp, d, D, rng, budget_end)
            if S is not None:
                n, e = _edges(grp, S)
                if consider(n, e):
                    break
        N += 1


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, 0.85 * time_limit - 1.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    state = {"best": lib.haar_graph(d, range(d))}

    def consider(n, e):
        """Accept (n, e) if it is valid and larger than the current best."""
        if n > state["best"][0] and lib.is_valid(n, e, d, D):
            state["best"] = (n, e)
            return True
        return False

    if D >= 3:
        try:
            pg = _pg_baseline(d)
            if pg is not None:
                consider(pg[0], pg[1])
        except Exception:
            pass
        try:
            ar = _araujo_baseline(d)
            if ar is not None:
                consider(ar[0], ar[1])
        except Exception:
            pass

    try:
        _cayley_search(d, D, rng, deadline, state, consider)
    except Exception:
        pass

    best = state["best"]
    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
