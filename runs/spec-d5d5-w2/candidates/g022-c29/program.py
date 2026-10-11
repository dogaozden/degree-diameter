import math
import random
import time

import lib

# ----------------------------------------------------------------------------
# NEW CONSTRUCTION: bi-Cayley lifts over arbitrary finite groups, annealed.
#
# A bi-Cayley graph over a group G with connection set S (|S| = d) has
# vertices A_x and B_x for x in G, and edges A_x ~ B_{x*g} for g in S.
# It is d-regular and bipartite. Left multiplication is an automorphism, so
# diameter <= D holds iff every vertex is within D of A_e and of B_e.
#
# The group is given either by a permutation closure (PSL(2,7), PGL(2,7),
# which are non-metacyclic and so outside the semidirect family) or by the
# semidirect products Z_m x| Z_k. Search runs simulated annealing on S, with
# cost = number of unreached (source, target) pairs from A_e and B_e.
# ----------------------------------------------------------------------------

_CAP = 400          # largest group order we tabulate
_PERM_CACHE = {}


def _compose(p, q):
    """(p o q)(i) = p(q(i)) on tuples."""
    return tuple(p[i] for i in q)


def _finish(N, M):
    """Attach inverse table to a multiplication table with identity 0."""
    invs = [row.index(0) for row in M]
    return N, M, invs


def _perm_group_tables(gens):
    """Closure of permutation generators; returns (N, M, invs) or None if too big."""
    ident = tuple(range(len(gens[0])))
    els = [ident]
    idx = {ident: 0}
    i = 0
    while i < len(els):
        x = els[i]
        i += 1
        for g in gens:
            y = _compose(g, x)
            if y not in idx:
                if len(els) >= _CAP:
                    return None
                idx[y] = len(els)
                els.append(y)
    N = len(els)
    M = [[idx[_compose(els[a], els[b])] for b in range(N)] for a in range(N)]
    return _finish(N, M)


def _psl_gens():
    """PSL(2,7) acting on PG(1,7) = {0..6, inf=7}: x+1, 2x, -1/x."""
    t = tuple((x + 1) % 7 for x in range(7)) + (7,)
    m2 = tuple((2 * x) % 7 for x in range(7)) + (7,)
    s = tuple([7] + [(-pow(x, 5, 7)) % 7 for x in range(1, 7)] + [0])
    return [t, m2, s]


def _pgl_gens():
    """PGL(2,7): as PSL(2,7) but with x -> 3x (3 is a non-square mod 7)."""
    t = tuple((x + 1) % 7 for x in range(7)) + (7,)
    m3 = tuple((3 * x) % 7 for x in range(7)) + (7,)
    s = tuple([7] + [(-pow(x, 5, 7)) % 7 for x in range(1, 7)] + [0])
    return [t, m3, s]


def _perm_tables(name):
    if name not in _PERM_CACHE:
        gens = _psl_gens() if name == "psl" else _pgl_gens()
        _PERM_CACHE[name] = _perm_group_tables(gens)
    return _PERM_CACHE[name]


def _semidirect_tables(m, k, r):
    """Multiplication table of Z_m x|_r Z_k (identity code 0), built on demand."""
    N, mul, _ = lib.semidirect_group(m, k, r)
    M = [[mul(a, b) for b in range(N)] for a in range(N)]
    return _finish(N, M)


def _sd_params(N):
    """All semidirect parameters (m, k, r) with m*k = N and m >= 2."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _unreached(N, M, invs, S, D):
    """Pairs (source, target) with source in {A_e, B_e} not within distance D."""
    Sinv = [invs[g] for g in S]
    total = 0
    for src in (0, N):
        seen = bytearray(2 * N)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < N:
                    row = M[u]
                    for g in S:
                        v = N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    row = M[u - N]
                    for h in Sinv:
                        v = row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += 2 * N - count
    return total


def _anneal(N, M, invs, d, D, rng, iters, dl):
    """Simulated annealing over connection sets S of size d; None if no zero-cost S found."""
    S = rng.sample(range(N), d)
    cur = _unreached(N, M, invs, S, D)
    T0, T1 = 3.0, 0.2
    ratio = (T1 / T0) ** (1.0 / max(1, iters))
    T = T0
    for it in range(iters):
        if cur == 0:
            break
        if (it & 31) == 0 and time.monotonic() >= dl:
            return None
        T *= ratio
        i = rng.randrange(d)
        c = rng.randrange(N)
        if c in S:
            continue
        old = S[i]
        S[i] = c
        v = _unreached(N, M, invs, S, D)
        if v <= cur or rng.random() < math.exp((cur - v) / T):
            cur = v
        else:
            S[i] = old
    return list(S) if cur == 0 else None


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

ITERS = 2000        # annealing steps per attempt
ITERS_BIG = 3000    # for the largest group
SLOT = 2.5          # seconds per order N in the sweep


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best_n, best_e = lib.haar_graph(d, range(d))   # K_{d,d}, diameter 2
    if D == 2:
        return best_n, best_e

    moore = lib.moore_bound(d, D)
    rng = random.Random(seed)

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    # Projective-plane incidence for D = 3 (calibration case).
    if D == 3:
        for q in range(min(d - 1, 16), 1, -1):
            if lib.is_prime_power(q):
                n, e = lib.projective_plane_incidence(q)
                consider(n, e)
                break

    if best_n >= moore:
        return best_n, best_e

    def emit(N, M, S):
        edges = [(x, N + M[x][g]) for x in range(N) for g in S]
        consider(2 * N, edges)

    def run(N, M, invs, iters, dl, tries):
        for _ in range(tries):
            if time.monotonic() >= dl:
                return None
            S = _anneal(N, M, invs, d, D, rng, iters, dl)
            if S is not None:
                return S
        return None

    def usable(N):
        return N is not None and N >= d and 2 * N <= moore and 2 * N > best_n

    t_a = start + 0.25 * budget
    t_b = start + 0.75 * budget

    # Phase A: PSL(2,7) (order 168, 336 vertices = record order).
    tabs = _perm_tables("psl")
    if tabs is not None and usable(tabs[0]):
        N, M, invs = tabs
        S = run(N, M, invs, ITERS, t_a, 50)
        if S is not None:
            emit(N, M, S)

    # Phase B: sweep semidirect groups upward from the record order to beat it.
    NCAP = min(moore // 2, _CAP)
    N = max(d, best_n // 2 + 1)
    while N <= NCAP and time.monotonic() < t_b:
        if N * 2 <= best_n:
            N = best_n // 2 + 1
            continue
        params = _sd_params(N)
        rng.shuffle(params)
        slot_end = min(t_b, time.monotonic() + SLOT)
        for (m, k, r) in params[:4]:
            if time.monotonic() >= slot_end:
                break
            N2, M, invs = _semidirect_tables(m, k, r)
            S = run(N2, M, invs, ITERS, slot_end, 2)
            if S is not None:
                emit(N2, M, S)
                break
        N = max(N + 1, best_n // 2 + 1)

    # Phase C: PGL(2,7) (order 336, 672 vertices) with the remaining time.
    tabs = _perm_tables("pgl")
    if tabs is not None and usable(tabs[0]):
        N, M, invs = tabs
        S = run(N, M, invs, ITERS_BIG, deadline, 1000)
        if S is not None:
            emit(N, M, S)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, best_e
