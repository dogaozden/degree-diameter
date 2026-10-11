import math
import random
import time

import lib

ITERS = 800          # annealing steps per (group, order) attempt
T_HOT = 2.0          # initial temperature (in unreached-pair units)
T_COLD = 0.1         # final temperature
PENALTY = 10 ** 6    # cost per duplicate dart (would create a repeated edge)
MAX_GROUPS = 8       # groups tried per attempt
_TABLES = {}         # cache of group multiplication tables


# ----------------------------------------------------------------------------
# Groups: semidirect products Z_m x|_r Z_k of order N = m*k.
# ----------------------------------------------------------------------------

def _groups(N):
    """Return all semidirect parameters (m, k, r) with m*k = N."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _tables(m, k, r):
    """Return (order, mul_table, inv_list) for the group, cached. Identity is element 0."""
    key = (m, k, r)
    if key in _TABLES:
        return _TABLES[key]
    if len(_TABLES) > 60:
        _TABLES.clear()
    order, mul, inv = lib.semidirect_group(m, k, r)
    M = [[mul(x, g) for g in range(order)] for x in range(order)]
    I = [inv(g) for g in range(order)]
    _TABLES[key] = (order, M, I)
    return _TABLES[key]


# ----------------------------------------------------------------------------
# Multi-orbit bi-regular lifts.
#
# Base graph: s vertices A_0..A_{s-1} and s vertices B_0..B_{s-1}. Each base
# layer t (t = 0..d-1) is a permutation sig[t] giving the dart A_i -> B_{sig[t][i]}
# with voltage volt[t][i] in G. Every base vertex then has base degree d.
#
# Lift: A_{i,x} is adjacent to B_{j,x*g} for each dart (i, j, g). Left
# multiplication by G is an automorphism, so eccentricities from the 2s base
# sources (A_{i,e}, B_{j,e}) decide the diameter. Each lifted vertex has degree d,
# and the graph is bipartite by construction.
# ----------------------------------------------------------------------------

def _cost(N, s, d, D, M, I, sig, volt):
    """Number of (source, vertex) pairs not within distance D, plus duplicate penalties."""
    out = [[] for _ in range(s)]
    inn = [[] for _ in range(s)]
    for t in range(d):
        st, vt = sig[t], volt[t]
        for i in range(s):
            j, g = st[i], vt[i]
            out[i].append((j, g))
            inn[j].append((i, I[g]))
    dup = 0
    for i in range(s):
        dup += len(out[i]) - len(set(out[i]))
    if dup:
        return PENALTY * dup

    sN = s * N
    V = 2 * sN
    sources = [i * N for i in range(s)] + [sN + j * N for j in range(s)]
    total = 0
    for src in sources:
        seen = bytearray(V)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < sN:
                    i, x = divmod(u, N)
                    Mx = M[x]
                    for j, g in out[i]:
                        v = sN + j * N + Mx[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - sN, N)
                    My = M[y]
                    for i, ig in inn[j]:
                        v = i * N + My[ig]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += V - count
    return total


def _anneal(N, s, d, D, M, I, rng, deadline):
    """Simulated annealing over the dart layers and voltages. Returns (sig, volt) or None."""
    sig = []
    for _ in range(d):
        p = list(range(s))
        rng.shuffle(p)
        sig.append(p)
    volt = [[rng.randrange(N) for _ in range(s)] for _ in range(d)]
    cur = _cost(N, s, d, D, M, I, sig, volt)
    for it in range(ITERS):
        if cur == 0:
            break
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / ITERS)
        t = rng.randrange(d)
        if s == 1 or rng.random() < 0.8:
            i = rng.randrange(s)
            old = volt[t][i]
            new = rng.randrange(N)
            if new == old:
                continue
            volt[t][i] = new
            v = _cost(N, s, d, D, M, I, sig, volt)
            if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
                cur = v
            else:
                volt[t][i] = old
        else:
            i, i2 = rng.sample(range(s), 2)
            st = sig[t]
            st[i], st[i2] = st[i2], st[i]
            v = _cost(N, s, d, D, M, I, sig, volt)
            if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
                cur = v
            else:
                st[i], st[i2] = st[i2], st[i]
    if cur == 0:
        return sig, volt
    return None


def _attempt(N, s, d, D, rng, deadline):
    """Try several groups of order N for a lift with s base vertices per side."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() >= deadline:
            return None
        order, M, I = _tables(m, k, r)
        res = _anneal(order, s, d, D, M, I, rng, deadline)
        if res is not None:
            sig, volt = res
            return order, M, sig, volt
    return None


def _lift(N, s, d, M, sig, volt):
    """Edge list of the lift: A_{i,x} -- B_{j,x*g} for each dart (i, j, g)."""
    sN = s * N
    E = []
    for t in range(d):
        st, vt = sig[t], volt[t]
        for i in range(s):
            j, g = st[i], vt[i]
            for x in range(N):
                E.append((i * N + x, sN + j * N + M[x][g]))
    return E


# ----------------------------------------------------------------------------
# Baseline families.
# ----------------------------------------------------------------------------

def _pg_for_degree(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget_total = max(0.5, min(0.8 * time_limit, time_limit - 5.0))
    deadline = start + budget_total
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = [1, []]

    def consider(n, e):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best[0] = n
            best[1] = e

    # Record-matching case for D = 3.
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best[0], best[1]

    # Always-valid fallback (rejected automatically if it fails the check).
    consider(*lib.haar_graph(d, range(d)))
    if D == 3:
        pg = _pg_for_degree(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if d < 2 or D < 2:
        return best[0], best[1]

    Moore = lib._moore_bound(d, D)

    # Safety net: single-orbit lifts (a plain bi-Cayley graph) near half the Moore bound.
    safety_dl = start + 0.25 * budget_total
    N_top = Moore // 4
    for N in range(N_top, max(d, N_top - 30), -1):
        now = time.monotonic()
        if now >= safety_dl:
            break
        res = _attempt(N, 1, d, D, rng, min(safety_dl, now + 0.4))
        if res is not None:
            order, M, sig, volt = res
            consider(2 * order, _lift(order, 1, d, M, sig, volt))
            break

    # Main phase: multi-orbit lifts (s >= 2 base vertices per side), ascending in order
    # above the current best, so any improvement is found early.
    budget = 0.3
    while time.monotonic() < deadline:
        cands = []
        for V in range(best[0] + 2, min(Moore, best[0] + 80) + 1, 2):
            for s in range(2, 7):
                if V % (2 * s) == 0:
                    N = V // (2 * s)
                    if N >= 2:
                        cands.append((V, s, N))
        if not cands:
            break
        progress = False
        for V, s, N in cands:
            now = time.monotonic()
            if now >= deadline:
                break
            res = _attempt(N, s, d, D, rng, min(deadline, now + budget))
            if res is None:
                continue
            order, M, sig, volt = res
            consider(2 * s * order, _lift(order, s, d, M, sig, volt))
            progress = True
            break
        if not progress:
            budget *= 2

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best[0], best[1]
