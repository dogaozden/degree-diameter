import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Constants.
# ----------------------------------------------------------------------------

MAX_GROUPS = 8        # groups tried per order N before moving on
CLIMB_ITERS = 400     # single-element hill-climb steps per group
ORBIT_ITERS = 500     # orbit-move climb steps per group
ANNEAL_ITERS = 500    # annealing steps for multi-base lifts
BAND_EXTRA = 12       # sweep window above the lower bound for bi-Cayley orders
_BIG = 10 ** 9
_TABLE_CACHE = {}


# ----------------------------------------------------------------------------
# D = 3 baseline: incidence graph of the projective plane PG(2, q).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Group machinery: semidirect products Z_m x|_r Z_k, element (a, b) coded as a*k+b.
# Identity is always code 0.
# ----------------------------------------------------------------------------

def _groups(N):
    """Return semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k."""
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
    """Cached (order, mul, T, invs) for Z_m x|_r Z_k, where T[x][g] = x*g and invs[g] = g^-1."""
    key = (m, k, r)
    hit = _TABLE_CACHE.get(key)
    if hit is not None:
        return hit
    order, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(order)] for x in range(order)]
    invs = [inv(g) for g in range(order)]
    val = (order, mul, T, invs)
    if len(_TABLE_CACHE) >= 48:
        _TABLE_CACHE.clear()
    _TABLE_CACHE[key] = val
    return val


def _unreached(N, T, invs, S, D):
    """Count vertex pairs (source, target) not within distance D, from A_0 and B_0.

    Bi-Cayley graph: A_x ~ B_{x g} for g in S. Left translation is an automorphism
    that is transitive on each side, so eccentricities of A_0 and B_0 suffice.
    """
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
                    row = T[u]
                    for g in S:
                        v = N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    row = T[u - N]
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


def _climb(N, T, invs, d, D, rng, iters, deadline):
    """Single-element hill-climb on S (identity fixed as one dart, WLOG). Sideways moves allowed."""
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(N, T, invs, S, D)
    for _ in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, T, invs, S2, D)
        if v <= cur:
            S, cur = S2, v
    return S if cur == 0 else None


# ----------------------------------------------------------------------------
# NEW: conjugation-orbit restricted bi-Cayley search.
#
# For a group G and a fixed h, the map g -> h g h^-1 is an automorphism phi.
# Relabelling A_x -> A_{phi x}, B_y -> B_{phi y} sends G_S to G_{phi(S)}, so the
# isomorphism class depends only on S up to phi. Choosing S as {e} plus a union
# of phi-orbits gives graphs with the extra symmetry phi(S) = S, and the search
# moves whole orbits instead of single elements. The moves preserve the orbit-size
# multiset, so the degree stays exactly d.
# ----------------------------------------------------------------------------

def _conj_orbits(N, T, invs, h):
    """Orbits of the non-identity elements under g -> h g h^-1."""
    ih = invs[h]
    perm = [T[T[h][g]][ih] for g in range(N)]
    seen = [False] * N
    seen[0] = True
    orbits = []
    for g in range(1, N):
        if seen[g]:
            continue
        orb = []
        x = g
        while not seen[x]:
            seen[x] = True
            orb.append(x)
            x = perm[x]
        orbits.append(orb)
    return orbits


def _fit_orbits(orbits, target, rng, tries=60):
    """Random choice of orbit indices whose sizes sum exactly to target; None on failure."""
    for _ in range(tries):
        idx = list(range(len(orbits)))
        rng.shuffle(idx)
        rem = target
        chosen = []
        for i in idx:
            s = len(orbits[i])
            if s <= rem:
                chosen.append(i)
                rem -= s
                if rem == 0:
                    break
        if rem == 0:
            return chosen
    return None


def _orbit_climb(N, T, invs, d, D, rng, iters, deadline):
    """Hill-climb over unions of conjugation orbits; S = {e} + chosen orbits has size d."""
    target = d - 1
    orbits = None
    chosen = None
    for _ in range(12):
        h = rng.randrange(1, N)
        orbits = _conj_orbits(N, T, invs, h)
        chosen = _fit_orbits(orbits, target, rng)
        if chosen is not None:
            break
    if chosen is None:
        return None

    def make_S(ch):
        S = [0]
        for i in ch:
            S.extend(orbits[i])
        return S

    cur = list(chosen)
    cost = _unreached(N, T, invs, make_S(cur), D)
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        j = rng.randrange(len(cur))
        sz = len(orbits[cur[j]])
        pool = [i for i in range(len(orbits))
                if len(orbits[i]) == sz and i not in cur]
        if not pool:
            continue
        new = cur[:]
        new[j] = rng.choice(pool)
        v = _unreached(N, T, invs, make_S(new), D)
        if v <= cost:
            cur, cost = new, v
    return make_S(cur) if cost == 0 else None


# ----------------------------------------------------------------------------
# Multi-base voltage lifts over semidirect products, annealed.
# ----------------------------------------------------------------------------

def _right_perm(mul, G, s):
    """Permutation g -> g*s of the group."""
    return [mul(g, s) for g in range(G)]


def _cost(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs not reached within D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        base_a = i * G
        base_b = (k + j) * G
        for g in range(G):
            a = base_a + g
            b = base_b + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen = [False] * N
        seen[src] = True
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = True
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer B-assignments."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    T0 = max(1.0, 0.05 * cost) if cost < _BIG else 1.0
    T_end = 0.5
    decay = (T_end / T0) ** (1.0 / max(1, iters)) if T0 > T_end else 1.0
    T = T0

    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(T_end, T * decay)

        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _right_perm(mul, G, new_s)
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_perm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Main search: aim above the current best order.
    sweep_next = None
    while best[0] < moore and time.monotonic() < deadline:
        n_best = best[0]

        if rng.random() < 0.75:
            # Bi-Cayley lift on a group of order N; the lift has 2N vertices.
            lo = n_best // 2 + 1
            if lo > moore // 2:
                break
            if sweep_next is None or sweep_next < lo or sweep_next > lo + BAND_EXTRA:
                sweep_next = lo
            N = sweep_next
            sweep_next += 1
            groups = _groups(N)
            rng.shuffle(groups)
            found = None
            for m, k2, rr in groups[:MAX_GROUPS]:
                if time.monotonic() > deadline:
                    break
                _, _, T, invs = _tables(m, k2, rr)
                if rng.random() < 0.6:
                    S = _orbit_climb(N, T, invs, d, D, rng, ORBIT_ITERS, deadline)
                else:
                    S = _climb(N, T, invs, d, D, rng, CLIMB_ITERS, deadline)
                if S is not None:
                    found = (T, S)
                    break
            if found is not None:
                T, S = found
                edges = [(x, N + T[x][g]) for x in range(N) for g in S]
                consider(2 * N, edges)
        else:
            # Multi-base lift with k base vertices per side over a group of order G.
            k = rng.choice((2, 3))
            lo = n_best // (2 * k) + 1
            if 2 * k * lo > moore:
                continue
            G = lo + rng.randrange(max(2, lo // 10))
            if G < 2:
                continue
            m, k2, rr = rng.choice(_groups(G))
            order, mul, _ = lib.semidirect_group(m, k2, rr)
            res = _anneal(d, D, k, order, mul, rng, deadline, ANNEAL_ITERS)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
