import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Constants
# ----------------------------------------------------------------------------

PER_N_SECONDS = 0.35     # time spent on one cyclic order N before moving on
ORBIT_COMBO_CAP = 800    # orbit-union candidates tried per multiplier subgroup
CLIMB_ITERS = 300        # hill-climb steps per attempt
ANNEAL_ITERS = 600       # annealing steps for multi-base lifts
MAX_GROUPS = 6           # semidirect groups tried per order N
BAND_EXTRA = 12          # window above the lower bound for semidirect orders


# ----------------------------------------------------------------------------
# D = 3 baseline: incidence graph of a projective plane.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# NEW IDEA: multiplier-invariant Haar graphs.
#
# A Haar graph of Z_N with connection set S (A_x ~ B_{x+s}, s in S) is
# bipartite and d-regular. If a unit multiplier h satisfies h*S = S (as a set
# mod N), then x -> h*x on both sides is an automorphism. So S may be taken as
# {0} union a union of orbits of a multiplier subgroup H <= Z_N^*. This shrinks
# the search space from C(N-1, d-1) to a small set of orbit combinations, which
# can be enumerated (capped) and checked exactly.
# ----------------------------------------------------------------------------

_SUB_CACHE = {}


def _mult_subgroups(N):
    """Distinct cyclic multiplier subgroups of Z_N^* of order >= 2, largest first."""
    hit = _SUB_CACHE.get(N)
    if hit is not None:
        return hit
    seen = set()
    out = []
    for u in range(2, N):
        if math.gcd(u, N) != 1:
            continue
        H = {1 % N}
        x = u
        while x not in H:
            H.add(x)
            x = x * u % N
        fz = frozenset(H)
        if len(fz) > 1 and fz not in seen:
            seen.add(fz)
            out.append(fz)
    out.sort(key=len, reverse=True)
    if len(_SUB_CACHE) > 64:
        _SUB_CACHE.clear()
    _SUB_CACHE[N] = out
    return out


def _orbits(N, H):
    """Orbits of the nonzero residues under multiplication by H."""
    seen = [False] * N
    seen[0] = True
    orbs = []
    for x in range(1, N):
        if seen[x]:
            continue
        orb = sorted({h * x % N for h in H})
        for y in orb:
            seen[y] = True
        orbs.append(orb)
    return orbs


def _orbit_combos(sizes, need):
    """Generator of index lists of orbits whose sizes sum exactly to `need`."""
    n = len(sizes)
    chosen = []

    def rec(start, rem):
        if rem == 0:
            yield list(chosen)
            return
        for i in range(start, n):
            s = sizes[i]
            if s <= rem:
                chosen.append(i)
                yield from rec(i + 1, rem - s)
                chosen.pop()

    return rec(0, need)


def _bfs_unreached(N, S, Sneg, D, src):
    """Vertices (of 2N) not within distance D of src in the Haar graph Z_N, S."""
    seen = bytearray(2 * N)
    seen[src] = 1
    count = 1
    frontier = [src]
    for _ in range(D):
        nxt = []
        for u in frontier:
            if u < N:
                for s in S:
                    v = N + (u + s) % N
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            else:
                y = u - N
                for s in Sneg:
                    v = (y + s) % N
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
        count += len(nxt)
        frontier = nxt
        if not frontier:
            break
    return 2 * N - count


def _cost_cyclic(N, S, D):
    """Unreached pairs from A_0 and B_0; zero means the Haar graph has diameter <= D."""
    Sneg = [(-s) % N for s in S]
    return _bfs_unreached(N, S, Sneg, D, 0) + _bfs_unreached(N, S, Sneg, D, N)


def _cyc_edges(N, S):
    return [(x, N + (x + s) % N) for x in range(N) for s in S]


def _orbit_search(N, d, D, rng, deadline):
    """Search S = {0} union (orbits of H) over multiplier subgroups H; return S or None."""
    if N < d:
        return None
    for H in _mult_subgroups(N):
        if time.monotonic() > deadline:
            return None
        orbs = _orbits(N, H)
        rng.shuffle(orbs)
        tried = 0
        for combo in _orbit_combos([len(o) for o in orbs], d - 1):
            S = [0]
            for i in combo:
                S.extend(orbs[i])
            tried += 1
            if _cost_cyclic(N, S, D) == 0:
                return S
            if tried >= ORBIT_COMBO_CAP:
                break
            if (tried & 31) == 0 and time.monotonic() > deadline:
                return None
    return None


def _climb_cyclic(N, d, D, rng, iters, deadline):
    """Plain hill-climb on connection sets of Z_N (0 fixed as one dart)."""
    if N < d or d < 2:
        return None
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _cost_cyclic(N, S, D)
    for _ in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _cost_cyclic(N, S2, D)
        if v <= cur:
            S, cur = S2, v
    return S if cur == 0 else None


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over Z_m x|_r Z_k (hill-climb) and multi-base annealing.
# ----------------------------------------------------------------------------

def _groups(N):
    """Semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


_TABLE_CACHE = {}


def _tables(m, k, r):
    """Cached (order, mul, T, invs) with T[x][g] = x*g and invs[g] = g^-1."""
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


def _unreached_group(N, T, invs, S, D):
    """Unreached pairs from A_0 and B_0 for the bi-Cayley graph A_x ~ B_{x g}, g in S."""
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


def _climb_group(N, T, invs, d, D, rng, iters, deadline):
    """Hill-climb a connection set S in a group of order N (identity fixed as one dart)."""
    if N < d or d < 2:
        return None
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached_group(N, T, invs, S, D)
    for _ in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached_group(N, T, invs, S2, D)
        if v <= cur:
            S, cur = S2, v
    return S if cur == 0 else None


def _right_perm(mul, G, s):
    """Permutation g -> g*s of the group."""
    return [mul(g, s) for g in range(G)]


def _cost(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs not reached within distance D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return 10 ** 9
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

    big = 10 ** 9
    T0 = max(1.0, 0.05 * cost) if cost < big else 1.0
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
    budget = max(0.5, min(0.85 * time_limit, time_limit - 4.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and meets the Moore bound for D = 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3 and d >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Ratchet for the cyclic multiplier-invariant sweep.
    n_cyc = max(best[0] // 2 + 1, moore // 6)

    while best[0] < moore and time.monotonic() < deadline:
        if best[0] // 2 + 1 > moore // 2:
            break
        r = rng.random()

        if r < 0.5:
            N = max(n_cyc, best[0] // 2 + 1)
            if 2 * N <= moore:
                per = min(deadline, time.monotonic() + PER_N_SECONDS)
                S = _orbit_search(N, d, D, rng, per)
                if S is None:
                    S = _climb_cyclic(N, d, D, rng, CLIMB_ITERS, per)
                if S is not None:
                    consider(2 * N, _cyc_edges(N, S))
                n_cyc = N + 1

        elif r < 0.8:
            N = best[0] // 2 + 1 + rng.randrange(BAND_EXTRA)
            if 2 * N <= moore:
                groups = _groups(N)
                rng.shuffle(groups)
                for m, k2, rr in groups[:MAX_GROUPS]:
                    if time.monotonic() > deadline:
                        break
                    _, _, T, invs = _tables(m, k2, rr)
                    S = _climb_group(N, T, invs, d, D, rng, CLIMB_ITERS, deadline)
                    if S is not None:
                        consider(2 * N, [(x, N + T[x][g]) for x in range(N) for g in S])
                        break

        else:
            k = rng.choice((2, 3))
            lo = best[0] // (2 * k) + 1
            G = lo + rng.randrange(max(2, lo // 10))
            if G >= 2 and 2 * k * G <= moore:
                m, k2, rr = rng.choice(_groups(G))
                order, mul, _ = lib.semidirect_group(m, k2, rr)
                res = _anneal(d, D, k, order, mul, rng, deadline, ANNEAL_ITERS)
                if res is not None:
                    consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
