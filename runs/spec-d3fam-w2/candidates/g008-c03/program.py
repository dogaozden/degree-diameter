import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Baselines (safe fallbacks): record AL graph, projective plane incidence,
# and K_{d,d}.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# NEW CONSTRUCTION: multiplier-invariant (orbit-restricted) cyclic bi-Cayley
# graphs.
#
# Let G = Z_N and S = {0} U T with |S| = d. The bipartite graph
# a_x ~ b_{x+s} (s in S) is 2N vertices, d-regular, bipartite, and has
# diameter <= 3 exactly when S - S = G (same-side pairs are at distance 2,
# cross pairs at distance <= 3 since (S-S)+S = G).
#
# Restriction: pick a unit t mod N of order k with (d-1) divisible by k, and
# require T to be a union of full <t>-orbits on Z_N \ {0} (every orbit of
# size k). Then S is invariant under multiplication by t, which cuts the
# search space from C(N-1, d-1) to C(#orbits, (d-1)/k) and makes the
# difference set much easier to find. Search is simulated annealing over
# which orbits are chosen, with cost = number of nonzero residues not hit by
# S - S.
# ----------------------------------------------------------------------------

def _orbit_pools(N, d):
    """For each unit t mod N whose order k divides d-1, list the free <t>-orbits of size k on Z_N \\ {0}."""
    res = []
    for t in range(2, N):
        if math.gcd(t, N) != 1:
            continue
        k, pw = 1, t
        while pw != 1:
            pw = pw * t % N
            k += 1
        if k < 2 or (d - 1) % k:
            continue
        m = (d - 1) // k
        seen = set()
        pool = []
        for x in range(1, N):
            if x in seen:
                continue
            orb = [x]
            y = x * t % N
            while y != x:
                orb.append(y)
                y = y * t % N
            seen.update(orb)
            if len(orb) == k:
                pool.append(orb)
        if len(pool) >= m:
            res.append((t, k, pool, m))
    return res


def _orbit_S(ch, pool):
    """Build S = {0} U (union of the chosen orbits)."""
    S = [0]
    for i in ch:
        S.extend(pool[i])
    return S


def _orbit_cost(S, N):
    """Number of nonzero residues mod N not represented as a difference of two elements of S."""
    diffs = set()
    for i in S:
        for j in S:
            if i != j:
                diffs.add((i - j) % N)
    return (N - 1) - len(diffs)


def _orbit_search(N, d, rng, deadline):
    """Find S = {0} U orbits with S - S = Z_N, or return None before the deadline."""
    pools = _orbit_pools(N, d)
    if not pools:
        return None
    rounds = 0
    iters = 6000
    while time.monotonic() < deadline:
        t, k, pool, m = pools[rounds % len(pools)]
        rounds += 1
        ch = rng.sample(range(len(pool)), m)
        cost = _orbit_cost(_orbit_S(ch, pool), N)
        for it in range(iters):
            if cost == 0:
                return _orbit_S(ch, pool)
            if (it & 255) == 0 and time.monotonic() >= deadline:
                return None
            T = 0.8 * (0.02 ** (it / iters))
            j = rng.randrange(m)
            new = rng.randrange(len(pool))
            if new in ch:
                continue
            old = ch[j]
            ch[j] = new
            c2 = _orbit_cost(_orbit_S(ch, pool), N)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                ch[j] = old
        if cost == 0:
            return _orbit_S(ch, pool)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley graphs over NON-ABELIAN groups (parent's search, kept as a second
# phase). Let G be a group of order N and S a subset of G with |S| = d and
# 1 in S. Vertices a_x, b_y; a_x ~ b_{x s} for s in S. Diameter <= 3 iff
# S S^-1 = G.
# ----------------------------------------------------------------------------

def _delta(cnt, S, skip, v, sign, Q):
    """Add (sign>0) or remove (sign<0) the quotients created by element v against S[j], j != skip.

    Returns the change in the number of uncovered non-identity group elements.
    """
    change = 0
    for j, b in enumerate(S):
        if j == skip:
            continue
        for y in (Q[v][b], Q[b][v]):
            if sign > 0:
                if cnt[y] == 0:
                    change -= 1
                cnt[y] += 1
            else:
                cnt[y] -= 1
                if cnt[y] == 0:
                    change += 1
    return change


def _anneal(N, d, Q, rng, deadline, moves):
    """Find S of size d, containing the identity 0, with S S^-1 = G; None on failure or timeout."""
    S = [0] + rng.sample(range(1, N), d - 1)
    cnt = [0] * N
    unc = N - 1
    for j in range(d):
        for k in range(d):
            if j != k:
                y = Q[S[j]][S[k]]
                if cnt[y] == 0:
                    unc -= 1
                cnt[y] += 1
    if unc == 0:
        return S
    for it in range(moves):
        if (it & 255) == 0 and time.monotonic() >= deadline:
            return None
        T = 0.5 * (0.02 ** (it / moves))
        idx = rng.randrange(1, d)
        x = rng.randrange(1, N)
        if x in S:
            continue
        old = S[idx]
        delta = _delta(cnt, S, idx, old, -1, Q) + _delta(cnt, S, idx, x, 1, Q)
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S[idx] = x
            unc += delta
            if unc == 0:
                return S
        else:
            _delta(cnt, S, idx, x, -1, Q)
            _delta(cnt, S, idx, old, 1, Q)
    return None


def _specs(N, rng, cap=16):
    """Candidate groups of order N: the cyclic group plus a sample of semidirect products Z_a x| Z_k."""
    cands = []
    for k in range(2, N + 1):
        if N % k:
            continue
        a = N // k
        if a == 1:
            continue
        for r in range(1, a):
            if math.gcd(r, a) == 1 and pow(r, k, a) == 1:
                cands.append((a, k, r))
    rng.shuffle(cands)
    return [("cyc",)] + cands[:cap]


def _tables(spec, N):
    """Multiplication table M and quotient table Q[x][y] = x * y^-1 for the group named by spec."""
    if spec[0] == "cyc":
        _, mul, inv = lib.cyclic_group(N)
    else:
        a, k, r = spec
        _, mul, inv = lib.semidirect_group(a, k, r)
    M = [[mul(x, y) for y in range(N)] for x in range(N)]
    I = [inv(x) for x in range(N)]
    Q = [[M[x][I[y]] for y in range(N)] for x in range(N)]
    return M, Q


def _search_N(N, d, rng, deadline):
    """Search for a valid S in some group of order N before the deadline. Returns (S, M) or None."""
    specs = _specs(N, rng)
    cache = {}
    rounds = 0
    while time.monotonic() < deadline:
        spec = specs[rounds % len(specs)]
        rounds += 1
        if spec not in cache:
            try:
                cache[spec] = _tables(spec, N)
            except Exception:
                cache[spec] = None
        tab = cache[spec]
        if tab is None:
            continue
        M, Q = tab
        S = _anneal(N, d, Q, rng, deadline, 30000)
        if S is not None:
            return S, M
    return None


def _edges_from(N, d, S, M):
    """Bi-Cayley edges: a_x = x joins b_y = N + x*s for s in S."""
    return [(x, N + M[x][s]) for x in range(N) for s in S]


# ----------------------------------------------------------------------------
# Driver
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    avail = 0.8 * time_limit
    deadline = start + avail
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
    except Exception:
        pass

    max_N = d * (d - 1) + 1

    # Phase 1 (new): multiplier-invariant cyclic bi-Cayley search.
    try:
        orb_deadline = start + 0.55 * avail
        lo = max(d, best[0] // 2 + 1)
        Ns = list(range(lo, max_N + 1))
        for idx, N in enumerate(Ns):
            now = time.monotonic()
            if now >= orb_deadline:
                break
            budget = (orb_deadline - now) / (len(Ns) - idx)
            S = _orbit_search(N, d, rng, now + budget)
            if S is None:
                continue
            cand = lib.haar_graph(N, S)
            if cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
                best = cand
    except Exception:
        pass

    # Phase 2: bi-Cayley graphs over non-abelian groups.
    try:
        N = max(d, best[0] // 2 + 1)
        while N <= max_N and time.monotonic() < deadline:
            rem = deadline - time.monotonic()
            budget = 0.7 * rem
            res = _search_N(N, d, rng, time.monotonic() + budget)
            if res is None:
                break
            S, M = res
            n, e = 2 * N, _edges_from(N, d, S, M)
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
            N += 1
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
