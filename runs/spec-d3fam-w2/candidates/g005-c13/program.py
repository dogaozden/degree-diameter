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
# Bi-Cayley graphs over groups (inherited from the parent).
# a_x ~ b_{x s} for s in S, |S| = d, 1 in S. Diameter 3 iff S S^-1 = G.
# ----------------------------------------------------------------------------

def _delta(cnt, S, skip, v, sign, Q):
    """Add (sign>0) or remove (sign<0) the quotients created by element v against S[j], j != skip."""
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
# NEW: orbit-representative lift search over a group with 2a base vertices.
#
# Base graph: a A-orbits and a B-orbits, each of size N (a group G of order N).
# Layer t gives a permutation perm_t of {0..a-1} (A_i -> B_{perm_t[i]}) and a
# voltage g_{t,i}. Edge (A_i, x) -- (B_j, x*g) for each dart (i, j, g).
# Every A and B vertex then has degree exactly d (one dart per layer).
#
# Key fact used: left multiplication by h in G is an automorphism of the lift,
# so every vertex is equivalent to one of the 2a base representatives
# (A_i, identity) or (B_j, identity). A graph has diameter <= D iff each of
# these 2a representatives reaches all vertices within D steps. This turns a
# full all-pairs check into 2a BFS runs, which makes an annealing search over
# voltages affordable. The cost is the number of unreached (rep, vertex) pairs,
# plus a large penalty for duplicate darts (i, j, g) that would merge edges.
# ----------------------------------------------------------------------------

def _lift_adj(a, N, M, perms, gss):
    """Unified adjacency: A vertices are 0..aN-1, B vertices are aN..2aN-1."""
    nA = a * N
    adj = [[] for _ in range(2 * nA)]
    for perm, gs in zip(perms, gss):
        for i in range(a):
            j = perm[i]
            g = gs[i]
            ub = i * N
            vb = nA + j * N
            for x in range(N):
                u = ub + x
                v = vb + M[x][g]
                adj[u].append(v)
                adj[v].append(u)
    return adj


def _dups(a, perms, gss):
    """Number of repeated darts (i, j, g); each would merge two edges and lower degree."""
    seen = set()
    dup = 0
    for perm, gs in zip(perms, gss):
        for i in range(a):
            key = (i, perm[i], gs[i])
            if key in seen:
                dup += 1
            else:
                seen.add(key)
    return dup


def _lift_cost(a, N, D, M, perms, gss):
    """0 iff the lift has diameter <= D (given no duplicate darts)."""
    dup = _dups(a, perms, gss)
    if dup:
        return 1000 * dup
    adj = _lift_adj(a, N, M, perms, gss)
    n = 2 * a * N
    nA = a * N
    reps = [i * N for i in range(a)] + [nA + j * N for j in range(a)]
    bad = 0
    for src in reps:
        seen = bytearray(n)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            if not nxt:
                break
            cnt += len(nxt)
            frontier = nxt
        bad += n - cnt
    return bad


def _lift_search(a, N, d, D, M, rng, deadline):
    """Simulated annealing over permutations and voltages. Returns (perms, gss) or None."""
    perms = []
    gss = []
    for _ in range(d):
        p = list(range(a))
        rng.shuffle(p)
        perms.append(p)
        gss.append([rng.randrange(N) for _ in range(a)])
    cost = _lift_cost(a, N, D, M, perms, gss)
    it = 0
    while cost > 0:
        if time.monotonic() >= deadline:
            return None
        it += 1
        T = 2.0 * (0.01 ** ((it % 2000) / 2000.0)) + 0.05
        t = rng.randrange(d)
        if a >= 2 and rng.random() < 0.3:
            p = perms[t]
            i1, i2 = rng.sample(range(a), 2)
            p[i1], p[i2] = p[i2], p[i1]
            new = _lift_cost(a, N, D, M, perms, gss)
            if new <= cost or rng.random() < math.exp(-(new - cost) / T):
                cost = new
            else:
                p[i1], p[i2] = p[i2], p[i1]
        else:
            gs = gss[t]
            i = rng.randrange(a)
            old = gs[i]
            gs[i] = rng.randrange(N)
            new = _lift_cost(a, N, D, M, perms, gss)
            if new <= cost or rng.random() < math.exp(-(new - cost) / T):
                cost = new
            else:
                gs[i] = old
    return perms, gss


def _lift_edges(a, N, M, perms, gss):
    """Materialise a found lift as (n, edges)."""
    nA = a * N
    edges = []
    for perm, gs in zip(perms, gss):
        for i in range(a):
            j = perm[i]
            g = gs[i]
            for x in range(N):
                edges.append((i * N + x, nA + j * N + M[x][g]))
    return 2 * nA, edges


def _lift_try(a, N, d, D, rng, sub):
    """Try to find a lift of order 2aN before deadline sub. Returns (n, edges) or None."""
    specs = _specs(N, rng)
    tabs = {}
    k = 0
    while time.monotonic() < sub:
        spec = specs[k % len(specs)]
        k += 1
        if spec not in tabs:
            try:
                tabs[spec] = _tables(spec, N)[0]
            except Exception:
                tabs[spec] = None
        M = tabs[spec]
        if M is None:
            continue
        slot = min(sub, time.monotonic() + 4.0)
        found = _lift_search(a, N, d, D, M, rng, slot)
        if found is not None:
            perms, gss = found
            return _lift_edges(a, N, M, perms, gss)
    return None


def _lift_phase(best, d, D, rng, deadline):
    """Search lifts with a in {2, 3} orbits per side for orders beating best."""
    bound = lib.moore_bound(d, D)
    cands = []
    for a in (2, 3):
        N_lo = max(best[0] // (2 * a) + 1, 2)
        N_hi = bound // (2 * a)
        for N in range(N_lo, N_hi + 1):
            cands.append((a, N))
    cands.sort(key=lambda c: 2 * c[0] * c[1])
    pending = cands
    while pending and time.monotonic() < deadline:
        a, N = pending.pop(0)
        if 2 * a * N <= best[0]:
            continue
        now = time.monotonic()
        remaining = deadline - now
        budget = remaining / (len(pending) + 1) * 1.5
        sub = min(deadline, now + max(budget, 0.5))
        res = _lift_try(a, N, d, D, rng, sub)
        if res is not None:
            n, e = res
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
            pending = [c for c in pending if 2 * c[0] * c[1] > best[0]]
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
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

    # Phase 1: bi-Cayley search over groups (inherited).
    try:
        phase1_deadline = start + 0.35 * time_limit
        max_N = d * (d - 1) + 1
        N = best[0] // 2 + 1
        while N <= max_N and N >= d and time.monotonic() < phase1_deadline:
            rem = phase1_deadline - time.monotonic()
            res = _search_N(N, d, rng, time.monotonic() + 0.7 * rem)
            if res is None:
                break
            S, M = res
            n, e = 2 * N, _edges_from(N, d, S, M)
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
            N += 1
    except Exception:
        pass

    # Phase 2: orbit-representative lift search (new construction).
    try:
        best = _lift_phase(best, d, D, rng, start + 0.8 * time_limit)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
