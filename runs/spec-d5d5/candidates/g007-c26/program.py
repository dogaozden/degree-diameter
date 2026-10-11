import math
import random
import time

import lib

BASE_FRAC = 0.35   # share of time_limit for the bi-Cayley baseline (safe fallback)
END_FRAC = 0.80    # stop all searching at this share of time_limit
ITERS = 400        # annealing steps per (group, connection set) try in the baseline


# ----------------------------------------------------------------------------
# Simple baselines (always verified before use).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


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


def _tables(N, m, k, r):
    """Right-multiplication table mul_tab[x][g] for the group Z_m x|_r Z_k of order N."""
    _, mul, _ = lib.semidirect_group(m, k, r)
    return [[mul(x, g) for g in range(N)] for x in range(N)]


# ----------------------------------------------------------------------------
# Baseline: bi-Cayley graphs over semidirect products (A_x -- B_{x s}, s in S).
# ----------------------------------------------------------------------------

def _unreached(N, T, invs, S, D):
    """Count (source, vertex) pairs not within distance D, for sources A_0 and B_0."""
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


def _anneal(N, T, invs, d, D, rng, iters, deadline):
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(N, T, invs, S, D)
    for it in range(iters):
        if cur == 0:
            return S
        if time.monotonic() > deadline:
            break
        temp = max(0.05, 2.0 * (1.0 - it / iters))
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, T, invs, S2, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            S, cur = S2, v
    return S if cur == 0 else None


def _attempt(N, d, D, rng, deadline):
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:12]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        S = _anneal(N, T, invs, d, D, rng, ITERS, deadline)
        if S is not None:
            return T, S
    return None


def _bicayley_phase(d, D, rng, deadline, consider):
    Nmax = lib._moore_bound(d, D) // 2
    top = min(Nmax, Nmax // 2 + 3)
    cands = set(range(d + 1, top + 1))
    budget = 0.4
    while time.monotonic() < deadline and cands:
        success = False
        for N in sorted(cands, reverse=True):
            now = time.monotonic()
            if now >= deadline:
                break
            res = _attempt(N, d, D, rng, min(deadline, now + budget))
            if res is None:
                continue
            T, S = res
            edges = [(x, N + T[x][g]) for x in range(N) for g in S]
            consider(2 * N, edges)
            cands = {M for M in cands if M > N}
            if N + 1 <= Nmax:
                cands.add(N + 1)
            success = True
            break
        if not success:
            budget *= 2


# ----------------------------------------------------------------------------
# Main new construction: voltage lifts of small bipartite multigraph bases over
# non-cyclic groups. Base: p vertices on each side, d darts per A vertex
# (realised as d random permutations, so the base is d-regular and bipartite).
# Lift: A_i,x -- B_j,(x*g) for each dart (i, j, g). G acts on the left, so only
# the identity coset of each base vertex needs a BFS source.
# ----------------------------------------------------------------------------

def _slots(p, d, rng):
    """Base dart slots (i, j): d random permutations; resample until the base is connected."""
    for _ in range(200):
        slots = []
        for _ in range(d):
            perm = list(range(p))
            rng.shuffle(perm)
            slots.extend((i, perm[i]) for i in range(p))
        adj = [[] for _ in range(2 * p)]
        for i, j in slots:
            adj[i].append(p + j)
            adj[p + j].append(i)
        seen = [False] * (2 * p)
        seen[0] = True
        st = [0]
        while st:
            v = st.pop()
            for w in adj[v]:
                if not seen[w]:
                    seen[w] = True
                    st.append(w)
        if all(seen):
            return slots
    return None


def _lift_cost(p, N, mul_tab, darts, D):
    """Total unreached (source, vertex) pairs over the 2p base-class sources."""
    V = 2 * p * N
    adj = [[] for _ in range(V)]
    for i, j, g in darts:
        bj = (p + j) * N
        ai = i * N
        for x in range(N):
            a = ai + x
            b = bj + mul_tab[x][g]
            adj[a].append(b)
            adj[b].append(a)
    total = 0
    for u in range(2 * p):
        s = u * N  # identity element of the group is index 0
        seen = bytearray(V)
        seen[s] = 1
        frontier = [s]
        cnt = 1
        for _ in range(D):
            nxt = []
            for v in frontier:
                for w in adj[v]:
                    if not seen[w]:
                        seen[w] = 1
                        nxt.append(w)
            if not nxt:
                break
            cnt += len(nxt)
            frontier = nxt
        total += V - cnt
    return total


def _anneal_lift(p, N, mul_tab, darts, used, D, rng, end):
    cur = _lift_cost(p, N, mul_tab, darts, D)
    t0 = time.monotonic()
    span = max(1e-3, end - t0)
    while cur > 0:
        now = time.monotonic()
        if now >= end:
            return None
        temp = max(0.05, 2.0 * (1.0 - (now - t0) / span))
        t = rng.randrange(len(darts))
        i, j, g_old = darts[t]
        g_new = rng.randrange(N)
        if g_new in used[(i, j)]:
            continue
        darts[t] = (i, j, g_new)
        v = _lift_cost(p, N, mul_tab, darts, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            used[(i, j)].discard(g_old)
            used[(i, j)].add(g_new)
            cur = v
        else:
            darts[t] = (i, j, g_old)
    return darts


def _try_lift(d, D, p, N, budget, rng, deadline, consider):
    groups = _groups(N)
    rng.shuffle(groups)
    groups = groups[:4]
    t_end = min(deadline, time.monotonic() + budget)
    for idx, (m, k, r) in enumerate(groups):
        now = time.monotonic()
        if now >= t_end:
            break
        end = now + (t_end - now) / (len(groups) - idx)
        mul_tab = _tables(N, m, k, r)
        slots = _slots(p, d, rng)
        if slots is None:
            continue
        used = {}
        darts = []
        for i, j in slots:
            s = used.setdefault((i, j), set())
            g = rng.randrange(N)
            while g in s:
                g = rng.randrange(N)
            s.add(g)
            darts.append((i, j, g))
        res = _anneal_lift(p, N, mul_tab, darts, used, D, rng, end)
        if res is not None:
            edges = []
            for i, j, g in res:
                for x in range(N):
                    edges.append((i * N + x, (p + j) * N + mul_tab[x][g]))
            if consider(2 * p * N, edges):
                return True
    return False


def _lift_phase(d, D, rng, deadline, best_n, consider):
    Mmax = lib._moore_bound(d, D)
    cands = []
    for p in (2, 3, 4, 5):
        for N in range(max(d, 2), Mmax // (2 * p) + 1):
            tot = 2 * p * N
            if best_n < tot <= Mmax:
                cands.append((tot, rng.random(), p, N))
    if not cands:
        return
    cands.sort()
    budget = 1.0
    cur_best = best_n
    while time.monotonic() < deadline:
        live = [c for c in cands if c[0] > cur_best]
        if not live:
            break
        improved = False
        for tot, _, p, N in live:
            if time.monotonic() >= deadline:
                break
            if _try_lift(d, D, p, N, budget, rng, deadline, consider):
                cur_best = tot
                improved = True
                break
        if not improved:
            budget *= 2


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + END_FRAC * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = [1, []]

    def consider(n, e):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best[0] = n
            best[1] = e
            return True
        return False

    # Record-matching case for D = 3.
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best[0], best[1]

    if D >= 2:
        consider(*lib.haar_graph(d, range(d)))
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if d >= 2 and D >= 2:
        base_deadline = min(deadline, start + BASE_FRAC * time_limit)
        _bicayley_phase(d, D, rng, base_deadline, consider)
        _lift_phase(d, D, rng, deadline, best[0], consider)

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best[0], best[1]
