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
# Bi-Cayley graphs over groups of order N: a_x ~ b_{x s} for s in S, |S| = d.
# Diameter 3 holds when S S^-1 = G.
#
# NEW (this version): degree-preserving repair. When annealing cannot find an
# exact S, keep the closest S (fewest uncovered group elements), build the
# bi-Cayley graph, and run simulated annealing over DOUBLE EDGE SWAPS
# (a1,b1),(a2,b2) -> (a1,b2),(a2,b1). Swaps keep every degree at d and keep the
# graph bipartite, and the cost is the exact number of vertex pairs at
# distance greater than 3. A zero-cost state is a valid diameter-3 graph of
# order 2N, possibly with N not coverable by any group-difference structure.
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
    """Anneal S (size d, containing 0) to cover G by S S^-1.

    Returns (S, unc): S with unc == 0 on success, else the best S seen with its
    count of uncovered non-identity elements.
    """
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
    best_unc, best_S = unc, list(S)
    if unc == 0:
        return S, 0
    for it in range(moves):
        if (it & 255) == 0 and time.monotonic() >= deadline:
            break
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
                return S, 0
            if unc < best_unc:
                best_unc, best_S = unc, list(S)
        else:
            _delta(cnt, S, idx, x, -1, Q)
            _delta(cnt, S, idx, old, 1, Q)
    return best_S, best_unc


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


def _edges_from(N, S, M):
    """Bi-Cayley edges: a_x = x joins b_y = N + x*s for s in S."""
    return [(x, N + M[x][s]) for x in range(N) for s in S]


def _bad(n, adj, D):
    """Number of unordered vertex pairs at distance greater than D."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _repair(N, D, E0, rng, deadline):
    """Simulated annealing over degree-preserving double edge swaps minimising bad pairs.

    E0 is a list of (a, b) edges with a < N <= b. Returns (edges, cost).
    """
    n = 2 * N
    E = [[a, b] for a, b in E0]
    adj = [set() for _ in range(n)]
    for a, b in E:
        adj[a].add(b)
        adj[b].add(a)
    cur = _bad(n, adj, D)
    T0 = 1.5
    t0 = time.monotonic()
    span = max(1e-6, deadline - t0)
    m = len(E)
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        frac = (now - t0) / span
        T = max(0.02, T0 * (1.0 - frac))
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2 or b2 in adj[a1] or b1 in adj[a2]:
            continue
        adj[a1].discard(b1)
        adj[b1].discard(a1)
        adj[a2].discard(b2)
        adj[b2].discard(a2)
        adj[a1].add(b2)
        adj[b2].add(a1)
        adj[a2].add(b1)
        adj[b1].add(a2)
        new = _bad(n, adj, D)
        if new <= cur or rng.random() < math.exp(-(new - cur) / T):
            E[i] = [a1, b2]
            E[j] = [a2, b1]
            cur = new
        else:
            adj[a1].discard(b2)
            adj[b2].discard(a1)
            adj[a2].discard(b1)
            adj[b1].discard(a2)
            adj[a1].add(b1)
            adj[b1].add(a1)
            adj[a2].add(b2)
            adj[b2].add(a2)
    return [(a, b) for a, b in E], cur


def _try_N(N, d, D, rng, deadline):
    """Try to produce a valid diameter-D bipartite graph of order 2N. Returns edges or None."""
    specs = _specs(N, rng)
    tabs = []
    for spec in specs:
        try:
            M, Q = _tables(spec, N)
            tabs.append((M, Q))
        except Exception:
            pass
    if not tabs:
        return None

    now = time.monotonic()
    exact_deadline = now + 0.35 * (deadline - now)
    cands = []
    r = 0
    while time.monotonic() < exact_deadline:
        M, Q = tabs[r % len(tabs)]
        r += 1
        S, u = _anneal(N, d, Q, rng, exact_deadline, 20000)
        if u == 0:
            return _edges_from(N, S, M)
        cands.append((u, S, M))

    if not cands:
        return None
    cands.sort(key=lambda c: c[0])
    top = cands[:2]
    for idx, (u, S, M) in enumerate(top):
        rem = deadline - time.monotonic()
        if rem <= 0:
            break
        share = rem / (len(top) - idx)
        edges, cost = _repair(N, D, _edges_from(N, S, M), rng, time.monotonic() + share)
        if cost == 0:
            return edges
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
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

    try:
        # Bi-Cayley search with degree-preserving repair for larger orders.
        max_N = d * (d - 1) + 1
        N = best[0] // 2 + 1
        while N <= max_N and N >= d and time.monotonic() < deadline:
            edges = _try_N(N, d, D, rng, deadline)
            if edges is None:
                break
            n = 2 * N
            if n > best[0] and lib.is_valid(n, edges, d, D):
                best = (n, edges)
            N += 1
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
