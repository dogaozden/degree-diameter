import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe baselines: K_{d,d} (diameter 2), the Araujo-Pardo & Lopez record for
# d = q + 2, and the projective plane incidence graph.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# New construction: two-fibre voltage lifts over small groups, with a
# non-trivial base graph.
#
# Base graph: p A-vertices and p B-vertices (p = 1 or 2). Between A-fibre i
# and B-fibre j there is a set S_ij of distinct group elements. Vertices are
# (A, i, x) and (B, j, y) for x, y in G, and (A, i, x) ~ (B, j, x*g) for
# every g in S_ij. Degree d needs row and column sums of |S_ij| to equal d.
# For p = 2 the sizes are [[a, d-a], [d-a, a]].
#
# Left multiplication by h in G is an automorphism that preserves fibres,
# so diameter <= 3 can be tested with 2p breadth-first searches from the
# fibre identities. The cost is the number of unreached (source, vertex)
# pairs, and simulated annealing drives it to zero by changing one element
# of one S_ij at a time.
#
# p = 2 gives order 4N, which is above the record when N is in the window
# ceil((best+1)/4)..moore/4. This is a different family from the single
# bi-Cayley search (p = 1), which is kept as the second stage.
# ----------------------------------------------------------------------------

def _group_mul_table(N, spec):
    """Multiplication table M[x][y] for the group named by spec; identity is index 0."""
    if spec[0] == "cyc":
        _, mul, _ = lib.cyclic_group(N)
    else:
        _, a, k, r = spec
        _, mul, _ = lib.semidirect_group(a, k, r)
    return [[mul(x, y) for y in range(N)] for x in range(N)]


def _specs(N, rng, cap=8):
    """The cyclic group plus a sample of semidirect products Z_a x| Z_k of order N."""
    cands = []
    for k in range(2, N + 1):
        if N % k:
            continue
        a = N // k
        if a == 1:
            continue
        for r in range(1, a):
            if math.gcd(r, a) == 1 and pow(r, k, a) == 1:
                cands.append(("sd", a, k, r))
    rng.shuffle(cands)
    return [("cyc",)] + cands[:cap]


def _patterns(p, d, N):
    """Bucket-size patterns: dict (i, j) -> |S_ij| with row and column sums equal to d."""
    pats = []
    if p == 1:
        if d <= N:
            pats.append({(0, 0): d})
    else:
        for a in range(1, d):
            if a <= N and d - a <= N:
                pats.append({(0, 0): a, (0, 1): d - a, (1, 0): d - a, (1, 1): a})
    return pats


def _ball_len(adj, src, D):
    """Number of vertices within distance D of src."""
    seen = {src}
    frontier = [src]
    for _ in range(D):
        nxt = []
        for u in frontier:
            for w in adj[u]:
                if w not in seen:
                    seen.add(w)
                    nxt.append(w)
        frontier = nxt
        if not frontier:
            break
    return len(seen)


def _cost(N, p, mats, M):
    """Total number of unreached pairs from the 2p fibre identities (0 iff diameter <= 3)."""
    n = 2 * p * N
    adj = [[] for _ in range(n)]
    for (i, j), S in mats.items():
        base = p * N + j * N
        for x in range(N):
            u = i * N + x
            row = M[x]
            au = adj[u]
            for g in S:
                w = base + row[g]
                au.append(w)
                adj[w].append(u)
    total = 0
    for t in range(2 * p):
        total += n - _ball_len(adj, t * N, 3)
    return total


def _anneal(N, p, pat, M, rng, deadline, moves):
    """Find bucket sets with cost 0, or return None on failure or timeout."""
    mats = {k: rng.sample(range(N), s) for k, s in pat.items()}
    keys = list(mats.keys())
    cur = _cost(N, p, mats, M)
    for it in range(moves):
        if cur == 0:
            return mats
        if (it & 63) == 0 and time.monotonic() >= deadline:
            return None
        key = rng.choice(keys)
        S = mats[key]
        idx = rng.randrange(len(S))
        x = rng.randrange(N)
        if x in S:
            continue
        old = S[idx]
        S[idx] = x
        c = _cost(N, p, mats, M)
        T = 2.0 * (0.01 ** (it / moves))
        if c <= cur or rng.random() < math.exp((cur - c) / T):
            cur = c
        else:
            S[idx] = old
    return mats if cur == 0 else None


def _edges(N, p, mats, M):
    """Edge list for a lift: A(i, x) = i*N + x, B(j, y) = p*N + j*N + y."""
    E = []
    for (i, j), S in mats.items():
        base = p * N + j * N
        for x in range(N):
            u = i * N + x
            row = M[x]
            for g in S:
                E.append((u, base + row[g]))
    return 2 * p * N, E


def _search_task(N, p, d, rng, deadline):
    """Search all groups and patterns of order N for one (p, N) task; return (mats, M) or None."""
    specs = _specs(N, rng)
    pats = _patterns(p, d, N)
    if not pats:
        return None
    cache = {}
    k = 0
    while time.monotonic() < deadline:
        spec = specs[k % len(specs)]
        k += 1
        if spec not in cache:
            try:
                cache[spec] = _group_mul_table(N, spec)
            except Exception:
                cache[spec] = None
        M = cache[spec]
        if M is None:
            continue
        pat = pats[rng.randrange(len(pats))]
        mats = _anneal(N, p, pat, M, rng, deadline, 6000)
        if mats is not None:
            return mats, M
    return None


def _lift_search(d, best_n, rng, deadline):
    """Return (n, edges) for the largest valid lift found beyond best_n, or None."""
    moore = lib.moore_bound(d, 3)
    tasks = [(2, N) for N in range(best_n // 4 + 1, moore // 4 + 1)]
    tasks += [(1, N) for N in range(best_n // 2 + 1, moore // 2 + 1)]
    best = None
    bestn = best_n
    for idx, (p, N) in enumerate(tasks):
        now = time.monotonic()
        if now >= deadline:
            break
        if 2 * p * N <= bestn:
            continue
        left = len(tasks) - idx
        tdl = min(deadline, now + (deadline - now) / left)
        res = _search_task(N, p, d, rng, tdl)
        if res is not None:
            mats, M = res
            n, e = _edges(N, p, mats, M)
            if n > bestn and lib.is_valid(n, e, d, 3):
                bestn = n
                best = (n, e)
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.7 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2, valid for D >= 2.
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
        res = _lift_search(d, best[0], rng, deadline)
        if res is not None and res[0] > best[0] and lib.is_valid(res[0], res[1], d, D):
            best = res
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
