import itertools
import math
import random
import time

import lib

MAX_GROUPS = 40      # groups tried per order N within one attempt
TABU_STEPS = 500     # tabu moves per group before giving up on it
SAMPLE = 40          # random single-element swaps evaluated per tabu move
TENURE = 12          # steps a removed connection element stays forbidden
STAGNATION = 150     # non-improving moves before a random restart of S
TOP_SLACK = 10       # search orders up to Nmax//2 + TOP_SLACK
WINDOW = 25          # ladder starts this far below the top candidate


# ----------------------------------------------------------------------------
# Baseline families (fast, always valid when they pass lib.is_valid).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley search over semidirect products Z_m x| Z_k of order N.
#
# Vertices A_x and B_y (x, y in G). Edge A_x -- B_{x s} for s in S, |S| = d.
# Left multiplication is an automorphism, so eccentricities from A_0 and B_0
# decide the diameter. Identity is WLOG in S (right translation relabels B).
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


def _tabu(N, T, invs, d, D, rng, deadline):
    """Tabu search over S = {0, s_1, ..., s_{d-1}}.

    Each step samples random single-element swaps, takes the best non-tabu one
    (even if it worsens the cost), and forbids re-inserting the removed element
    for TENURE steps. A long stall triggers a fresh random S.
    """
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(N, T, invs, S, D)
    best = cur
    since = 0
    tabu_until = [0] * N
    it = 0
    while it < TABU_STEPS and cur > 0:
        if time.monotonic() > deadline:
            return None
        in_S = set(S)
        move, mval = None, None
        for _ in range(SAMPLE):
            i = rng.randrange(1, d)
            c = rng.randrange(1, N)
            if c in in_S:
                continue
            S2 = S[:]
            S2[i] = c
            v = _unreached(N, T, invs, S2, D)
            if tabu_until[c] > it and v >= best:   # aspiration: allow if new best
                continue
            if mval is None or v < mval:
                move, mval = (i, c), v
        it += 1
        if move is None:
            continue
        i, c = move
        tabu_until[S[i]] = it + TENURE
        S[i] = c
        cur = mval
        if cur < best:
            best, since = cur, 0
        else:
            since += 1
        if since > STAGNATION and cur > 0:
            S = [0] + rng.sample(range(1, N), d - 1)
            cur = _unreached(N, T, invs, S, D)
            best, since = cur, 0
            tabu_until = [0] * N
    return S if cur == 0 else None


def _search(N, d, D, rng, deadline):
    """Try random groups of order N with tabu search; return (T, S) on success."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        _, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        S = _tabu(N, T, invs, d, D, rng, deadline)
        if S is not None:
            return T, S
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = (1, [])
    best_n = 1

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Record-matching case: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best

    if D >= 2:
        consider(*lib.haar_graph(d, range(d)))
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D == 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if d < 2 or D < 2:
        return best

    Nmax = lib._moore_bound(d, D) // 2   # bi-Cayley graph has 2N vertices
    hi = min(Nmax, Nmax // 2 + TOP_SLACK)
    # Ladder: start a window below the top, just above what we already have.
    lo = max(best_n // 2 + 1, hi - WINDOW, d + 1)
    if lo <= hi:
        cands = list(range(lo, hi + 1))
    else:
        cands = list(range(hi, d, -1))

    budget = 1.0
    while time.monotonic() < deadline and cands:
        progressed = False
        for N in cands:
            now = time.monotonic()
            if now >= deadline:
                break
            res = _search(N, d, D, rng, min(deadline, now + budget))
            if res is not None:
                T, S = res
                edges = [(x, N + T[x][g]) for x in range(N) for g in S]
                consider(2 * N, edges)
                # Only larger orders can improve now.
                cands = [M for M in range(N + 1, hi + 1)]
                progressed = True
                break
        if not progressed:
            budget *= 1.5

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
