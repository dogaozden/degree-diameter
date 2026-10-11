import itertools
import math
import random
import time

import lib

WALKERS = 6          # (order, group) walkers annealed concurrently
ITERS = 600          # annealing steps per walker before it is reseeded
GROUPS_PER_N = 3     # groups tried for one order N in the first sweep (doubles each sweep)
STEPS_PER_TURN = 40  # annealing steps per walker per round-robin turn


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
# decide the diameter. Identity is WLOG in S.
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


def _new_walker(N, d, D, rng):
    """Create an annealing walker for order N with a random group and random connection set."""
    m, k, r = rng.choice(_groups(N))
    _, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(N)] for x in range(N)]
    invs = [inv(g) for g in range(N)]
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(N, T, invs, S, D)
    return {"N": N, "T": T, "invs": invs, "S": S, "cur": cur, "it": 0}


def _turn(w, d, D, rng, steps):
    """Advance one walker by up to `steps` simulated-annealing moves (state persists across turns)."""
    N = w["N"]
    for _ in range(steps):
        if w["cur"] == 0 or w["it"] >= ITERS:
            return
        w["it"] += 1
        temp = max(0.05, 2.0 * (1.0 - w["it"] / ITERS))
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        S = w["S"]
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, w["T"], w["invs"], S2, D)
        if v <= w["cur"] or rng.random() < math.exp(-(v - w["cur"]) / temp):
            w["S"], w["cur"] = S2, v


def _sweep(d, D, top, solved, limit, rng, deadline, consider):
    """Interleave walkers over orders N from top downward; return the largest order solved."""
    walkers = []
    used = {}
    best = solved
    next_N = top

    def fresh(N):
        used[N] = used.get(N, 0) + 1
        return _new_walker(N, d, D, rng)

    while time.monotonic() < deadline:
        # Refill the pool with the next (largest remaining) orders above the best solved one.
        while len(walkers) < WALKERS and next_N > max(d, best):
            walkers.append(fresh(next_N))
            next_N -= 1
        if not walkers:
            break
        survivors = []
        for w in walkers:
            if w["N"] <= best:
                continue  # superseded: only larger orders can improve the result
            if time.monotonic() >= deadline:
                return best
            _turn(w, d, D, rng, STEPS_PER_TURN)
            if w["cur"] == 0:
                N, T, S = w["N"], w["T"], w["S"]
                consider(2 * N, [(x, N + T[x][g]) for x in range(N) for g in S])
                best = max(best, N)
            elif w["it"] >= ITERS:
                if used.get(w["N"], 0) < limit:
                    survivors.append(fresh(w["N"]))
            else:
                survivors.append(w)
        walkers = survivors
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
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

    if D >= 2 and d >= 1:
        consider(*lib.haar_graph(d, range(d)))
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if d < 2 or D < 2:
        return best

    Nmax = lib._moore_bound(d, D) // 2   # bi-Cayley graph has 2N vertices
    top = min(Nmax, Nmax // 2 + 3)

    solved = best_n // 2 if best_n > 1 else d
    solved = max(solved, d)
    limit = GROUPS_PER_N
    # Repeated sweeps with a doubling group budget: each sweep resumes the search
    # from fresh groups for the orders still above the best solved one.
    while time.monotonic() < deadline and top > solved:
        solved = _sweep(d, D, top, solved, limit, rng, deadline, consider)
        limit *= 2

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best

