import math
import random
import time

import lib

SAFETY = 5.0          # seconds kept in reserve below time_limit
MAX_K = 30            # cover search only for modest degree (table size ~ m^2)
TEMP = 0.35           # annealing temperature for the difference-cover search


# ---------------------------------------------------------------- abelian groups

def _group(a, b):
    """Addition and negation tables for Z_a x Z_b, element (x, y) coded as x*b + y."""
    m = a * b
    xs = [divmod(i, b) for i in range(m)]
    A = [[0] * m for _ in range(m)]
    for i in range(m):
        x1, y1 = xs[i]
        row = A[i]
        for j in range(m):
            x2, y2 = xs[j]
            row[j] = ((x1 + x2) % a) * b + (y1 + y2) % b
    N = [((-x) % a) * b + (-y) % b for x, y in xs]
    return A, N


# ---------------------------------------------------------------- difference covers
# A set S in an abelian group G with S - S = G gives a bipartite Haar-type graph
# (a_g ~ b_{g+s}) with parts of size |G|, degree |S|, and diameter <= 3.

def _cover_search(m, A, N, k, rng, deadline):
    """Simulated annealing for a k-subset S of G (|G| = m) with S - S = G. Returns S or None."""
    S = [0] + rng.sample(range(1, m), k - 1)
    inS = [False] * m
    for s in S:
        inS[s] = True
    cnt = [0] * m
    for i in range(k):
        for j in range(k):
            if i != j:
                cnt[A[S[i]][N[S[j]]]] += 1
    unc = sum(1 for g in range(1, m) if cnt[g] == 0)
    steps = 0
    while unc > 0:
        steps += 1
        if (steps & 127) == 0 and time.monotonic() > deadline:
            return None
        i = rng.randrange(1, k)
        x = S[i]
        y = rng.randrange(1, m)
        if inS[y]:
            continue
        before = unc
        # remove x: drop its differences with the other members
        for j in range(k):
            if j == i:
                continue
            s = S[j]
            g = A[x][N[s]]
            cnt[g] -= 1
            if cnt[g] == 0:
                unc += 1
            g = A[s][N[x]]
            cnt[g] -= 1
            if cnt[g] == 0:
                unc += 1
        # add y: create its differences
        for j in range(k):
            if j == i:
                continue
            s = S[j]
            g = A[y][N[s]]
            if cnt[g] == 0:
                unc -= 1
            cnt[g] += 1
            g = A[s][N[y]]
            if cnt[g] == 0:
                unc -= 1
            cnt[g] += 1
        delta = unc - before
        if delta <= 0 or rng.random() < math.exp(-delta / TEMP):
            S[i] = y
            inS[x] = False
            inS[y] = True
        else:
            # revert the addition of y
            for j in range(k):
                if j == i:
                    continue
                s = S[j]
                g = A[y][N[s]]
                cnt[g] -= 1
                if cnt[g] == 0:
                    unc += 1
                g = A[s][N[y]]
                cnt[g] -= 1
                if cnt[g] == 0:
                    unc += 1
            # revert the removal of x
            for j in range(k):
                if j == i:
                    continue
                s = S[j]
                g = A[x][N[s]]
                if cnt[g] == 0:
                    unc -= 1
                cnt[g] += 1
                g = A[s][N[x]]
                if cnt[g] == 0:
                    unc -= 1
                cnt[g] += 1
    return S


def _find_cover(k, rng, deadline, lo, hi):
    """Try orders m from hi downwards (lo <= m) until a difference cover of size k is found."""
    m = hi
    while m >= lo:
        now = time.monotonic()
        remaining = deadline - now
        if remaining <= 0.2:
            break
        per = min(remaining, max(1.0, 1.5 * remaining / (m - lo + 1)))
        opts = [(x, m // x) for x in range(1, m + 1) if m % x == 0]
        a, b = rng.choice(opts)
        A, N = _group(a, b)
        S = _cover_search(m, A, N, k, rng, now + per)
        if S is not None:
            return m, A, N, S
        m -= 1
    return None


# ---------------------------------------------------------------- fallback constructions

def _pg_graph(d):
    """Incidence graph of PG(2,q), q the largest prime power <= d-1."""
    q = d - 1
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    if q < 2:
        return None
    return lib.projective_plane_incidence(q)


def _fallbacks(d, D):
    """Known constructions for this (d, D); each is verified by the caller."""
    out = []
    if D == 3:
        pg = _pg_graph(d)
        if pg is not None:
            out.append(pg)
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                out.append(lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass
    out.append(lib.haar_graph(d, range(d)))   # K_{d,d}, valid for every D >= 2
    return out


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - SAFETY))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:                                 # cycle of length 2D
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]
    if D == 2:                                 # K_{d,d} is extremal for D = 2
        return lib.haar_graph(d, range(d))
    if D == 3 and lib.is_prime_power(d - 1):   # Moore-extremal projective plane
        return lib.projective_plane_incidence(d - 1)

    cands = []
    for n, e in _fallbacks(d, D):
        if lib.is_valid(n, e, d, D):
            cands.append((n, e))
    if not cands:
        return lib.haar_graph(d, range(d))

    # Bold path: bi-Cayley (Haar-type) graphs over abelian groups with a difference cover.
    if D == 3 and 3 <= d <= MAX_K:
        best_v = max(n for n, _ in cands)
        hi = d * d - d + 1                     # largest group a difference cover can fill
        lo = max(d, best_v // 2 + 1)           # need 2m > best_v to improve
        if hi >= lo and time.monotonic() < deadline:
            res = _find_cover(d, rng, deadline, lo, hi)
            if res is not None:
                m, A, N, S = res
                edges = [(g, m + A[g][s]) for g in range(m) for s in S]
                if lib.is_valid(2 * m, edges, d, D):
                    cands.append((2 * m, edges))

    best = max(cands, key=lambda c: c[0])
    return best

