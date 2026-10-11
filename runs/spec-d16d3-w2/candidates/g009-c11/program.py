import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# D = 3: bi-Cayley graphs over groups, found by searching for "difference covers".
#
# Let G be a finite group of order m and S a k-subset of G. The bi-Cayley graph
# has parts A = G and B = G, with a_x ~ b_{xs} for s in S. It is k-regular and
# bipartite. Two A-vertices a_x, a_y have a common neighbour iff y^{-1}x = t s^{-1}
# for some s != t in S, so A-A distances are <= 2 iff S S^{-1} covers G. The same
# condition gives A-B distances <= 3, since G = G S. So the graph has diameter 3
# iff S S^{-1} = G, and its order is 2m <= 2(k^2 - k + 1).
#
# The new ingredient is that G is not restricted to cyclic groups. We also use
# semidirect products Z_a x| Z_b (lib.semidirect_group), which give more group
# structures to search over. For each candidate order m we pick a random group
# of that order and anneal S to minimise the number of uncovered elements.
# ----------------------------------------------------------------------------

def _groups_for(m):
    """Descriptors (a, b, r) for groups Z_a x| Z_b of order m; (m, 1, 1) is the cyclic group."""
    out = [(m, 1, 1)]
    for b in range(2, m):
        if m % b:
            continue
        a = m // b
        if a < 2:
            continue
        for r in range(1, a):
            if math.gcd(r, a) == 1 and pow(r, b, a) == 1 % a:
                out.append((a, b, r))
    return out


def _diff_table(m, mul, inv):
    """DT[t][s] = t * s^{-1} as a table, so the cover search uses plain indexing."""
    invl = [inv(s) for s in range(m)]
    return [[mul(t, invl[s]) for s in range(m)] for t in range(m)]


def _cover_search(k, m, DT, rng, deadline):
    """Find S subset of G (|S| = k) with S S^{-1} = G, by annealing on the uncovered count."""
    S = rng.sample(range(m), k)
    in_s = set(S)
    cnt = [0] * m
    for i in range(k):
        for j in range(k):
            if i != j:
                cnt[DT[S[i]][S[j]]] += 1
    # Identity is always covered by the pair (s, s), so only non-identity elements count.
    unc = sum(1 for g in range(1, m) if cnt[g] == 0)
    T = 1.0
    it = 0
    while unc > 0:
        it += 1
        if (it & 1023) == 0 and time.monotonic() > deadline:
            return None
        if it % 200000 == 0:
            T = 0.8
        T = max(0.05, T * 0.99995)
        i = rng.randrange(k)
        x = S[i]
        y = rng.randrange(m)
        if y in in_s:
            continue
        others = S[:i] + S[i + 1:]
        old = unc
        # Remove x: drop the differences that involve x.
        for s in others:
            g = DT[x][s]
            cnt[g] -= 1
            if cnt[g] == 0:
                unc += 1
            g = DT[s][x]
            cnt[g] -= 1
            if cnt[g] == 0:
                unc += 1
        # Add y: add the differences that involve y.
        for s in others:
            g = DT[y][s]
            if cnt[g] == 0:
                unc -= 1
            cnt[g] += 1
            g = DT[s][y]
            if cnt[g] == 0:
                unc -= 1
            cnt[g] += 1
        delta = unc - old
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S[i] = y
            in_s.discard(x)
            in_s.add(y)
        else:
            # Roll back the addition, then the removal.
            for s in others:
                cnt[DT[y][s]] -= 1
                cnt[DT[s][y]] -= 1
            for s in others:
                cnt[DT[x][s]] += 1
                cnt[DT[s][x]] += 1
            unc = old
    return sorted(S)


def _group_search(k, rng, deadline):
    """Scan orders m from 0.78*mmax up to mmax = k(k-1)+1; each m gets a random group and a time slice.

    Returns (m, desc, S) for the largest m that succeeded, or None.
    """
    mmax = k * (k - 1) + 1
    m_lo = max(k, int(0.78 * mmax))
    ms = list(range(m_lo, mmax + 1))
    best = None
    for idx, m in enumerate(ms):
        now = time.monotonic()
        if now >= deadline:
            break
        remaining = deadline - now
        left = len(ms) - idx
        slice_ = min(remaining, max(0.3, 1.5 * remaining / left))
        desc = rng.choice(_groups_for(m))
        a, b, r = desc
        _, mul, inv = lib.semidirect_group(a, b, r)
        DT = _diff_table(m, mul, inv)
        S = _cover_search(k, m, DT, rng, min(deadline, now + slice_))
        if S is not None:
            best = (m, desc, S)
    return best


# ----------------------------------------------------------------------------
# Generalized quadrangle baseline (D = 4)
# ----------------------------------------------------------------------------

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
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Entry point
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = min(0.75 * float(time_limit), 45.0)
    deadline = start + budget
    rng = random.Random(seed * 1000003 + 17 * d + D)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best_n, best_E = lib.haar_graph(d, range(d))

    def consider(n, E):
        nonlocal best_n, best_E
        if n > best_n and lib.is_valid(n, E, d, D):
            best_n, best_E = n, list(E)

    if D == 3 and d >= 2:
        res = _group_search(d, rng, start + 0.9 * budget)
        if res is not None:
            m, desc, S = res
            a, b, r = desc
            _, mul, _ = lib.semidirect_group(a, b, r)
            E = [(x, m + mul(x, s)) for x in range(m) for s in S]
            consider(2 * m, E)

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, list(best_E)
