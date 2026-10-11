import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Generalized quadrangle baseline (D >= 4), carried over from the parent.
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
# New construction for D = 3: bi-Cayley graphs over NON-ABELIAN groups.
#
# For a finite group G of order n and a k-subset S of G, let the bipartite
# graph have parts A = G and B = G with a_x ~ b_{x s} for s in S. (This is
# lib.group_lift(2, [(0,1,s)...], n, mul).) It is k-regular and bipartite.
#
#   A-A distance <= 2  <=>  S S^{-1} = G       (every element a difference)
#   B-B distance <= 2  <=>  S^{-1} S = G
#   mixed distance <= 3 follows from S S^{-1} = G, since then S S^{-1} S = G.
#
# So diameter 3 holds exactly when both two-sided covers hold. Cyclic groups
# (difference covers) are the parent's search. Semidirect products
# Z_m x|_r Z_k give other group structures of the same order, and each one
# is a separate search space. We search over (group, S) with simulated
# annealing on the number of uncovered elements, using incremental counts
# c1[g] = #{(s,t): s t^{-1} = g} and c2[g] = #{(s,t): s^{-1} t = g}.
# Each order n is tried across several groups, and n is climbed upward.
# ----------------------------------------------------------------------------

def _divisors(n):
    return [k for k in range(1, n + 1) if n % k == 0]


def _groups_of_order(n, rng, cap=4):
    """Candidate groups of order n: cyclic Z_n first, then sampled semidirect products Z_m x|_r Z_k."""
    out = [lib.cyclic_group(n)]
    extra = []
    for k in _divisors(n):
        if k < 2:
            continue
        m = n // k
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) != 1 or pow(r, k, m) != 1 % m:
                continue
            if r == 1 and math.gcd(m, k) == 1:
                continue  # direct product is cyclic, already covered
            extra.append((m, k, r))
    rng.shuffle(extra)
    for m, k, r in extra:
        if len(out) >= cap:
            break
        try:
            out.append(lib.semidirect_group(m, k, r))
        except ValueError:
            pass
    return out


def _tables(order, mul, inv):
    P = [[mul(x, y) for y in range(order)] for x in range(order)]
    I = [inv(x) for x in range(order)]
    return P, I


def _anneal(k, order, P, I, rng, deadline):
    """Find a k-subset S of the group with S S^{-1} = G and S^{-1} S = G, or None at the deadline."""
    BIG = 1 << 30
    S = rng.sample(range(order), k)
    in_s = set(S)
    c1 = [0] * order
    c2 = [0] * order
    for a in S:
        for b in S:
            c1[P[a][I[b]]] += 1
            c2[P[I[a]][b]] += 1
    # Identity is always covered; BIG keeps index 0 from ever transitioning.
    c1[0] += BIG
    c2[0] += BIG
    unc = sum(1 for g in range(1, order) if c1[g] == 0) + \
          sum(1 for g in range(1, order) if c2[g] == 0)

    T = 1.0
    it = 0
    while unc > 0:
        it += 1
        if (it & 2047) == 0 and time.monotonic() > deadline:
            return None
        if it % 400000 == 0:
            T = 1.0
        T = max(0.06, T * 0.99998)
        i = rng.randrange(k)
        x = S[i]
        y = rng.randrange(order)
        if y in in_s:
            continue
        others = S[:i] + S[i + 1:]
        Ix = I[x]
        Iy = I[y]
        delta = 0
        # Remove x: pairs (s,x), (x,s) for every other s.
        for s in others:
            Is = I[s]
            for g in (P[s][Ix], P[x][Is]):
                c1[g] -= 1
                if c1[g] == 0:
                    delta += 1
            for g in (P[Is][x], P[Ix][s]):
                c2[g] -= 1
                if c2[g] == 0:
                    delta += 1
        # Add y: pairs (s,y), (y,s).
        for s in others:
            Is = I[s]
            for g in (P[s][Iy], P[y][Is]):
                if c1[g] == 0:
                    delta -= 1
                c1[g] += 1
            for g in (P[Is][y], P[Iy][s]):
                if c2[g] == 0:
                    delta -= 1
                c2[g] += 1

        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S[i] = y
            in_s.discard(x)
            in_s.add(y)
            unc += delta
        else:
            # Undo addition of y, then undo removal of x.
            for s in others:
                Is = I[s]
                for g in (P[s][Iy], P[y][Is]):
                    c1[g] -= 1
                for g in (P[Is][y], P[Iy][s]):
                    c2[g] -= 1
            for s in others:
                Is = I[s]
                for g in (P[s][Ix], P[x][Is]):
                    c1[g] += 1
                for g in (P[Is][x], P[Ix][s]):
                    c2[g] += 1
    return sorted(S)


def _search_order(k, n, deadline, rng, slice_t):
    """Try several groups of order n; return (order, S, mul) for the first success, else None."""
    for order, mul, inv in _groups_of_order(n, rng):
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            return None
        P, I = _tables(order, mul, inv)
        stop = time.monotonic() + min(slice_t, remaining)
        S = _anneal(k, order, P, I, rng, min(deadline, stop))
        if S is not None:
            return order, S, mul
    return None


def _d3_search(k, deadline, rng):
    """Climb the group order n upward from a high start; return the largest (order, S, mul) found."""
    hi = k * (k - 1) + 1  # Moore-type cap for a two-sided cover of size k
    lo = max(k, int(0.8 * hi))
    best = None
    n = lo
    fails = 0
    slice_t = 3.0
    while n <= hi and time.monotonic() < deadline:
        res = _search_order(k, n, deadline, rng, slice_t)
        if res is not None:
            best = res
            n += 1
            fails = 0
            slice_t = 3.0
        else:
            fails += 1
            slice_t *= 2.0
            if fails >= 3:
                break
    return best


# ----------------------------------------------------------------------------
# Entry point
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best_n, best_E = lib.haar_graph(d, range(d))
    if D == 2:
        return best_n, list(best_E)

    deadline = t0 + min(0.7 * float(time_limit), 40.0)
    rng = random.Random(seed * 1000003 + 31 * d + D)

    if D == 3:
        res = _d3_search(d, deadline, rng)
        if res is not None:
            order, S, mul = res
            n, E = lib.group_lift(2, [(0, 1, s) for s in S], order, mul)
            if n > best_n and lib.is_valid(n, E, d, D):
                best_n, best_E = n, E
    elif time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None and gq[0] > best_n and lib.is_valid(gq[0], gq[1], d, D):
            best_n, best_E = gq

    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, list(best_E)
