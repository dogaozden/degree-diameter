import math
import random
import time

import lib

TIME_FRAC = 0.85     # fraction of time_limit used before returning
MARGIN = 2.0         # seconds kept in reserve
STEPS = 40000        # annealing moves per attempt
ATTEMPTS = 8         # attempts per group order m
MAX_FAILS = 3        # consecutive failed orders m before stopping


# ---------------------------------------------------------------- fallback bases

def _pg_base(d):
    """Incidence graph of PG(2,q), q the largest prime power <= d-1 (diameter 3, degree <= d)."""
    q = d - 1
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    if q < 2:
        return None
    return lib.projective_plane_incidence(q)


# ---------------------------------------------------------------- bi-Cayley search (D = 3)
#
# Group G of order m, connection set S of size d containing the identity.
# Graph: a_x ~ b_{x*s} for s in S (x in G).  The graph is d-regular and bipartite.
# a-a and b-b distances are <= 2 exactly when S S^{-1} = G and S^{-1} S = G;
# a-b distances are then <= 3.  So D = 3 holds iff both sets cover G.
# The search keeps coverage counts and updates them in O(d) per move.

def _cover_pairs(x, others, M, I):
    """Products involving element x, given the other elements of S."""
    ix = I[x]
    p1 = [M[x][I[b]] for b in others]     # x * b^{-1}
    p1.append(0)                          # x * x^{-1}
    p1.extend(M[a][ix] for a in others)   # a * x^{-1}
    p2 = [M[ix][b] for b in others]       # x^{-1} * b
    p2.append(0)                          # x^{-1} * x
    p2.extend(M[I[a]][x] for a in others) # a^{-1} * x
    return p1, p2


def _bump(cnt, gs, step):
    """Add (+1) or remove (-1) the products gs; return the change in the number of uncovered elements."""
    ch = 0
    if step > 0:
        for g in gs:
            cnt[g] += 1
            if cnt[g] == 1:
                ch -= 1
    else:
        for g in gs:
            cnt[g] -= 1
            if cnt[g] == 0:
                ch += 1
    return ch


def _search(order, M, I, d, rng, steps, deadline):
    """Simulated annealing for a covering set S (size d, identity included). Returns S or None."""
    S = [0] + rng.sample(range(1, order), d - 1)
    inS = set(S)
    cnt1 = [0] * order
    cnt2 = [0] * order
    for a in S:
        for b in S:
            cnt1[M[a][I[b]]] += 1
            cnt2[M[I[a]][b]] += 1
    unc = sum(1 for c in cnt1 if c == 0) + sum(1 for c in cnt2 if c == 0)
    if unc == 0:
        return S
    for it in range(steps):
        if it % 2000 == 0 and time.monotonic() > deadline:
            return None
        i = rng.randrange(1, d)          # keep the identity at position 0
        y = rng.randrange(1, order)
        if y in inS:
            continue
        old = S[i]
        others = S[:i] + S[i + 1:]
        o1, o2 = _cover_pairs(old, others, M, I)
        delta = _bump(cnt1, o1, -1) + _bump(cnt2, o2, -1)
        n1, n2 = _cover_pairs(y, others, M, I)
        delta += _bump(cnt1, n1, 1) + _bump(cnt2, n2, 1)
        T = 1.0 * (1.0 - it / steps) + 0.05
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            unc += delta
            S[i] = y
            inS.discard(old)
            inS.add(y)
            if unc == 0:
                return S
        else:
            _bump(cnt1, n1, -1)
            _bump(cnt2, n2, -1)
            _bump(cnt1, o1, 1)
            _bump(cnt2, o2, 1)
    return None


def _tables(m, rng):
    """Multiplication/inverse tables for a few groups of order m: cyclic plus up to 3 metacyclic."""
    cands = [lib.cyclic_group(m)]
    nonab = []
    for k in range(2, m):
        if m % k:
            continue
        a = m // k
        if a < 2:
            continue
        for r in range(2, a):
            if math.gcd(r, a) == 1 and pow(r, k, a) == 1 % a:
                nonab.append((a, k, r))
                break
    rng.shuffle(nonab)
    for a, k, r in nonab[:3]:
        cands.append(lib.semidirect_group(a, k, r))
    out = []
    for order, mul, inv in cands:
        M = [[mul(x, y) for y in range(order)] for x in range(order)]
        I = [inv(x) for x in range(order)]
        out.append((order, M, I))
    return out


def _grow(base_n, d, D, rng, deadline):
    """Find the largest m (order of G, graph order 2m) for which a covering S is found. Returns (n, edges) or None."""
    best = None
    m = base_n // 2 + 1
    mmax = d * (d - 1) + 1          # Moore bound for this construction
    fails = 0
    while m <= mmax and time.monotonic() < deadline and fails < MAX_FAILS:
        tables = _tables(m, rng)
        found = None
        for att in range(ATTEMPTS):
            if time.monotonic() > deadline:
                break
            order, M, I = tables[att % len(tables)]
            S = _search(order, M, I, d, rng, STEPS, deadline)
            if S is None:
                continue
            edges = [(x, m + M[x][s]) for x in range(m) for s in S]
            if lib.is_valid(2 * m, edges, d, D):
                found = (2 * m, edges)
                break
        if found is not None:
            best = found
            fails = 0
        else:
            fails += 1
        m += 1
    return best


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, TIME_FRAC * time_limit - MARGIN)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:                       # cycle of length 2D: bipartite, diameter D
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]
    if D == 2:                       # K_{d,d} is extremal for D = 2
        return lib.haar_graph(d, range(d))
    if D == 3 and lib.is_prime_power(d - 1):   # Moore-extremal projective plane
        return lib.projective_plane_incidence(d - 1)

    # Safe starting candidates (all have diameter 3, so valid for any D >= 3).
    bases = []
    pg = _pg_base(d)
    if pg is not None:
        bases.append(pg)
    if d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            bases.append(lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass
    kdd = lib.haar_graph(d, range(d))
    bases.append(kdd)
    valid = [(n, e) for n, e in bases if lib.is_valid(n, e, d, D)]
    if not valid:
        return kdd
    base_n, base_e = max(valid, key=lambda c: c[0])

    # Bold path for D = 3: bi-Cayley graphs over small groups, searched for larger order.
    if D == 3 and d >= 3:
        try:
            res = _grow(base_n, d, D, rng, deadline)
            if res is not None and res[0] > base_n and lib.is_valid(res[0], res[1], d, D):
                return res
        except Exception:
            pass

    return base_n, base_e
