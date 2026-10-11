import itertools
import math
import random
import time

import lib

MAX_RUN = 8.0  # seconds allotted to a single annealing run


# ----------------------------------------------------------------------------
# Structured baselines (used as safe starting points and for D = 3 / D >= 4).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Points and lines of the generalized quadrangle W(q); bipartite, diameter 4."""
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
    """W(q) for the largest prime power q with q + 1 <= d, capped at q = 5."""
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Multi-base voltage lifts over finite groups, found by simulated annealing.
#
# Vertices: A-side (i, g) -> i*G + g,  B-side (j, h) -> (k+j)*G + h,  i, j < k.
# Layer L (L < d) is a permutation p_L of the k base indices with a voltage
# s_{L,i} per A-base vertex: A(i, g) ~ B(p_L(i), g * s_{L,i}).
# Every vertex then has degree d, the graph is bipartite by construction, and
# the group acts by left multiplication, so only the k A- and k B-base vertices
# need to be checked for eccentricity.
# ----------------------------------------------------------------------------

def _groups(N):
    """Semidirect-product parameters (m, k, r) giving groups Z_m x|_r Z_k of order N."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _right_table(order, mul):
    """table[s][g] = g * s, so table[s] is the right-translation permutation by s."""
    return [[mul(g, s) for g in range(order)] for s in range(order)]


def _build_adj(k, G, d, st, table):
    """Adjacency lists (with possible repeats, harmless for distances) of the lift."""
    N2 = 2 * k * G
    adj = [[] for _ in range(N2)]
    for L in range(d):
        row_st = st[L]
        for i in range(k):
            j, s = row_st[i]
            tr = table[s]
            base_a = i * G
            base_b = (k + j) * G
            for g in range(G):
                a = base_a + g
                b = base_b + tr[g]
                adj[a].append(b)
                adj[b].append(a)
    return adj


def _cost(N2, adj, D, reps):
    """Number of (representative, vertex) pairs at distance > D, via bitset balls."""
    ball = [1 << v for v in range(N2)]
    for _ in range(D):
        nxt = [0] * N2
        for v in range(N2):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            nxt[v] = x
        ball = nxt
    return sum(N2 - ball[r].bit_count() for r in reps)


def _anneal(d, D, k, G, table, rng, deadline):
    """Anneal voltages and base permutations until every representative reaches all vertices in D steps."""
    N2 = 2 * k * G
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]

    st = []
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        st.append([[p[i], rng.randrange(G)] for i in range(k)])

    cost = _cost(N2, _build_adj(k, G, d, st, table), D, reps)
    start = time.monotonic()
    span = max(1e-3, deadline - start)

    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        T = max(0.05, 2.0 * (1.0 - (now - start) / span))
        L = rng.randrange(d)

        if k > 1 and rng.random() < 0.3:
            # Swap the B-targets of two base vertices within one layer (keeps a permutation).
            a, b = rng.sample(range(k), 2)
            ca, cb = st[L][a], st[L][b]
            ca[0], cb[0] = cb[0], ca[0]
            c2 = _cost(N2, _build_adj(k, G, d, st, table), D, reps)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                ca[0], cb[0] = cb[0], ca[0]
        else:
            # Re-randomize one voltage.
            i = rng.randrange(k)
            cell = st[L][i]
            old = cell[1]
            new = rng.randrange(G)
            if new == old:
                continue
            cell[1] = new
            c2 = _cost(N2, _build_adj(k, G, d, st, table), D, reps)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                cell[1] = old

    if cost != 0:
        return None
    E = set()
    for L in range(d):
        for i in range(k):
            j, s = st[L][i]
            tr = table[s]
            for g in range(G):
                E.add((i * G + g, (k + j) * G + tr[g]))
    return N2, sorted(E)


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d}: bipartite, degree d, diameter 2. Safe fallback for every D >= 2.
    fallback = lib.haar_graph(d, range(d))
    best_n, best_e = fallback[0], list(fallback[1])
    if D == 2:
        return best_n, best_e

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)
            return True
        return False

    moore = lib.moore_bound(d, D)

    # Structured baselines (wrapped so that any failure falls back safely).
    try:
        if D == 3:
            if lib.is_prime_power(d - 1):
                n, e = lib.projective_plane_incidence(d - 1)
                consider(n, e)
                return best_n, best_e
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])
        if D >= 4:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq[0], gq[1])
    except Exception:
        pass

    # Main search: annealed multi-base lifts over varied groups, aiming above best_n.
    while time.monotonic() < deadline and best_n < moore:
        try:
            k = rng.choice((1, 2, 2, 3, 3, 4))
            G = best_n // (2 * k) + 1 + rng.randrange(3)
            if 2 * k * G > moore:
                continue
            groups = _groups(G)
            if not groups:
                continue
            m, k2, r = rng.choice(groups)
            order, mul, _ = lib.semidirect_group(m, k2, r)
            table = _right_table(order, mul)
            run_deadline = min(deadline, time.monotonic() + MAX_RUN)
            res = _anneal(d, D, k, order, table, rng, run_deadline)
            if res is not None:
                consider(res[0], res[1])
        except Exception:
            continue

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = fallback[0], list(fallback[1])
    return best_n, best_e
