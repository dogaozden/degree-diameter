import math
import random
import time

import lib

# ----------------------------------------------------------------------------
# Construction A (D = 3): Haar-type graphs over finite groups.
#
# For a group G of order m and a k-subset S with 1 in S, let H(G,S) be the
# bipartite graph with parts {a_x} and {b_y}, x,y in G, and a_x ~ b_{xs} for s in S.
# It is k-regular, has 2m vertices, and has diameter 3 exactly when
#     S S^{-1} = G   (A-A pairs at distance 2)
#     S^{-1} S = G   (B-B pairs at distance 2)
# Mixed pairs are then within distance 3. Both conditions are needed for
# non-abelian G. Since 1 is in S, we only search over the other k-1 elements.
# The search is an annealing on the number of uncovered group elements, and it
# runs over many groups Z_a x| Z_k of each order m.
# Moore-type cap: m <= k(k-1)+1.
# ----------------------------------------------------------------------------


def _group_params(m, rng):
    """Candidate groups of order m as (a, kk, r): Z_a x|_r Z_kk, with the cyclic group first."""
    out = [(m, 1, 1)]
    others = []
    for kk in range(2, m + 1):
        if m % kk:
            continue
        a = m // kk
        if a < 2:
            continue
        for r in range(1, a):
            if math.gcd(r, a) == 1 and pow(r, kk, a) == 1 % a:
                others.append((a, kk, r))
    rng.shuffle(others)
    others.sort(key=lambda t: t[2] == 1)  # non-abelian (r != 1) first
    return out + others[:2]


def _group_tables(a, kk, r):
    """Multiplication and inverse tables of the group with elements coded 0..m-1 (identity 0)."""
    order, mul, inv = lib.semidirect_group(a, kk, r)
    M = [[mul(x, y) for y in range(order)] for x in range(order)]
    iv = [inv(x) for x in range(order)]
    return M, iv


def _anneal(M, iv, m, k, rng, deadline):
    """Find S = {0} + (k-1 elements) with S S^{-1} = G and S^{-1} S = G, or return None."""
    S = [0] + rng.sample(range(1, m), k - 1)
    c1 = [0] * m  # counts of u v^{-1}, u != v
    c2 = [0] * m  # counts of u^{-1} v, u != v
    for u in S:
        for v in S:
            if u != v:
                c1[M[u][iv[v]]] += 1
                c2[M[iv[u]][v]] += 1
    unc = sum(1 for g in range(1, m) if c1[g] == 0) + sum(1 for g in range(1, m) if c2[g] == 0)
    T = 0.4
    it = 0
    while unc > 0:
        it += 1
        if (it & 255) == 0 and time.monotonic() > deadline:
            return None
        i = rng.randrange(1, k)
        x = S[i]
        y = rng.randrange(1, m)
        if y in S:
            continue
        others = [S[j] for j in range(k) if j != i]
        delta = 0
        for t in others:
            for u, v in ((x, t), (t, x)):
                a = M[u][iv[v]]
                b = M[iv[u]][v]
                c1[a] -= 1
                if c1[a] == 0:
                    delta += 1
                c2[b] -= 1
                if c2[b] == 0:
                    delta += 1
        for t in others:
            for u, v in ((y, t), (t, y)):
                a = M[u][iv[v]]
                b = M[iv[u]][v]
                if c1[a] == 0:
                    delta -= 1
                c1[a] += 1
                if c2[b] == 0:
                    delta -= 1
                c2[b] += 1
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S[i] = y
            unc += delta
        else:
            for t in others:
                for u, v in ((y, t), (t, y)):
                    c1[M[u][iv[v]]] -= 1
                    c2[M[iv[u]][v]] -= 1
            for t in others:
                for u, v in ((x, t), (t, x)):
                    c1[M[u][iv[v]]] += 1
                    c2[M[iv[u]][v]] += 1
    return S


def _group_graph(m, M, S):
    """Haar-type graph: a_x ~ b_{x s} for x in G, s in S. Returns (2m, edges)."""
    E = []
    for x in range(m):
        Mx = M[x]
        for s in S:
            E.append((x, m + Mx[s]))
    return 2 * m, E


def _group_search(d, base_n, deadline, rng):
    """Search groups of order m (descending, m > base_n/2) for a k-element difference cover."""
    k = d
    hi = k * (k - 1) + 1
    lo = base_n // 2 + 1
    if hi < lo:
        return None
    cands = []
    for m in range(hi, lo - 1, -1):
        for a, kk, r in _group_params(m, rng):
            cands.append((m, a, kk, r))
    tabs = {}
    best = None
    slice_ = 0.1
    while time.monotonic() < deadline:
        for m, a, kk, r in cands:
            if best is not None and m <= best[0]:
                continue
            now = time.monotonic()
            if now >= deadline:
                return best
            key = (a, kk, r)
            if key not in tabs:
                tabs[key] = _group_tables(a, kk, r)
            M, iv = tabs[key]
            S = _anneal(M, iv, m, k, rng, min(deadline, now + slice_))
            if S is not None:
                n, E = _group_graph(m, M, S)
                best = (m, n, E)
                if m == hi:
                    return best
        slice_ *= 2
    return best


# ----------------------------------------------------------------------------
# Construction B (D = 3): projective plane incidence with a conic arc attached.
# Uses the spare degree s = d - q - 1 of PG(2,q) to add 2k vertices.
# ----------------------------------------------------------------------------

def _arc_graph(q, d):
    """PG(2,q) incidence graph plus an A/B pair for each point of a small arc. Returns (n, edges) or None."""
    n2, E = lib.projective_plane_incidence(q)
    m = n2 // 2
    s = d - q - 1
    if s < 0:
        return None
    if s == 0:
        return n2, E
    if s == 1:
        S = [0]
    else:
        F = lib.GF(q)
        index = {p: i for i, p in enumerate(lib.projective_points(q))}
        S = [index[(1, t, F.mul(t, t))] for t in range(q)] + [index[(0, 0, 1)]]
        if q % 2 == 0:
            S.append(index[(0, 1, 0)])
    lines_of = [[] for _ in range(m)]
    pts_of = [[] for _ in range(m)]
    for u, v in E:
        lines_of[u].append(v - m)
        pts_of[v - m].append(u)
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in lines_of[P]:
            cl[L] += 1
        for Q in pts_of[P]:
            cp[Q] += 1
    if max(cl) > s or max(cp) > s:
        return None
    kk = len(S)
    base = 2 * m
    out = list(E)
    for t, P in enumerate(S):
        for L in lines_of[P]:
            out.append((base + t, m + L))
    for t, j in enumerate(S):
        for Q in pts_of[j]:
            out.append((Q, base + kk + t))
    return base + 2 * kk, out


# ----------------------------------------------------------------------------
# Entry point
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + min(0.7 * float(time_limit), 40.0)
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    rng = random.Random(seed * 1000003 + 17 * d + D)

    # Safe fallback: K_{d,d} has diameter 2.
    best_n, best_E = lib.haar_graph(d, range(d))

    def consider(n, E):
        nonlocal best_n, best_E
        if n > best_n and lib.is_valid(n, E, d, D):
            best_n, best_E = n, list(E)

    if D >= 3:
        for q in range(2, d):
            if lib.is_prime_power(q) and q + 1 <= d:
                res = _arc_graph(q, d)
                if res is not None:
                    consider(res[0], res[1])
        if d >= 2 and time.monotonic() < deadline:
            res = _group_search(d, best_n, deadline, rng)
            if res is not None:
                consider(res[1], res[2])

    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, list(best_E)
