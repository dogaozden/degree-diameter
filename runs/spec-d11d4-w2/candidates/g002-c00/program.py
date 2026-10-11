import itertools
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q): points 0..P-1, totally isotropic lines as point lists.
# ----------------------------------------------------------------------------

def _gq_lines(q):
    """Return (P, lines) for the symplectic generalized quadrangle W(q)."""
    F = lib.GF(q)
    A = F.add_table.tolist()
    M = F.mul_table.tolist()
    NEG = [F.neg(a) for a in range(q)]
    INV = [0] + [F.inv(a) for a in range(1, q)]
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    P = len(pts)
    index = {v: i for i, v in enumerate(pts)}

    def norm(v):
        c = next(x for x in v if x)
        ic = INV[c]
        return tuple(M[ic][x] for x in v)

    covered = [bytearray(P) for _ in range(P)]
    lines = []
    for i in range(P):
        x = pts[i]
        ci = covered[i]
        for j in range(i + 1, P):
            if ci[j]:
                continue
            y = pts[j]
            t = A[M[x[0]][y[1]]][NEG[M[x[1]][y[0]]]]
            s = A[M[x[2]][y[3]]][NEG[M[x[3]][y[2]]]]
            if A[t][s] != 0:
                continue
            L = set()
            for a in range(q):
                ax = [M[a][x[k]] for k in range(4)]
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(A[ax[k]][M[b][y[k]]] for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                cp = covered[p]
                for r in L:
                    cp[r] = 1
    return P, lines


def _gq_incidence(P, lines):
    """Incidence graph: points 0..P-1, lines P..P+L-1; degree q+1, diameter 4."""
    return P + len(lines), [(p, P + j) for j, Ls in enumerate(lines) for p in Ls]


def _conflicts(lines, P):
    """Return (pt_lines, line_conf, pt_conf): point->lines, line-sharing-point and point-collinear adjacency."""
    pl = [[] for _ in range(P)]
    for j, Ls in enumerate(lines):
        for p in Ls:
            pl[p].append(j)
    line_conf = [set() for _ in lines]
    for p in range(P):
        for a in pl[p]:
            for b in pl[p]:
                if a != b:
                    line_conf[a].add(b)
    pt_conf = [set() for _ in range(P)]
    for Ls in lines:
        for p in Ls:
            for r in Ls:
                if p != r:
                    pt_conf[p].add(r)
    return pl, [sorted(s) for s in line_conf], [sorted(s) for s in pt_conf]


# ----------------------------------------------------------------------------
# Independent-set searches on conflict graphs.
# ----------------------------------------------------------------------------

def _spread_search(A_nb, B_to_A, nB, k, rng, deadline):
    """Largest family of A-vertices with pairwise disjoint neighbourhoods (size k each).

    Depth-first search branching on the uncovered B-vertex with fewest options,
    restarted with fresh random orders on node caps.
    """
    nA = len(A_nb)
    blocked = [0] * nA
    covered = [False] * nB
    chosen = []
    best = []
    stop = [False]
    steps = [0]
    cap = [0]
    order = list(range(nB))

    def rec(U):
        if stop[0]:
            return
        steps[0] += 1
        if steps[0] > cap[0] or ((steps[0] & 15) == 0 and time.monotonic() >= deadline):
            stop[0] = True
            return
        if len(chosen) > len(best):
            best[:] = chosen
        if U == 0 or len(chosen) + U // k <= len(best):
            return
        pick = None
        for b in order:
            if covered[b]:
                continue
            o = [a for a in B_to_A[b] if blocked[a] == 0]
            if not o:
                return
            if pick is None or len(o) < len(pick):
                pick = o
        rng.shuffle(pick)
        for a in pick:
            chosen.append(a)
            for x in A_nb[a]:
                covered[x] = True
                for a2 in B_to_A[x]:
                    blocked[a2] += 1
            rec(U - k)
            for x in A_nb[a]:
                covered[x] = False
                for a2 in B_to_A[x]:
                    blocked[a2] -= 1
            chosen.pop()
            if stop[0]:
                return

    while time.monotonic() < deadline and len(best) * k < nB:
        rng.shuffle(order)
        stop[0] = False
        cap[0] = steps[0] + 600
        rec(nB)
    return list(best)


def _independent_set(N, nb, rng, nprng, deadline):
    """Iterated local search (conflict-minimising swaps with tabu) for an independent set."""
    if N == 0:
        return []
    nbn = [np.asarray(x, dtype=np.int64) for x in nb]
    cnt = np.zeros(N, dtype=np.int64)
    inS = np.zeros(N, dtype=bool)
    tabu = np.zeros(N, dtype=np.int64)
    S = []
    conf = 0
    best = []
    best_size = 0
    it = 0
    last_best_it = 0

    def add(v):
        nonlocal conf
        conf += int(cnt[v])
        cnt[nbn[v]] += 1
        inS[v] = True
        S.append(v)

    def remove(u):
        nonlocal conf
        conf -= int(cnt[u])
        cnt[nbn[u]] -= 1
        inS[u] = False
        S.remove(u)

    def pick():
        score = cnt + nprng.random(N)
        score[inS] = np.inf
        score[tabu > it] = np.inf
        return int(np.argmin(score))

    while True:
        it += 1
        if (it & 63) == 0 and time.monotonic() >= deadline:
            break
        if conf == 0:
            if len(S) > best_size:
                best = list(S)
                best_size = len(S)
                last_best_it = it
            add(pick())
        else:
            conflicting = [u for u in S if cnt[u] > 0]
            u = conflicting[rng.randrange(len(conflicting))]
            remove(u)
            tabu[u] = it + 5 + rng.randrange(8)
            add(pick())
        if S and it - last_best_it > 15000:
            u = S[rng.randrange(len(S))]
            remove(u)
            tabu[u] = it + 5
            last_best_it = it
    if conf == 0 and len(S) > best_size:
        best = list(S)
    return best


def _mis(n, adj, deadline, rng):
    """k-fixed tabu search for a large independent set (adj = neighbour lists)."""
    inS = [False] * n
    c = [0] * n
    S = []

    def add(v):
        inS[v] = True
        S.append(v)
        for w in adj[v]:
            c[w] += 1

    def remove(u):
        inS[u] = False
        S.remove(u)
        for w in adj[u]:
            c[w] -= 1

    order = list(range(n))
    rng.shuffle(order)
    for v in order:
        if c[v] == 0:
            add(v)
    best = list(S)
    tab_add = [0] * n
    tab_rem = [0] * n
    it = 0
    stuck = 0
    while time.monotonic() < deadline:
        it += 1
        cost = sum(c[v] for v in S)
        if cost == 0:
            if len(S) > len(best):
                best = list(S)
                stuck = 0
            cands = [v for v in range(n) if not inS[v] and tab_add[v] <= it] \
                or [v for v in range(n) if not inS[v]]
            if not cands:
                break
            mn = min(c[v] for v in cands)
            add(rng.choice([v for v in cands if c[v] == mn]))
            continue
        stuck += 1
        if stuck > 3000:
            for v in list(S):
                remove(v)
            for v in best:
                add(v)
            stuck = 0
            continue
        ok = [u for u in S if tab_rem[u] <= it] or list(S)
        mx = max(c[u] for u in ok)
        u = rng.choice([x for x in ok if c[x] == mx])
        remove(u)
        tab_add[u] = it + rng.randint(5, 15)
        cands = [v for v in range(n) if not inS[v] and tab_add[v] <= it] \
            or [v for v in range(n) if not inS[v]]
        mn = min(c[v] for v in cands)
        v = rng.choice([x for x in cands if c[x] == mn])
        add(v)
        tab_rem[v] = it + rng.randint(5, 15)
    return best


def _best_indep(N, nb, deadline, rng, nprng):
    """Run both independent-set searches, each on part of the time; return the larger set."""
    now = time.monotonic()
    mid = now + 0.5 * max(0.0, deadline - now)
    a = _independent_set(N, nb, rng, nprng, mid)
    b = _mis(N, nb, deadline, rng)
    return a if len(a) >= len(b) else b


# ----------------------------------------------------------------------------
# Twin blow-up.
#
# Blowing a vertex up into a twin (same neighbourhood) preserves all distances.
# Base vertices have degree d-1, so each may gain at most one twin neighbour:
#   - blown lines must be pairwise disjoint (a partial spread);
#   - blown points must be pairwise non-collinear (a partial ovoid).
# The two constraints are independent, so the sides are searched separately.
# ----------------------------------------------------------------------------

def _blow(n0, edges0, S):
    """Blow up each vertex in S into two twin copies."""
    extra = {}
    for v in S:
        extra[v] = n0 + len(extra)
    copies = [[v] + ([extra[v]] if v in extra else []) for v in range(n0)]
    edges = []
    for u, v in edges0:
        for a in copies[u]:
            for b in copies[v]:
                edges.append((a, b))
    return n0 + len(extra), edges


def _blowup(P, lines, n0, edges0, d, deadline, rng, nprng):
    """Twin blow-up of W(d-2): spread on the line side, partial ovoid on the point side."""
    rem = deadline - time.monotonic()
    if rem <= 0:
        return None
    pl, line_conf, pt_conf = _conflicts(lines, P)
    k = d - 1

    # Line side (spread). Exact-cover DFS first; a local search only if DFS is not perfect.
    a_end = time.monotonic() + 0.3 * rem
    chosen_lines = _spread_search(lines, pl, P, k, rng, a_end)
    if len(chosen_lines) * k < P:
        a2 = time.monotonic() + 0.1 * rem
        alt = _best_indep(len(lines), line_conf, a2, rng, nprng)
        if len(alt) > len(chosen_lines):
            chosen_lines = alt
    S = [P + j for j in chosen_lines]

    # Point side (partial ovoid) with the remaining time.
    S += _best_indep(P, pt_conf, deadline, rng, nprng)
    return _blow(n0, edges0, S)


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit - 6.0, 42.0))
    deadline = t0 + budget
    rng = random.Random(seed)
    nprng = np.random.default_rng(abs(int(seed)) % (2 ** 32))

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    # Projective plane incidence graph: degree d, diameter 3.
    if D >= 3 and lib.is_prime_power(d - 1):
        try:
            consider(*lib.projective_plane_incidence(d - 1))
        except Exception:
            pass

    # W(d-1): degree d, diameter 4.
    if D >= 4 and 2 <= d - 1 <= 11 and lib.is_prime_power(d - 1):
        try:
            P, lines = _gq_lines(d - 1)
            consider(*_gq_incidence(P, lines))
        except Exception:
            pass

    # W(d-2) blown up to degree d, diameter 4.
    q = d - 2
    if D >= 4 and 2 <= q <= 11 and lib.is_prime_power(q) and time.monotonic() < deadline - 3.0:
        try:
            P, lines = _gq_lines(q)
            n0, e0 = _gq_incidence(P, lines)
            consider(n0, e0)
            res = _blowup(P, lines, n0, e0, d, deadline, rng, nprng)
            if res is not None:
                consider(res[0], res[1])
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
