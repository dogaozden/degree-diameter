import itertools
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q): points and totally isotropic lines.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Return (P, lines): points of W(q) as 0..P-1 and each line as a sorted point list."""
    F = lib.GF(q)
    mul = F.mul_table.tolist()
    add = F.add_table.tolist()
    neg = [next(b for b in range(q) if add[a][b] == 0) for a in range(q)]
    inv = [0] * q
    for a in range(1, q):
        inv[a] = next(b for b in range(1, q) if mul[a][b] == 1)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        ic = inv[c]
        return tuple(mul[ic][x] for x in v)

    def form(x, y):
        t = add[mul[x[0]][y[1]]][neg[mul[x[1]][y[0]]]]
        u = add[mul[x[2]][y[3]]][neg[mul[x[3]][y[2]]]]
        return add[t][u]

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i * P + j) in covered:
                continue
            y = pts[j]
            if form(x, y):
                continue
            Lset = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(add[mul[a][x[k]]][mul[b][y[k]]] for k in range(4))
                    if any(v):
                        Lset.add(index[norm(v)])
            Ls = sorted(Lset)
            lines.append(Ls)
            for p in Ls:
                for r in Ls:
                    if p < r:
                        covered.add(p * P + r)
    return P, lines


# ----------------------------------------------------------------------------
# k-growing tabu search for a large independent set (conflict-free family).
# ----------------------------------------------------------------------------

def _tabu_mis(N, nbrs, cap, deadline, rng, nprng):
    """Largest conflict-free set found by tabu swaps before deadline (stops early at cap)."""
    if N == 0:
        return []
    nb = [np.asarray(x, dtype=np.int64) for x in nbrs]
    cnt = np.zeros(N, dtype=np.int64)     # number of chosen neighbours of each vertex
    inS = np.zeros(N, dtype=bool)
    tabu = np.zeros(N, dtype=np.int64)
    S = []
    cost = 0
    it = 0

    def add(v):
        nonlocal cost
        cost += int(cnt[v])
        cnt[nb[v]] += 1
        inS[v] = True
        S.append(v)

    def remove(u):
        nonlocal cost
        cnt[nb[u]] -= 1
        cost -= int(cnt[u])
        inS[u] = False
        S.remove(u)

    def pick():
        score = cnt + nprng.random(N)
        score[inS] = 1e18
        score[tabu > it] = 1e18
        v = int(np.argmin(score))
        if score[v] >= 1e17:
            score = cnt + nprng.random(N)
            score[inS] = 1e18
            v = int(np.argmin(score))
        return v

    order = list(range(N))
    rng.shuffle(order)
    for v in order:
        if cnt[v] == 0:
            add(v)
    best = list(S)
    since = 0
    while len(best) < cap and time.monotonic() < deadline:
        it += 1
        if cost == 0:
            if len(S) > len(best):
                best = list(S)
                since = 0
                if len(best) >= cap:
                    break
            add(pick())
        else:
            conf = [u for u in S if cnt[u] > 0]
            u = conf[rng.randrange(len(conf))]
            remove(u)
            tabu[u] = it + 7 + rng.randrange(10)
            add(pick())
        since += 1
        if since > 3000:
            for u in list(S):
                remove(u)
            for v in best:
                add(v)
            for _ in range(2):
                u = S[rng.randrange(len(S))]
                remove(u)
                tabu[u] = it + 20
            since = 0
    return best


# ----------------------------------------------------------------------------
# Twin blow-up of W(q), degree q+2, diameter 4.
#
# Blowing up point p (copy p' with the same neighbourhood) adds one degree to
# every line through p, so the blown points must be pairwise non-collinear
# (partial ovoid). Blowing up line j adds one degree to every point on j, so
# the blown lines must be pairwise disjoint (partial spread). The two sides
# are independent. Twin blow-ups preserve distances between original vertices.
# ----------------------------------------------------------------------------

def _twin(P, lines, q, deadline, rng, nprng):
    L = len(lines)
    lop = [[] for _ in range(P)]
    for j, Ls in enumerate(lines):
        for p in Ls:
            lop[p].append(j)
    pconf = [set() for _ in range(P)]      # collinear points
    for Ls in lines:
        for p in Ls:
            pconf[p].update(Ls)
    for p in range(P):
        pconf[p].discard(p)
    lconf = [set() for _ in range(L)]      # lines sharing a point
    for p in range(P):
        for a in lop[p]:
            lconf[a].update(lop[p])
    for a in range(L):
        lconf[a].discard(a)

    now = time.monotonic()
    mid = now + 0.5 * (deadline - now)
    I = _tabu_mis(P, [sorted(s) for s in pconf], q * q + 1, mid, rng, nprng)
    J = _tabu_mis(L, [sorted(s) for s in lconf], P // (q + 1), deadline, rng, nprng)

    n0 = P + L
    E0 = [(p, P + j) for j, Ls in enumerate(lines) for p in Ls]
    extra = {}
    for v in list(I) + [P + j for j in J]:
        extra[v] = n0 + len(extra)
    edges = []
    for u, v in E0:
        cu = (u, extra[u]) if u in extra else (u,)
        cv = (v, extra[v]) if v in extra else (v,)
        for a in cu:
            for b in cv:
                edges.append((a, b))
    return n0 + len(extra), edges


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit - 5.0, time_limit - 12.0))
    deadline = t0 + budget
    rng = random.Random(seed)
    nprng = np.random.default_rng(abs(int(seed)) % (2 ** 32))

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))      # K_{d,d}, diameter 2

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 2:
        return best

    # Projective plane incidence graph: degree d, diameter 3.
    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        try:
            consider(*lib.projective_plane_incidence(d - 1))
        except Exception:
            pass

    # W(d-1) incidence graph: degree d, diameter 4.
    if D >= 4 and 2 <= d - 1 <= 11 and lib.is_prime_power(d - 1):
        try:
            P, lines = _gq_w(d - 1)
            e = [(p, P + j) for j, Ls in enumerate(lines) for p in Ls]
            consider(P + len(lines), e)
        except Exception:
            pass

    # Twin blow-up of W(d-2): degree d, diameter 4.
    q = d - 2
    if D >= 4 and 2 <= q <= 11 and lib.is_prime_power(q):
        try:
            P, lines = _gq_w(q)
            e0 = [(p, P + j) for j, Ls in enumerate(lines) for p in Ls]
            consider(P + len(lines), e0)          # degree d-1 fallback
            if time.monotonic() < deadline - 1.0:
                consider(*_twin(P, lines, q, deadline, rng, nprng))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return lib.haar_graph(d, range(d))
    return best
