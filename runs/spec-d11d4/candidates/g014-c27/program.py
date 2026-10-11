import itertools
import random
import time

import numpy as np

import lib


NOISE = 0.25     # probability of a random (rather than greedy) pick in extension covers
TRIES = 300      # cover attempts per extension step before giving up


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q): points and totally isotropic lines.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Return (P, lines): points of W(q) indexed 0..P-1, each line as a sorted point list."""
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


def _gq_incidence(q):
    """Incidence graph of W(q): degree q+1, diameter 4."""
    P, lines = _gq_w(q)
    return P + len(lines), [(p, P + j) for j, Ls in enumerate(lines) for p in Ls]


# ----------------------------------------------------------------------------
# Maximum independent set: fixed-size tabu search on the conflict graph.
# ----------------------------------------------------------------------------

def _mis(n, nbrs, deadline, rng, nprng):
    """Return a large independent set; nbrs[v] is a numpy array of conflicting vertices."""
    inS = np.zeros(n, dtype=bool)
    conf = np.zeros(n, dtype=np.int64)      # number of chosen neighbours of each vertex
    tab_add = np.zeros(n, dtype=np.int64)   # may not be re-added before this iteration
    tab_rem = np.zeros(n, dtype=np.int64)   # may not be removed before this iteration
    S = []
    cost = 0                                # number of conflicting pairs inside S

    def add(v):
        nonlocal cost
        cost += int(conf[v])
        inS[v] = True
        conf[nbrs[v]] += 1
        S.append(v)

    def remove(u):
        nonlocal cost
        inS[u] = False
        conf[nbrs[u]] -= 1
        cost -= int(conf[u])
        S.remove(u)

    order = list(range(n))
    rng.shuffle(order)
    for v in order:
        if conf[v] == 0:
            add(v)
    best = list(S)
    it = 0
    stall = 0
    while True:
        it += 1
        if (it & 15) == 0 and time.monotonic() >= deadline:
            break
        if cost == 0:
            if len(S) > len(best):
                best = list(S)
                stall = 0
            cand = np.flatnonzero((~inS) & (tab_add <= it))
            if cand.size == 0:
                cand = np.flatnonzero(~inS)
            if cand.size == 0:
                break
            v = int(cand[np.argmin(conf[cand] + nprng.random(cand.size))])
            add(v)
            continue
        stall += 1
        if stall > 4000:
            # Perturb: rebuild from a random 90% of the best set.
            for u in list(S):
                remove(u)
            keep = list(best)
            rng.shuffle(keep)
            drop = max(1, len(keep) // 10)
            for v in keep[drop:]:
                add(v)
            tab_add[:] = 0
            tab_rem[:] = 0
            stall = 0
            continue
        Sarr = np.array(S, dtype=np.int64)
        cs = conf[Sarr]
        ok = tab_rem[Sarr] <= it
        if ok.any():
            Sarr = Sarr[ok]
            cs = cs[ok]
        mx = cs.max()
        choices = Sarr[cs == mx]
        u = int(choices[rng.randrange(len(choices))])
        remove(u)
        tab_add[u] = it + 7 + rng.randrange(10)
        cand = np.flatnonzero((~inS) & (tab_add <= it))
        if cand.size == 0:
            cand = np.flatnonzero(~inS)
        v = int(cand[np.argmin(conf[cand] + nprng.random(cand.size))])
        add(v)
        tab_rem[v] = it + 3 + rng.randrange(5)
    return best


# ----------------------------------------------------------------------------
# Twin graph on W(q): add a twin vertex for each point of I (adjacent to its lines)
# and each line of J (adjacent to its points). With I a set of pairwise non-collinear
# points and J a set of pairwise non-concurrent lines, all degrees stay <= q+2.
# ----------------------------------------------------------------------------

def _twin(P, lines, pl, I, J):
    L = len(lines)
    edges = [(p, P + j) for j, Ls in enumerate(lines) for p in Ls]
    n = P + L
    for p in I:
        for j in pl[p]:
            edges.append((n, P + j))
        n += 1
    for j in J:
        for p in lines[j]:
            edges.append((p, n))
        n += 1
    return n, edges


# ----------------------------------------------------------------------------
# Greedy set-cover extension for diameter 4.
#
# A new vertex x joined to S (all on one side, all with spare degree) keeps
# diameter <= 4 iff the union of the radius-3 balls of S covers every vertex.
# Adding x only shortens distances, so no other pair can break.
# The balls are recomputed after every successful addition.
# ----------------------------------------------------------------------------

def _ball3(n, adj):
    reach = [1 << v for v in range(n)]
    for _ in range(3):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return reach


def _pick(pool, reach, unc, rng):
    if rng.random() < NOISE:
        useful = [v for v in pool if reach[v] & unc]
        return rng.choice(useful) if useful else -1
    best_g, bv = 0, -1
    for v in pool:
        g = (reach[v] & unc).bit_count()
        if g > best_g:
            best_g, bv = g, v
    return bv


def _extend(n, edges, d, deadline, rng):
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for w in adj[u]:
                if color[w] == -1:
                    color[w] = 1 - color[u]
                    stack.append(w)

    while time.monotonic() < deadline:
        reach = _ball3(n, adj)
        full = (1 << n) - 1
        spare = [v for v in range(n) if len(adj[v]) < d]
        if not spare:
            break
        added = False
        for _ in range(TRIES):
            if time.monotonic() >= deadline:
                break
            s0 = rng.choice(spare)
            pool = [v for v in spare if color[v] == color[s0] and v != s0]
            S = [s0]
            unc = full & ~reach[s0]
            while unc and len(S) < d and pool:
                bv = _pick(pool, reach, unc, rng)
                if bv < 0:
                    break
                S.append(bv)
                unc &= ~reach[bv]
                pool.remove(bv)
            if unc:
                continue
            x = n
            n += 1
            for s in S:
                edges.append((s, x))
                adj[s].append(x)
            adj.append(list(S))
            color.append(1 - color[s0])
            added = True
            break
        if not added:
            break
    return n, edges


# ----------------------------------------------------------------------------
# Twin route for D = 4, degree d = q + 2 with q a prime power.
# ----------------------------------------------------------------------------

def _twin_route(q, deadline, rng, nprng):
    """Return a list of candidate (n, edges) graphs of degree q+2, diameter 4."""
    P, lines = _gq_w(q)
    L = len(lines)
    pl = [[] for _ in range(P)]
    for j, Ls in enumerate(lines):
        for p in Ls:
            pl[p].append(j)

    pc = [set() for _ in range(P)]          # collinear points
    for Ls in lines:
        for p in Ls:
            pc[p].update(Ls)
    for p in range(P):
        pc[p].discard(p)
    lc = [set() for _ in range(L)]          # concurrent lines
    for p in range(P):
        for a in pl[p]:
            lc[a].update(pl[p])
    for a in range(L):
        lc[a].discard(a)
    pn = [np.array(sorted(s), dtype=np.int64) for s in pc]
    ln = [np.array(sorted(s), dtype=np.int64) for s in lc]

    now = time.monotonic()
    rem = max(0.0, deadline - now)
    I = _mis(P, pn, now + 0.4 * rem, rng, nprng)
    J = _mis(L, ln, now + 0.8 * rem, rng, nprng)

    n, e = _twin(P, lines, pl, I, J)
    out = [(n, e)]
    n2, e2 = _extend(n, e, q + 2, deadline, rng)
    out.append((n2, e2))
    return out


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 10.0))
    deadline = t0 + budget
    rng = random.Random(seed)
    nprng = np.random.default_rng(abs(int(seed)) % (2 ** 32))

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 2:
        return best

    # Projective plane incidence: degree d, diameter 3.
    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        try:
            consider(*lib.projective_plane_incidence(d - 1))
        except Exception:
            pass

    # W(d-1) incidence: degree d, diameter 4.
    if D >= 4 and 2 <= d - 1 <= 9 and lib.is_prime_power(d - 1):
        try:
            consider(*_gq_incidence(d - 1))
        except Exception:
            pass

    # Twin graph on W(d-2) with set-cover extension: degree d, diameter 4.
    if D >= 4 and 2 <= d - 2 <= 9 and lib.is_prime_power(d - 2):
        try:
            for n2, e2 in _twin_route(d - 2, deadline, rng, nprng):
                consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
