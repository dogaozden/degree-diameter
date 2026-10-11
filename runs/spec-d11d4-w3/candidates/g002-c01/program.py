import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) as a point/line list (table-based, pure Python).
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Return (P, lines): points of W(q) indexed 0..P-1 and each totally isotropic line as a sorted point list."""
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
    """Incidence graph of W(q): (n, edges), points 0..P-1, lines P..P+L-1; degree q+1, diameter 4."""
    P, lines = _gq_w(q)
    L = len(lines)
    return P + L, [(p, P + j) for j, Ls in enumerate(lines) for p in Ls]


# ----------------------------------------------------------------------------
# Maximum independent set by k-fixed tabu search (pure Python).
# ----------------------------------------------------------------------------

def _mis(n, adj, deadline, rng):
    """Return a large independent set of the graph (n vertices, adj neighbour lists) found before deadline."""
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


# ----------------------------------------------------------------------------
# Twin construction on W(q), degree q+2 (for d = q+2, D = 4).
# ----------------------------------------------------------------------------

def _twin_graph(q, deadline, rng):
    P, lines = _gq_w(q)
    L = len(lines)
    pl = [[] for _ in range(P)]
    for j, Ls in enumerate(lines):
        for p in Ls:
            pl[p].append(j)
    padj = [set() for _ in range(P)]
    for Ls in lines:
        for p in Ls:
            for r in Ls:
                if p != r:
                    padj[p].add(r)
    ladj = [set() for _ in range(L)]
    for p in range(P):
        for a in pl[p]:
            for b in pl[p]:
                if a != b:
                    ladj[a].add(b)

    now = time.monotonic()
    mid = now + (deadline - now) / 2.0
    I = _mis(P, [sorted(s) for s in padj], mid, rng)
    J = _mis(L, [sorted(s) for s in ladj], deadline, rng)

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
# Greedy set-cover vertex extension for diameter 4.
# ----------------------------------------------------------------------------

NOISE = 0.25


def _ball3(n, adj):
    """Return per-vertex bitmasks of all vertices within distance 3."""
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
    """Choose the next cover vertex from pool: best gain, or a random useful one with prob NOISE."""
    if rng.random() < NOISE:
        useful = [v for v in pool if reach[v] & unc]
        if useful:
            return rng.choice(useful)
        return -1
    best, bv = 0, -1
    for v in pool:
        g = (reach[v] & unc).bit_count()
        if g > best:
            best, bv = g, v
    return bv


def _extend(n, edges, d, deadline, rng):
    """Greedily add vertices while keeping max degree d and diameter 4; return (n, edges)."""
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

    MAX_FAILS = 20000
    fails = 0
    while time.monotonic() < deadline:
        reach = _ball3(n, adj)
        full = (1 << n) - 1
        grown = False
        while time.monotonic() < deadline:
            spare = [v for v in range(n) if len(adj[v]) < d]
            if not spare:
                return n, edges
            if fails >= MAX_FAILS:
                return n, edges
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
                fails += 1
                continue
            x = n
            n += 1
            for s in S:
                edges.append((s, x))
                adj[s].append(x)
            adj.append(list(S))
            color.append(1 - color[s0])
            fails = 0
            grown = True
            break
        if not grown:
            break
    return n, edges


# ----------------------------------------------------------------------------
# Cyclic Haar-graph search (generic fallback).
# ----------------------------------------------------------------------------

def _haar_search(d, deadline, D, rng, consider):
    m, misses = d + 1, 0
    while time.monotonic() < deadline and misses < 10:
        found = None
        for _ in range(30):
            if time.monotonic() >= deadline:
                break
            S = [0] + rng.sample(range(1, m), d - 1)
            n, edges = lib.haar_graph(m, S)
            if lib.within_diameter(n, edges, D):
                found = (n, edges)
                break
        if found:
            consider(*found)
            misses = 0
        else:
            misses += 1
        m += 1


# ----------------------------------------------------------------------------
# NEW (bold) construction: bi-Cayley Haar lifts over small non-abelian groups.
#
# Base graph: two vertices A, B joined by d parallel darts with voltages
# S = {g_1..g_d} in a group G of order M. The lift has A_x ~ B_{x*g} for g in S.
# Left multiplication is an automorphism, so the diameter is <= 4 iff
#   (i)  the radius-4 ball of A_e contains all of A and all of B, and
#   (ii) the radius-4 ball of B_e contains all of B.
# We search over S with simulated annealing on the number of missed vertices,
# over several groups of order M, and grow M while successes continue.
# ----------------------------------------------------------------------------

def _groups_of_order(M):
    """Return semidirect-product parameters (a, k, r) with a*k = M, usable by lib.semidirect_group."""
    out = []
    for a in range(1, M + 1):
        if M % a:
            continue
        k = M // a
        if a == 1:
            out.append((1, k, 1))
        else:
            for r in range(1, a):
                if math.gcd(r, a) == 1 and pow(r, k, a) == 1 % a:
                    out.append((a, k, r))
    return out


def _reach(root, M, mul, S, ginv):
    """Vertices within distance 4 of root (A indices 0..M-1, B indices M..2M-1)."""
    seen = {root}
    frontier = [root]
    for _ in range(4):
        nxt = []
        for u in frontier:
            if u < M:
                for g in S:
                    w = M + mul(u, g)
                    if w not in seen:
                        seen.add(w)
                        nxt.append(w)
            else:
                y = u - M
                for h in ginv:
                    w = mul(y, h)
                    if w not in seen:
                        seen.add(w)
                        nxt.append(w)
        frontier = nxt
        if not frontier:
            break
    return seen


def _lift_cost(M, mul, S, ginv):
    """Number of vertices missed by the radius-4 balls of A_e and B_e (0 iff diameter <= 4)."""
    sa = _reach(0, M, mul, S, ginv)
    sb = _reach(M, M, mul, S, ginv)
    nb = sum(1 for w in sb if w >= M)
    return (2 * M - len(sa)) + (M - nb)


def _anneal(M, d, mul, inv, rng, deadline):
    """Search a d-element voltage set S in the group of order M with zero lift cost; return S or None."""
    S = rng.sample(range(M), d)
    ginv = [inv(g) for g in S]
    c = _lift_cost(M, mul, S, ginv)
    T = 2.0
    while c > 0 and time.monotonic() < deadline:
        i = rng.randrange(d)
        g = rng.randrange(M)
        if g in S:
            continue
        S2 = S[:]
        S2[i] = g
        ginv2 = [inv(x) for x in S2]
        c2 = _lift_cost(M, mul, S2, ginv2)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
            S, c, ginv = S2, c2, ginv2
        T = max(0.2, T * 0.998)
    return S if c == 0 else None


def _lift_hunt(d, deadline, rng, consider, n_best):
    """Repeatedly search bi-Cayley lifts with growing group order until the deadline."""
    M = n_best // 2 + 1
    while time.monotonic() < deadline - 0.5:
        cands = _groups_of_order(M)
        rng.shuffle(cands)
        success = False
        for (a, k, r) in cands[:4]:
            now = time.monotonic()
            if now >= deadline - 0.5:
                break
            slice_end = min(deadline, now + 3.0)
            _, mul, inv = lib.semidirect_group(a, k, r)
            S = _anneal(M, d, mul, inv, rng, slice_end)
            if S is not None:
                n, edges = lib.group_lift(2, [(0, 1, g) for g in S], M, mul)
                consider(n, edges)
                success = True
                M += 1
                break
        if not success and not cands:
            M += 1


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 8.0))
    deadline = t0 + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    structured = False

    def consider(n, edges):
        nonlocal best
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)

    # Projective plane incidence graph: degree d, diameter 3 (Moore-optimal).
    if D >= 3 and lib.is_prime_power(d - 1):
        try:
            before = best[0]
            consider(*lib.projective_plane_incidence(d - 1))
            if best[0] > before:
                structured = True
        except Exception:
            pass
        if D == 3 and structured:
            return best

    # Baseline budget: for D = 4 keep the twin/extension pipeline in the first
    # part of the budget, and leave the rest for the bi-Cayley lift hunt.
    base_deadline = t0 + 0.6 * budget if D == 4 else deadline

    # Twin graph on W(d-2), then randomized set-cover extension.
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        q = d - 2
        attempt = 0
        while attempt < 4:
            now = time.monotonic()
            rem = base_deadline - now
            if rem < 3.0:
                break
            share = rem if attempt == 3 else rem * 0.5
            tw_dl = now + share * 0.4
            ex_dl = now + share
            try:
                n2, e2 = _twin_graph(q, tw_dl, rng)
                before = best[0]
                consider(n2, e2)
                if best[0] > before:
                    structured = True
                n3, e3 = _extend(n2, e2, d, ex_dl, rng)
                consider(n3, e3)
            except Exception:
                pass
            attempt += 1

    # Generalized quadrangle W(d-1): degree d, diameter 4.
    if D >= 4 and lib.is_prime_power(d - 1) and 2 <= d - 1 <= 11 \
            and time.monotonic() < base_deadline:
        try:
            before = best[0]
            consider(*_gq_incidence(d - 1))
            if best[0] > before:
                structured = True
        except Exception:
            pass

    # No structured construction succeeded: cyclic Haar lifts in the baseline phase.
    if not structured and time.monotonic() < base_deadline:
        _haar_search(d, base_deadline, D, rng, consider)

    # Bold phase: bi-Cayley lifts over non-abelian groups, grown from the current best.
    if D == 4 and time.monotonic() < deadline - 1.0:
        try:
            _lift_hunt(d, deadline, rng, consider, best[0])
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
