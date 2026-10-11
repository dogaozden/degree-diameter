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
# Maximum independent set by iterated local search with (1,2)-swaps.
# ----------------------------------------------------------------------------

def _mis(n, adj, deadline, rng):
    """Return a large independent set of the graph (n vertices, adj neighbour lists) found before deadline."""
    if n == 0:
        return []
    inS = [False] * n
    c = [0] * n          # number of neighbours of v inside S
    S = set()
    adjset = [set(a) for a in adj]

    def add(v):
        inS[v] = True
        S.add(v)
        for w in adj[v]:
            c[w] += 1

    def remove(u):
        inS[u] = False
        S.discard(u)
        for w in adj[u]:
            c[w] -= 1

    def local_search():
        while True:
            changed = False
            free = [v for v in range(n) if not inS[v] and c[v] == 0]
            rng.shuffle(free)
            for v in free:
                if not inS[v] and c[v] == 0:
                    add(v)
                    changed = True
            for x in list(S):
                if not inS[x]:
                    continue
                one = [u for u in adj[x] if c[u] == 1]
                if len(one) < 2:
                    continue
                rng.shuffle(one)
                pair = None
                for i in range(len(one)):
                    for j in range(i + 1, len(one)):
                        if one[j] not in adjset[one[i]]:
                            pair = (one[i], one[j])
                            break
                    if pair is not None:
                        break
                if pair is not None:
                    remove(x)
                    add(pair[0])
                    add(pair[1])
                    changed = True
            if not changed:
                break

    order = list(range(n))
    rng.shuffle(order)
    for v in order:
        if not inS[v] and c[v] == 0:
            add(v)
    local_search()
    best = list(S)
    stale = 0

    while time.monotonic() < deadline:
        cand = [v for v in range(n) if not inS[v]]
        if not cand:
            break
        v = rng.choice(cand)
        for w in adj[v]:
            if inS[w]:
                remove(w)
        add(v)
        local_search()
        if len(S) > len(best):
            best = list(S)
            stale = 0
        else:
            stale += 1
        if len(S) < len(best) - 1 or stale > 300:
            for u in list(S):
                remove(u)
            for u in best:
                add(u)
            stale = 0
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
# Bold path: bi-Cayley graphs over small groups.
# Vertices A = G and B = G, with a ~ b iff a^{-1} b lies in S (|S| = d).
# Left translation is an automorphism, so the diameter is at most D iff
# every B-vertex is within D of the identity A-vertex and every A-vertex
# is within D of the identity B-vertex. A simulated-annealing search picks S.
# ----------------------------------------------------------------------------

def _groups_of_order(N, rng):
    """Candidate groups of order N as (order, mul, inv): cyclic, plus semidirect Z_m x| Z_k for small k."""
    groups = []
    if N >= 2:
        groups.append(lib.cyclic_group(N))
    for k in (2, 3, 4, 5, 6, 8):
        if N % k or N // k < 2:
            continue
        m = N // k
        rs = [m - 1] if k == 2 else []
        rs.append(1)
        rs += [rng.randrange(1, m) for _ in range(40)]
        seen = set()
        for r in rs:
            if r in seen:
                continue
            seen.add(r)
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                try:
                    groups.append(lib.semidirect_group(m, k, r))
                    break
                except ValueError:
                    pass
    rng.shuffle(groups)
    return groups


def _unreached(order, mul, S, invS, D, start_side):
    """Number of vertices (both sides) NOT within distance D of the identity vertex on side start_side."""
    vis = [bytearray(order), bytearray(order)]  # side 0 = A, side 1 = B
    vis[start_side][0] = 1
    frontier = [0]
    side = start_side
    for _ in range(D):
        nxt_side = 1 - side
        gens = S if side == 0 else invS   # A->B: g*s ; B->A: h*s^{-1}
        tgt = vis[nxt_side]
        nxt = []
        for g in frontier:
            for t in gens:
                x = mul(g, t)
                if not tgt[x]:
                    tgt[x] = 1
                    nxt.append(x)
        frontier = nxt
        side = nxt_side
        if not frontier:
            break
    return 2 * order - vis[0].count(1) - vis[1].count(1)


def _sa_connection_set(order, mul, inv, d, D, deadline, rng):
    """Anneal a size-d connection set S so the bi-Cayley graph has diameter <= D; return S or None."""
    if d > order or order < 2:
        return None
    S = rng.sample(range(order), d)

    def cost(T):
        invT = [inv(t) for t in T]
        return _unreached(order, mul, T, invT, D, 0) + _unreached(order, mul, T, invT, D, 1)

    cur = cost(S)
    best = (cur, list(S))
    temp = 2.0
    while cur > 0 and time.monotonic() < deadline:
        i = rng.randrange(d)
        x = rng.randrange(order)
        if x in S:
            continue
        cand = list(S)
        cand[i] = x
        c = cost(cand)
        if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
            S, cur = cand, c
            if cur < best[0]:
                best = (cur, list(S))
        temp = max(0.05, temp * 0.999)
    return best[1] if best[0] == 0 else None


def _bicayley_graph(order, mul, S):
    """Edges of the bi-Cayley graph: A-vertex g joined to B-vertex order + g*s for each s in S."""
    return 2 * order, [(g, order + mul(g, s)) for g in range(order) for s in S]


def _grow_bicayley(d, D, n0, deadline, rng, consider):
    """Repeatedly look for a bi-Cayley graph one order larger than the current best; stop when a search fails."""
    N = n0 // 2 + 1
    cap = lib._moore_bound(d, D) // 2
    while N <= cap and time.monotonic() < deadline:
        groups = _groups_of_order(N, rng)
        if not groups:
            N += 1
            continue
        found = False
        for idx, (order, mul, inv) in enumerate(groups):
            now = time.monotonic()
            if now >= deadline:
                break
            share = (deadline - now) / (len(groups) - idx)
            S = _sa_connection_set(order, mul, inv, d, D, now + share, rng)
            if S is not None:
                n_, edges = _bicayley_graph(order, mul, S)
                consider(n_, edges)
                found = True
                break
        if not found:
            break
        N += 1


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 10.0))
    deadline = t0 + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, edges):
        nonlocal best
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)

    # Projective plane incidence graph: degree d, diameter 3.
    if D >= 3 and lib.is_prime_power(d - 1):
        try:
            consider(*lib.projective_plane_incidence(d - 1))
        except Exception:
            pass

    # Generalized quadrangle W(d-1): degree d, diameter 4.
    if D >= 4 and lib.is_prime_power(d - 1) and 2 <= d - 1 <= 11:
        try:
            consider(*_gq_incidence(d - 1))
        except Exception:
            pass

    # Twin construction on W(d-2) (degree d, diameter 4). Gets half the budget,
    # leaving the rest for the bold bi-Cayley search.
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            twin_deadline = t0 + 0.5 * budget
            consider(*_twin_graph(d - 2, twin_deadline, rng))
        except Exception:
            pass

    # Bold path: bi-Cayley search over small groups, aiming one order above the current best.
    if d >= 2 and D >= 2:
        try:
            _grow_bicayley(d, D, best[0], deadline, rng, consider)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
