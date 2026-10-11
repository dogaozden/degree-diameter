import itertools
import math
import random
import time

import numpy as np

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
# Randomized greedy set-cover vertex extension for diameter 4.
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
    """Choose the next cover vertex: best gain, or a random useful one with prob NOISE."""
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
# NEW: bipartite group lifts over non-abelian groups, found by annealing.
#
# Base graph: two vertices joined by d darts with voltages g_1..g_d in a group G
# (right multiplication): A_x ~ B_{x g_i}. Left multiplication is an automorphism
# group acting transitively on each side, so diameter <= 4 reduces to covering G:
#   A-A: {1} U S S^-1 U (S S^-1)(S S^-1)  must equal G
#   B-B: {1} U S^-1 S U (S^-1 S)(S^-1 S)  must equal G
#   A-B: S U S S^-1 S                     must equal G
# Non-abelian G is essential: abelian groups collapse the word counts.
# ----------------------------------------------------------------------------

def _group_candidates(G, rng):
    """Non-abelian semidirect products Z_m x|_r Z_k of order G with small k, shuffled."""
    out = []
    for k in range(2, min(G, 12) + 1):
        if G % k:
            continue
        m = G // k
        if m < 2:
            continue
        for r in range(2, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1:
                out.append((m, k, r))
    rng.shuffle(out)
    return out


def _group_search(m, k, r, d, deadline, rng):
    """Anneal a d-element generating multiset S with zero coverage cost; return voltages or None."""
    G = m * k
    if G <= d + 1:
        return None
    xs = np.arange(G, dtype=np.int64)[:, None]
    ys = np.arange(G, dtype=np.int64)[None, :]
    a, b = xs // k, xs % k
    c, e = ys // k, ys % k
    pw = np.array([pow(r, t, m) for t in range(k)], dtype=np.int64)
    tab = (((a + pw[b] * c) % m) * k + (b + e) % k).astype(np.int64)
    inv = np.argmax(tab == 0, axis=1).astype(np.int64)

    def cost(S):
        Si = inv[S]
        # Words g h^-1 and h^-1 g (length 2), and length-3 words.
        D1 = tab[S[:, None], Si[None, :]].ravel()
        E2 = tab[D1[:, None], D1[None, :]].ravel()
        CA = np.zeros(G, dtype=bool)
        CA[E2] = True
        CA[D1] = True
        CA[0] = True
        Q1 = tab[Si[:, None], S[None, :]].ravel()
        Q2 = tab[Q1[:, None], Q1[None, :]].ravel()
        CB = np.zeros(G, dtype=bool)
        CB[Q2] = True
        CB[Q1] = True
        CB[0] = True
        O1 = tab[D1[:, None], S[None, :]].ravel()
        O = np.zeros(G, dtype=bool)
        O[O1] = True
        O[S] = True
        return int(G - CA.sum()) + int(G - CB.sum()) + int(G - O.sum())

    S = np.array(rng.sample(range(G), d), dtype=np.int64)
    cur = cost(S)
    best_c, best_S = cur, S.copy()
    start = time.monotonic()
    span = max(1e-3, deadline - start)
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        frac = (now - start) / span
        T = max(0.3, 1.5 * (1.0 - frac))
        i = rng.randrange(d)
        g = rng.randrange(G)
        if np.any(S == g):
            continue
        Sn = S.copy()
        Sn[i] = g
        cn = cost(Sn)
        if cn <= cur or rng.random() < math.exp(-(cn - cur) / T):
            S, cur = Sn, cn
            if cur < best_c:
                best_c, best_S = cur, S.copy()
    if best_c == 0:
        return [int(v) for v in best_S]
    return None


def _group_phase(d, D, cur_n, deadline, rng, consider):
    """Search group lifts for orders above the current best, ascending, within deadline."""
    hi = lib._moore_bound(d, D) // 2
    lo = max(cur_n // 2 + 1, d + 2)
    for G in range(lo, hi + 1):
        if time.monotonic() >= deadline - 0.5:
            return
        cands = _group_candidates(G, rng)[:3]
        for (m, k, r) in cands:
            remaining = deadline - time.monotonic()
            if remaining < 1.0:
                return
            slice_end = time.monotonic() + min(remaining, 4.0)
            S = _group_search(m, k, r, d, slice_end, rng)
            if S is not None:
                order, mul, _ = lib.semidirect_group(m, k, r)
                n, edges = lib.group_lift(2, [(0, 1, g) for g in S], order, mul)
                consider(n, edges)
                break


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.88 * time_limit, time_limit - 7.0))
    deadline = t0 + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Split time for D = 4: the parent pipeline keeps a solid share, the
    # group-lift search gets the rest.
    group_phase = (D == 4 and d >= 3)
    pdeadline = t0 + (0.65 * budget if group_phase else budget)
    pbudget = pdeadline - t0

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

    # Twin graph on W(d-2) (degree d), then randomized set-cover extension.
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            twin_deadline = t0 + 0.4 * pbudget
            n2, e2 = _twin_graph(d - 2, twin_deadline, rng)
            consider(n2, e2)
            attempt = 0
            while time.monotonic() < pdeadline - 1.0 and attempt < 4:
                remaining = pdeadline - time.monotonic()
                slice_end = time.monotonic() + max(1.0, remaining / (4 - attempt))
                n3, e3 = _extend(n2, e2, d, min(slice_end, pdeadline), rng)
                consider(n3, e3)
                attempt += 1
                if n3 == n2 and attempt >= 2:
                    break
        except Exception:
            pass

    # Bold new construction: non-abelian group lifts of a 2-vertex base graph,
    # searched above the current best order.
    if group_phase:
        try:
            _group_phase(d, D, best[0], deadline, rng, consider)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
