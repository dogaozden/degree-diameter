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
# Greedy set-cover vertex extension for diameter 4.
# ----------------------------------------------------------------------------

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

    fails = 0
    while time.monotonic() < deadline and fails < 3000:
        reach = _ball3(n, adj)
        full = (1 << n) - 1
        grown = False
        while time.monotonic() < deadline and fails < 3000:
            spare = [v for v in range(n) if len(adj[v]) < d]
            if not spare:
                return n, edges
            s0 = rng.choice(spare)
            pool = [v for v in spare if color[v] == color[s0] and v != s0]
            S = [s0]
            unc = full & ~reach[s0]
            while unc and len(S) < d and pool:
                best, bv = 0, -1
                for v in pool:
                    g = (reach[v] & unc).bit_count()
                    if g > best:
                        best, bv = g, v
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
# Haar graphs H(Z_m, S) with |S| = d, searched randomly (cyclic baseline).
# ----------------------------------------------------------------------------

def _haar_ok(m, S, D):
    """True if the Haar graph on Z_m with connection set S has diameter <= D."""
    A = np.zeros(m, dtype=bool)
    A[0] = True
    B = np.zeros(m, dtype=bool)
    negS = [(-s) % m for s in S]
    for step in range(D):
        Y = np.zeros(m, dtype=bool)
        if step % 2 == 0:
            for s in S:
                Y |= np.roll(A, s)
            B |= Y
        else:
            for t in negS:
                Y |= np.roll(B, t)
            A |= Y
    return bool(A.all() and B.all())


def _haar_search(d, D, m_hi, rng, deadline, trials_per):
    """Binary search for the largest m with a working random Haar graph; return (m, S)."""
    lo, hi = d, max(d, m_hi)
    best = (d, list(range(d)))
    while lo < hi and time.monotonic() < deadline:
        mid = (lo + hi + 1) // 2
        found = None
        for _ in range(trials_per):
            if time.monotonic() >= deadline:
                break
            S = rng.sample(range(mid), d)
            if _haar_ok(mid, S, D):
                found = S
                break
        if found is not None:
            best = (mid, found)
            lo = mid
        else:
            hi = mid - 1
    return best


# ----------------------------------------------------------------------------
# NEW: Cayley-type bipartite graphs (Haar graphs over non-abelian groups).
#
# Group G = Z_m x|_r Z_k, elements coded a*k+b. The bipartite graph has sides
# A and B, each indexed by G, with a_g ~ b_{g*s} for s in S (|S| = d).
# Left translations are automorphisms and transitive on each side, so the
# diameter is at most D iff a BFS from a_e and a BFS from b_e both reach
# everything within D steps. We run simulated-annealing-style local search on
# S, minimizing the number of unreached (vertex, start) pairs.
# ----------------------------------------------------------------------------

class _Group:
    """Z_m x|_r Z_k with elements coded a*k+b; provides right-multiplication maps over all elements."""

    def __init__(self, m, k, r):
        self.m, self.k, self.r = m, k, r
        self.N = m * k
        idx = np.arange(self.N, dtype=np.int64)
        self.A = idx // k
        self.B = idx % k
        self.powers = [pow(r, b, m) for b in range(k)]
        self.pwB = np.array(self.powers, dtype=np.int64)[self.B]

    def inv(self, s):
        """Inverse of element s: (a, b)^{-1} = (-r^{-b} a, -b)."""
        a, b = divmod(s, self.k)
        nb = (-b) % self.k
        return ((-self.powers[nb] * a) % self.m) * self.k + nb

    def rcol(self, s):
        """Array g -> g*s over all g: (a, b)(c, d) = (a + r^b c, b + d)."""
        c, d = divmod(s, self.k)
        return ((self.A + self.pwB * c) % self.m) * self.k + (self.B + d) % self.k


def _uncovered(N, Fw, Bw, start, D):
    """Count vertices not reached within D steps from a_e (start=0) or b_e (start=1)."""
    rA = np.zeros(N, dtype=bool)
    rB = np.zeros(N, dtype=bool)
    if start == 0:
        rA[0] = True
    else:
        rB[0] = True
    side = start
    for _ in range(D):
        if side == 0:
            for f in Fw:
                rB[f[rA]] = True
        else:
            for g in Bw:
                rA[g[rB]] = True
        side ^= 1
    return int(N - rA.sum()) + int(N - rB.sum())


def _cayley_cost(G, S, D):
    """Number of unreached (vertex, start) pairs; zero iff the Haar graph has diameter <= D."""
    Fw = [G.rcol(s) for s in S]
    Bw = [G.rcol(G.inv(s)) for s in S]
    return _uncovered(G.N, Fw, Bw, 0, D) + _uncovered(G.N, Fw, Bw, 1, D)


def _cayley_edges(G, S):
    """Edge list of the Haar graph: A-vertex g is g, B-vertex h is N + h."""
    N = G.N
    edges = []
    for s in S:
        f = G.rcol(s).tolist()
        edges.extend((g, N + f[g]) for g in range(N))
    return edges


def _group_candidates(n_lo, n_hi, d, rng):
    """List of (N, m, k, r) semidirect-product options with N = m*k in [n_lo, n_hi] and N >= d."""
    cands = []
    for N in range(max(n_lo, d), n_hi + 1):
        for k in range(1, min(12, N) + 1):
            if N % k:
                continue
            m = N // k
            if m < 2:
                continue
            if k == 1:
                rs = [1]
            else:
                target = 1 % m
                rs = [r for r in range(1, m)
                      if math.gcd(r, m) == 1 and pow(r, k, m) == target]
                if len(rs) > 2:
                    rs = rng.sample(rs, 2)
            for r in rs:
                cands.append((N, m, k, r))
    rng.shuffle(cands)
    cands.sort(key=lambda c: c[0])
    return cands


def _cayley_search(d, D, floor, rng, deadline):
    """Round-robin local search over group candidates; return the largest valid (n, edges) with n > floor, or None."""
    n_lo = floor // 2 + 1
    cands = _group_candidates(n_lo, n_lo + 30, d, rng)
    states = {}
    result = None
    SLICE = 120
    while cands and time.monotonic() < deadline:
        for c in list(cands):
            if time.monotonic() >= deadline:
                break
            if 2 * c[0] <= floor:
                continue
            st = states.get(c)
            if st is None:
                G = _Group(c[1], c[2], c[3])
                S = rng.sample(range(G.N), d)
                cost = _cayley_cost(G, S, D)
                st = {"G": G, "S": S, "cost": cost, "best": cost, "stale": 0}
                states[c] = st
            G = st["G"]
            S = st["S"]
            cost = st["cost"]
            for _ in range(SLICE):
                if cost == 0 or time.monotonic() >= deadline:
                    break
                x = rng.randrange(G.N)
                if x in S:
                    continue
                S2 = list(S)
                S2[rng.randrange(d)] = x
                c2 = _cayley_cost(G, S2, D)
                if c2 <= cost or rng.random() < 0.02:
                    S, cost = S2, c2
                if cost < st["best"]:
                    st["best"] = cost
                    st["stale"] = 0
                else:
                    st["stale"] += 1
                if st["stale"] > 500:
                    S = rng.sample(range(G.N), d)
                    cost = _cayley_cost(G, S, D)
                    st["best"] = cost
                    st["stale"] = 0
            st["S"] = S
            st["cost"] = cost
            if cost == 0:
                n = 2 * G.N
                edges = _cayley_edges(G, S)
                if lib.is_valid(n, edges, d, D):
                    result = (n, edges)
                    floor = n
                    cands = [x for x in cands if 2 * x[0] > floor]
                else:
                    cands.remove(c)
    return result


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 10.0))
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

    # Parent pipeline gets the first half of the budget.
    deadline = t0 + 0.5 * budget

    # Phase 1: cyclic random Haar graphs.
    try:
        m_hi = max(d, lib._moore_bound(d, D) // 2)
        m, S = _haar_search(d, D, m_hi, rng, t0 + 0.25 * budget, 1500)
        consider(*lib.haar_graph(m, S))
    except Exception:
        pass

    # Phase 2: algebraic constructions.
    if D >= 3 and lib.is_prime_power(d - 1):
        try:
            consider(*lib.projective_plane_incidence(d - 1))
        except Exception:
            pass

    if D >= 4 and lib.is_prime_power(d - 1) and 2 <= d - 1 <= 11:
        try:
            consider(*_gq_incidence(d - 1))
        except Exception:
            pass

    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            now = time.monotonic()
            twin_deadline = now + 0.5 * (deadline - now)
            n2, e2 = _twin_graph(d - 2, twin_deadline, rng)
            consider(n2, e2)
            n3, e3 = _extend(n2, e2, d, deadline, rng)
            consider(n3, e3)
        except Exception:
            pass

    # Phase 3 (bold): Cayley-type search over non-abelian groups, aiming above the current best.
    if d >= 4 and D >= 3:
        try:
            res = _cayley_search(d, D, best[0], rng, t0 + 0.92 * budget)
            if res is not None:
                consider(*res)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
