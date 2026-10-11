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
MAX_FAILS = 20000


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

    reach = _ball3(n, adj)
    fails = 0
    while time.monotonic() < deadline:
        spare = [v for v in range(n) if len(adj[v]) < d]
        if not spare or fails >= MAX_FAILS:
            break
        full = (1 << n) - 1
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
        reach = _ball3(n, adj)
        fails = 0
    return n, edges


# ----------------------------------------------------------------------------
# Cyclic Haar-graph search: generic fallback.
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
# NEW BOLD BRANCH: bi-Cayley graphs over a group G of order M.
#
# Vertices a_x and b_x (x in G). Connection set S of size d; edges a_x -- b_{x s}.
# This is d-regular and bipartite. Left translation by g is an automorphism,
# so diameter <= D holds iff BFS from a_e and from b_e reaches everything in D steps.
# Connection sets are found by simulated annealing on the number of unreached
# vertices, and the order M is bisected upward.
# ----------------------------------------------------------------------------

def _make_group(M, rng):
    """Return (mt, invl): mt[x][s] = x*s and invl[s] = s^-1 for a random group of order M."""
    ks = [k for k in range(2, 13) if M % k == 0 and M // k >= 3]
    if ks and rng.random() < 0.6:
        for _ in range(60):
            k = rng.choice(ks)
            m = M // k
            r = rng.randrange(2, m)
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                _, mul, inv = lib.semidirect_group(m, k, r)
                mt = [[mul(x, s) for s in range(M)] for x in range(M)]
                invl = [inv(s) for s in range(M)]
                return mt, invl
    mt = [[(x + s) % M for s in range(M)] for x in range(M)]
    invl = [(-s) % M for s in range(M)]
    return mt, invl


def _cost(M, mt, S, Sinv, D):
    """Total number of (source, vertex) pairs NOT within distance D, for sources a_e and b_e."""
    total = 0
    for src in (0, M):
        seen = bytearray(2 * M)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for v in frontier:
                if v < M:
                    row = mt[v]
                    for s in S:
                        w = M + row[s]
                        if not seen[w]:
                            seen[w] = 1
                            nxt.append(w)
                else:
                    row = mt[v - M]
                    for si in Sinv:
                        w = row[si]
                        if not seen[w]:
                            seen[w] = 1
                            nxt.append(w)
            cnt += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += 2 * M - cnt
    return total


def _anneal(M, mt, invl, d, D, deadline, rng):
    """Search a connection set S (|S| = d) with zero cost; return S or None at deadline."""
    S = rng.sample(range(M), d)
    cur = _cost(M, mt, S, [invl[s] for s in S], D)
    T = 0.6
    while cur > 0:
        if time.monotonic() > deadline:
            return None
        i = rng.randrange(d)
        c = rng.randrange(M)
        if c in S:
            continue
        old = S[i]
        S[i] = c
        new = _cost(M, mt, S, [invl[s] for s in S], D)
        if new <= cur or rng.random() < math.exp(-(new - cur) / T):
            cur = new
        else:
            S[i] = old
    return S


def _bold(d, D, rng, deadline, consider):
    """Bisect the bi-Cayley group order M, annealing a connection set at each M."""
    lo, hi = None, None
    M = max(d + 1, 300)
    while time.monotonic() < deadline:
        now = time.monotonic()
        remaining = deadline - now
        slice_end = min(deadline, now + max(2.0, remaining * 0.5))
        mt, invl = _make_group(M, rng)
        S = _anneal(M, mt, invl, d, D, slice_end, rng)
        if S is not None:
            edges = [(x, M + mt[x][s]) for x in range(M) for s in S]
            consider(2 * M, edges)
            lo = M
        else:
            hi = M
        if lo is None:
            if hi <= d + 1:
                break
            M = max(d + 1, int(hi * 0.85))
        elif hi is None:
            M = int(lo * 1.05) + 1
        else:
            if hi - lo <= 2:
                break
            M = (lo + hi) // 2


# ----------------------------------------------------------------------------
# Legacy pipeline (projective plane, twin graph plus extension, GQ incidence).
# ----------------------------------------------------------------------------

def _legacy(d, D, rng, deadline, consider, state):
    structured = False

    if D >= 3 and lib.is_prime_power(d - 1):
        before = state[0]
        try:
            consider(*lib.projective_plane_incidence(d - 1))
        except Exception:
            pass
        if state[0] > before:
            structured = True
        if D == 3 and structured:
            return

    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        q = d - 2
        attempts = 6
        for attempt in range(attempts):
            now = time.monotonic()
            rem = deadline - now
            if rem < 3.0:
                break
            share = rem / (attempts - attempt)
            tw_dl = now + share * 0.25
            ex_dl = now + share
            try:
                n2, e2 = _twin_graph(q, tw_dl, rng)
                before = state[0]
                consider(n2, e2)
                if state[0] > before:
                    structured = True
                n3, e3 = _extend(n2, e2, d, ex_dl, rng)
                before = state[0]
                consider(n3, e3)
                if state[0] > before:
                    structured = True
            except Exception:
                pass

    if D >= 4 and lib.is_prime_power(d - 1) and 2 <= d - 1 <= 11 and time.monotonic() < deadline:
        try:
            before = state[0]
            consider(*_gq_incidence(d - 1))
            if state[0] > before:
                structured = True
        except Exception:
            pass

    if not structured and time.monotonic() < deadline:
        _haar_search(d, deadline, D, rng, consider)


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.92 * time_limit, time_limit - 5.0))
    deadline = t0 + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, valid for D >= 2.
    base = lib.haar_graph(d, range(d))
    state = [base[0], base[1]]

    def consider(n, edges):
        if n > state[0] and lib.is_valid(n, edges, d, D):
            state[0] = n
            state[1] = edges

    # Legacy pipeline gets most of the budget; the bold branch gets the rest.
    _legacy(d, D, rng, t0 + 0.7 * budget, consider, state)

    if d >= 3 and D >= 2 and state[0] < lib.moore_bound(d, D) and time.monotonic() < deadline:
        try:
            _bold(d, D, rng, deadline, consider)
        except Exception:
            pass

    n, edges = state
    if not lib.is_valid(n, edges, d, D):
        return 2, [(0, 1)]
    return n, edges
