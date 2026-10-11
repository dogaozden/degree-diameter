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
# Maximum independent set by iterated local search with (1,2)-swaps.
# ----------------------------------------------------------------------------

def _mis(n, adj, deadline, rng):
    """Return a large independent set of the graph (n vertices, adj neighbour lists) found before deadline."""
    if n == 0:
        return []
    inS = [False] * n
    c = [0] * n
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
# Bold new construction: bi-Cayley graphs over semidirect products Z_m x| Z_k.
#
# Vertices A_g and B_g (g in G, |G| = N). Edge A_g ~ B_{g*s} for s in S, |S| = d.
# Left multiplication is an automorphism, so the graph is bipartite, d-regular,
# and has diameter <= D iff BFS from A_e and from B_e reaches all 2N vertices
# within D steps. Simulated annealing over S minimises the unreached count.
# ----------------------------------------------------------------------------

SLICE = 4.0


def _group_table(m, k, r):
    """Multiplication table M (N x N) and inverse array for Z_m x| Z_k, element (a,b) coded a*k+b."""
    N = m * k
    pw = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    X = np.arange(N, dtype=np.int64)
    ax, bx = X // k, X % k
    A = (ax[:, None] + pw[bx][:, None] * ax[None, :]) % m
    B = (bx[:, None] + bx[None, :]) % k
    M = A * k + B
    inv = np.argmax(M == 0, axis=1).astype(np.int64)
    return M, inv


def _groups(N, rng):
    """Candidate (m, k, r) with m*k = N; nonabelian first (shuffled), cyclic last."""
    out = []
    for k in range(2, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 3:
            continue
        for r in range(2, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1:
                out.append((m, k, r))
    rng.shuffle(out)
    out = out[:40]
    out.append((N, 1, 1))
    return out


def _bfs_bad(M, N, S, Sinv, D, side0):
    """Number of vertices (of 2N) NOT within distance D of the source (A_e if side0 == 0, else B_e)."""
    visA = np.zeros(N, dtype=bool)
    visB = np.zeros(N, dtype=bool)
    if side0 == 0:
        visA[0] = True
        side = 0
    else:
        visB[0] = True
        side = 1
    front = np.array([0], dtype=np.int64)
    for _ in range(D):
        if side == 0:
            nb = np.unique(M[front[:, None], S[None, :]])
            tgt = visB
        else:
            nb = np.unique(M[front[:, None], Sinv[None, :]])
            tgt = visA
        new = nb[~tgt[nb]]
        tgt[new] = True
        front = new
        side ^= 1
        if front.size == 0:
            break
    return 2 * N - int(visA.sum()) - int(visB.sum())


def _cost_list(M, inv, N, Sl, D):
    arr = np.array(Sl, dtype=np.int64)
    Sinv = inv[arr]
    return _bfs_bad(M, N, arr, Sinv, D, 0) + _bfs_bad(M, N, arr, Sinv, D, 1)


def _sa_group(M, inv, N, d, D, end, rng):
    """Anneal a connection set S of size d; return it if cost reaches 0 before end, else None."""
    S = rng.sample(range(N), d)
    cur = _cost_list(M, inv, N, S, D)
    T = 2.0
    while cur > 0:
        if time.monotonic() >= end:
            return None
        i = rng.randrange(d)
        x = rng.randrange(N)
        if x in S:
            continue
        T2 = list(S)
        T2[i] = x
        c = _cost_list(M, inv, N, T2, D)
        if c <= cur or rng.random() < math.exp(-(c - cur) / T):
            S, cur = T2, c
        T = max(0.15, T * 0.999)
    return S


def _bicayley_phase(d, D, N, Nmax, end, rng, consider):
    """Ascending search over group orders N (graph order 2N); stops at the first order that fails."""
    while N <= Nmax and time.monotonic() < end:
        groups = _groups(N, rng)
        found = None
        for (m, k, r) in groups:
            now = time.monotonic()
            if now >= end:
                break
            M, inv = _group_table(m, k, r)
            found = _sa_group(M, inv, N, d, D, min(end, now + SLICE), rng)
            if found is not None:
                Ss = [int(x) for x in found]
                edges = [(g, N + int(M[g, s])) for g in range(N) for s in Ss]
                consider(2 * N, edges)
                break
        if found is None:
            return
        N += max(2, N // 64)


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

    def consider(n, edges):
        nonlocal best
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)

    moore = lib._moore_bound(d, D)

    # Projective plane incidence graph: degree d, diameter 3.
    if D >= 3 and lib.is_prime_power(d - 1):
        try:
            consider(*lib.projective_plane_incidence(d - 1))
        except Exception:
            pass
    if best[0] >= moore:
        return best

    # Parent pipeline (W(q) quadrangle and twin/extension graphs) gets the first share of time.
    parent_deadline = t0 + 0.4 * budget

    if D >= 4 and lib.is_prime_power(d - 1) and 2 <= d - 1 <= 11:
        try:
            consider(*_gq_incidence(d - 1))
        except Exception:
            pass

    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            now = time.monotonic()
            n2, e2 = _twin_graph(d - 2, now + 0.35 * (parent_deadline - now), rng)
            consider(n2, e2)
            attempts = 3
            for a in range(attempts):
                now = time.monotonic()
                if now >= parent_deadline - 0.5:
                    break
                slice_end = now + (parent_deadline - now) / (attempts - a)
                n3, e3 = _extend(n2, e2, d, min(slice_end, parent_deadline), rng)
                consider(n3, e3)
        except Exception:
            pass

    if best[0] >= moore:
        return best

    # Bold phase: bi-Cayley lifts over non-cyclic groups, starting just above the current best order.
    if d >= 3 and time.monotonic() < deadline - 3.0:
        try:
            N_start = max(d, best[0] // 2 + 1)
            Nmax = moore // 2
            sa_end = deadline - 1.0
            _bicayley_phase(d, D, N_start, Nmax, sa_end, rng, consider)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
