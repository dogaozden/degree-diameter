import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Bases from the parent program (kept as the safe fallback route).
# ----------------------------------------------------------------------------

def _pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1, or None."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq(q):
    """Point-line incidence graph of the symplectic generalized quadrangle W(q)."""
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
    edges = [(p, P + j) for j, L in enumerate(lines) for p in L]
    return P + len(lines), edges


def _independent_set(N, nb, rng, nprng, deadline):
    """Iterated local search for a large set of vertices with no conflicting pair."""
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


def _blow(n0, edges0, S):
    """Blow up each vertex of S into two twin copies (same neighbourhood)."""
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


def _blowup(n0, edges0, d, deadline, rng, nprng):
    """Twin blow-up of a base graph of degree d-1 by a large distance-2-free set."""
    adj = [[] for _ in range(n0)]
    for u, v in edges0:
        adj[u].append(v)
        adj[v].append(u)
    if any(len(a) != d - 1 for a in adj):
        return None
    cs = [set() for _ in range(n0)]
    for w in range(n0):
        a = adj[w]
        for i in range(len(a)):
            for j in range(i + 1, len(a)):
                x, y = a[i], a[j]
                cs[x].add(y)
                cs[y].add(x)
    nb = [sorted(s) for s in cs]
    if n0 <= 60:
        deadline = min(deadline, time.monotonic() + 2.0)
    S = _independent_set(n0, nb, rng, nprng, deadline)
    return _blow(n0, edges0, S)


# ----------------------------------------------------------------------------
# NEW ROUTE: bi-Cayley graphs (two base vertices, group lift).
#
# Base graph: vertices A and B, with d darts A->B labelled by distinct group
# elements s in S. Vertices are (A,x) and (B,x) for x in G, and (A,x) ~ (B,x*s).
# Left multiplication by G is an automorphism, so the graph is vertex-transitive
# on each side. Diameter <= D reduces to two BFS checks, one from (A,e) and one
# from (B,e). The search uses semidirect products Z_m x|_r Z_k (k=1 is cyclic)
# and a local search over S that minimises the number of unreached vertices.
# Any candidate is confirmed with lib.is_valid before it is accepted.
# ----------------------------------------------------------------------------

def _group_table(m, k, r):
    """Multiplication table and right-inverse table for Z_m x|_r Z_k, element (a,b) coded a*k+b."""
    N = m * k
    idx = np.arange(N, dtype=np.int64)
    a = idx // k
    b = idx % k
    pw = np.array([pow(r, bb, m) for bb in range(k)], dtype=np.int64)
    Mt = ((a[:, None] + pw[b][:, None] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
    rows, cols = np.nonzero(Mt == 0)
    inv = np.empty(N, dtype=np.int64)
    inv[rows] = cols
    return Mt, inv


def _groups(N, rng):
    """Candidate (m, k, r) with m*k = N: cyclic, plus a few semidirect products."""
    out = []
    for m in range(2, N + 1):
        if N % m:
            continue
        k = N // m
        if k == 1:
            out.append((m, 1, 1))
            continue
        rs = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if not rs:
            continue
        pick = [1] if 1 in rs else []
        others = [r for r in rs if r != 1]
        rng.shuffle(others)
        pick += others[:3]
        for r in pick:
            out.append((m, k, r))
    rng.shuffle(out)
    return out


def _cost(S, Mt, inv, N, depth):
    """Number of vertex pairs (source, target) not reached within `depth` from (A,e) and (B,e)."""
    Sarr = np.asarray(S, dtype=np.int64)
    Sinv = inv[Sarr]
    total = 0
    for src in (0, N):
        vis = np.zeros(2 * N, dtype=bool)
        vis[src] = True
        front = np.array([src], dtype=np.int64)
        for _ in range(depth):
            fa = front[front < N]
            fb = front[front >= N] - N
            parts = []
            if fa.size:
                parts.append(N + Mt[fa[:, None], Sarr[None, :]].ravel())
            if fb.size:
                parts.append(Mt[fb[:, None], Sinv[None, :]].ravel())
            if not parts:
                break
            nxt = np.unique(np.concatenate(parts))
            nxt = nxt[~vis[nxt]]
            if nxt.size == 0:
                break
            vis[nxt] = True
            front = nxt
        total += 2 * N - int(vis.sum())
    return total


def _search_group(Mt, inv, N, d, depth, rng, steps):
    """Local search for a connection set S of size d with zero cost, or None."""
    S = rng.sample(range(N), d)
    cur = _cost(S, Mt, inv, N, depth)
    inS = set(S)
    for _ in range(steps):
        if cur == 0:
            return S
        i = rng.randrange(d)
        g = rng.randrange(N)
        if g in inS:
            continue
        T = S[:]
        T[i] = g
        c = _cost(T, Mt, inv, N, depth)
        if c <= cur or rng.random() < 0.01:
            inS.discard(S[i])
            inS.add(g)
            S = T
            cur = c
    return S if cur == 0 else None


def _bicayley(d, D, best_n, deadline, rng, on_success):
    """Search increasing group orders N; each success gives a graph with 2N vertices."""
    hi = min(lib._moore_bound(d, D) // 2, 1500)
    N = best_n // 2 + 1
    while N <= hi and time.monotonic() < deadline:
        now = time.monotonic()
        cap = now + max(1.0, 0.4 * (deadline - now))
        groups = _groups(N, rng)
        succ = None
        if groups:
            gi = 0
            while succ is None and time.monotonic() < cap:
                m, k, r = groups[gi % len(groups)]
                gi += 1
                Mt, inv = _group_table(m, k, r)
                S = _search_group(Mt, inv, N, d, D, rng, 400)
                if S is not None:
                    succ = (Mt, S)
        if succ is None:
            break
        on_success(N, succ[0], succ[1])
        N += 1


def _lift_edges(Mt, N, S):
    """Edges of the bi-Cayley graph: (A,x) joined to (B, x*s) for s in S."""
    edges = []
    for x in range(N):
        for g in S:
            edges.append((x, N + int(Mt[x, g])))
    return 2 * N, edges


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)
    nprng = np.random.default_rng(abs(int(seed)) % (2 ** 32))

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    pg = _pg(d)
    if pg is not None:
        consider(pg[0], pg[1])

    # Parent's blow-up route, now capped to a share of the time budget.
    q = d - 2
    if 2 <= q <= 11 and lib.is_prime_power(q):
        bl_deadline = start + 0.3 * time_limit
        n0 = 0
        e0 = []
        if D >= 4:
            n0, e0 = _gq(q)
        elif D == 3:
            n0, e0 = lib.projective_plane_incidence(q)
        if n0 > 0:
            consider(n0, e0)
            if time.monotonic() < bl_deadline - 1.0:
                res = _blowup(n0, e0, d, bl_deadline, rng, nprng)
                if res is not None:
                    consider(res[0], res[1])

    # NEW: bi-Cayley group-lift search with the remaining time.
    search_deadline = start + max(0.5, 0.8 * time_limit - 3.0)
    if D >= 3 and d >= 3 and time.monotonic() < search_deadline:
        def on_success(N, Mt, S):
            n2, e2 = _lift_edges(Mt, N, S)
            consider(n2, e2)

        _bicayley(d, D, best_n, search_deadline, rng, on_success)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
