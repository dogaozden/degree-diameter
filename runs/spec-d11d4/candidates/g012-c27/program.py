import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Parent constructions (kept as the fallback route).
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
# NEW ROUTE: bi-Cayley graphs over semidirect groups Z_m x|_r Z_k.
#
# Vertices are A-copies and B-copies of a group G (|G| = N); A-vertex x is
# adjacent to B-vertex x*s for each s in a connection set S of size d.
# Left multiplication is an automorphism, so the diameter is at most D iff
# BFS from (A, e) and from (B, e) reach everything within D steps.
# A simulated-annealing search over S minimises the number of unreached
# vertices. Everything is vectorised with numpy, and the result is verified
# with lib.is_valid before use.
# ----------------------------------------------------------------------------

def _moore(d, D):
    if D == 0 or d == 0:
        return 1
    if d == 1:
        return min(2, D + 1)
    if d == 2:
        return 2 * D
    return 2 * sum((d - 1) ** i for i in range(D))


def _group_options(N, rng):
    """Candidate semidirect groups (m, k, r) of order N = m*k, shuffled and capped."""
    opts = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        if k == 1:
            opts.append((m, 1, 1))
            continue
        rs = [r for r in range(1, m)
              if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if len(rs) > 4:
            rs = rng.sample(rs, 4)
        opts.extend((m, k, r) for r in rs)
    rng.shuffle(opts)
    return opts[:12]


def _right_table(m, k, r):
    """tab[g, x] = x*g in Z_m x|_r Z_k (element (a,b) coded as a*k+b); inv[g] = index of g^-1."""
    N = m * k
    pw = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    x = np.arange(N, dtype=np.int64)
    a = x // k
    b = x % k
    tab = np.empty((N, N), dtype=np.int64)
    inv = np.empty(N, dtype=np.int64)
    for g in range(N):
        c, dv = divmod(g, k)
        tab[g] = ((a + pw[b] * c) % m) * k + (b + dv) % k
        dinv = (-dv) % k
        cinv = (-int(pw[dinv]) * c) % m
        inv[g] = cinv * k + dinv
    return tab, inv


def _deficiency(tab, inv, S, N, D):
    """Number of (root, vertex) pairs not reached within D steps, for roots A-e and B-e."""
    Pm = tab[S]          # Pm[i, x] = x * s_i   (A -> B)
    Qm = tab[inv[S]]     # Qm[i, y] = y * s_i^-1 (B -> A)
    total = 0
    for side in (0, 1):
        visA = np.zeros(N, dtype=bool)
        visB = np.zeros(N, dtype=bool)
        fr = np.array([0], dtype=np.int64)
        if side == 0:
            visA[0] = True
            on_a = True
        else:
            visB[0] = True
            on_a = False
        for _ in range(D):
            new = np.zeros(N, dtype=bool)
            if on_a:
                new[Pm[:, fr].ravel()] = True
                new &= ~visB
                visB |= new
            else:
                new[Qm[:, fr].ravel()] = True
                new &= ~visA
                visA |= new
            fr = np.flatnonzero(new)
            if fr.size == 0:
                break
            on_a = not on_a
        total += 2 * N - int(visA.sum()) - int(visB.sum())
    return total


def _anneal(tab, inv, N, d, D, rng, deadline):
    """Simulated annealing for a connection set S of size d with deficiency 0, or None."""
    S = rng.sample(range(N), d)
    Sarr = np.array(S, dtype=np.int64)
    cur = _deficiency(tab, inv, Sarr, N, D)
    t_start = time.monotonic()
    span = max(1e-3, deadline - t_start)
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        frac = (now - t_start) / span
        T = 0.05 + 1.5 * (1.0 - frac)
        i = rng.randrange(d)
        g = rng.randrange(N)
        if g in S:
            continue
        old = S[i]
        S[i] = g
        Sarr[i] = g
        new = _deficiency(tab, inv, Sarr, N, D)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = new
        else:
            S[i] = old
            Sarr[i] = old
    return list(S) if cur == 0 else None


def _bicayley_search(d, D, rng, N_lo, N_hi, deadline):
    """Find the largest valid bi-Cayley graph with N_lo <= |G| <= N_hi; return (n, edges) or None."""
    best = None
    N = N_lo
    while N <= N_hi and time.monotonic() < deadline - 0.5:
        remaining = deadline - time.monotonic()
        budget = max(1.0, 0.6 * remaining)
        opts = _group_options(N, rng)
        if not opts:
            N += 1
            continue
        per_opt = budget / len(opts)
        found = None
        for (m, k, r) in opts:
            if time.monotonic() >= deadline - 0.5:
                break
            end = min(deadline, time.monotonic() + per_opt)
            tab, inv = _right_table(m, k, r)
            S = _anneal(tab, inv, N, d, D, rng, end)
            if S is None:
                continue
            edges = []
            for g in S:
                row = tab[g].tolist()
                edges.extend((x, N + row[x]) for x in range(N))
            if lib.is_valid(2 * N, edges, d, D):
                found = (2 * N, edges)
                break
        if found is None:
            break
        best = found
        N += 1
    return best


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

    # Parent route, given a share of the budget.
    pdeadline = start + 0.3 * time_limit
    pg = _pg(d)
    if pg is not None:
        consider(pg[0], pg[1])

    q = d - 2
    if 2 <= q <= 11 and lib.is_prime_power(q) and time.monotonic() < pdeadline - 2.0:
        if D >= 4:
            n0, e0 = _gq(q)
        elif D == 3:
            n0, e0 = lib.projective_plane_incidence(q)
        else:
            n0, e0 = 0, []
        if n0 > 0:
            consider(n0, e0)
            res = _blowup(n0, e0, d, pdeadline, rng, nprng)
            if res is not None:
                consider(res[0], res[1])

    # Bold route: bi-Cayley search for orders above the current best.
    moore = _moore(d, D)
    if d >= 3 and D >= 3 and best_n < moore:
        sdeadline = start + max(1.0, 0.88 * time_limit - 2.0)
        N_lo = max(best_n // 2 + 1, d)
        N_hi = min(moore // 2, 1500)
        if N_lo <= N_hi and time.monotonic() < sdeadline:
            res = _bicayley_search(d, D, rng, N_lo, N_hi, sdeadline)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
