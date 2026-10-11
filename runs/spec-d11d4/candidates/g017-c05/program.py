import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Bases (unchanged from the parent).
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


# ----------------------------------------------------------------------------
# Twin blow-up (unchanged from the parent).
# ----------------------------------------------------------------------------

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

    if N == 0:
        return []

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


def _side_search(V, cs, rng, nprng, deadline):
    idx = {v: i for i, v in enumerate(V)}
    nb_local = [[idx[w] for w in cs[v] if w in idx] for v in V]
    res = _independent_set(len(V), nb_local, rng, nprng, deadline)
    return [V[i] for i in res]


def _two_colour(n, edges):
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
            x = stack.pop()
            for y in adj[x]:
                if color[y] == -1:
                    color[y] = 1 - color[x]
                    stack.append(y)
    return color


def _blow(n0, edges0, S):
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
    if n0 <= 60:
        deadline = min(deadline, time.monotonic() + 2.0)
    color = _two_colour(n0, edges0)
    sides = [[v for v in range(n0) if color[v] == c] for c in (0, 1)]

    now = time.monotonic()
    total = max(0.0, deadline - now)
    S = []
    S += _side_search(sides[0], cs, rng, nprng, now + 0.5 * total)
    S += _side_search(sides[1], cs, rng, nprng, deadline)
    return _blow(n0, edges0, S)


# ----------------------------------------------------------------------------
# New bold route: Haar graphs of small NON-ABELIAN groups for diameter 4.
#
# Haar graph H(G, S): parts a_x, b_y (x, y in G), edges a_x -- b_{x s} for s in S.
# It is bipartite and |S|-regular on 2|G| vertices, and left multiplication is an
# automorphism, so the diameter is <= 4 iff, with T1 = {s_i s_j^-1} and
# U1 = {s_i^-1 s_j},
#   odd  : {e-free words} S u S*T1 ... i.e. S u {s_i s_j^-1 s_k}  covers G  (a-b pairs)
#   even : {e} u T1 u T1.T1 covers G   (a-a pairs)
#   even : {e} u U1 u U1.U1 covers G   (b-b pairs)
# Abelian groups cannot reach orders above about 740 this way, hence non-abelian
# semidirect products Z_m x| Z_k are used. Any result is verified with lib.is_valid,
# and the parent's graph is kept whenever the search does not beat it.
# ----------------------------------------------------------------------------

def _semidirect_table(m, k, r):
    """Multiplication table of Z_m x|_r Z_k, element (a, b) coded as a*k + b."""
    N = m * k
    X = np.arange(N, dtype=np.int64)
    a = X // k
    b = X % k
    pw = np.array([pow(r, t, m) for t in range(k)], dtype=np.int64)
    A = a[:, None]
    B = b[:, None]
    C = a[None, :]
    E = b[None, :]
    return ((A + pw[B] * C) % m) * k + (B + E) % k


def _groups_of_order(N):
    """(m, k, r) giving non-abelian semidirect groups of order N = m*k."""
    out = []
    for k in range(2, N // 3 + 1):
        if N % k:
            continue
        m = N // k
        if m < 3:
            continue
        for r in range(2, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1:
                out.append((m, k, r))
    return out


def _haar_cost(M, invT, N, Sa):
    """Number of uncovered group elements over the three coverage conditions (0 = diameter 4)."""
    invS = invT[Sa]
    T1 = M[Sa[:, None], invS[None, :]]          # s_i s_j^-1
    U1 = M[invS[:, None], Sa[None, :]]          # s_i^-1 s_j
    fT = T1.ravel()
    fU = U1.ravel()
    odd = np.concatenate([Sa, M[T1[:, :, None], Sa[None, None, :]].ravel()])
    ev = np.concatenate([np.array([0], dtype=np.int64), fT,
                         M[fT[:, None], fT[None, :]].ravel()])
    ev2 = np.concatenate([np.array([0], dtype=np.int64), fU,
                          M[fU[:, None], fU[None, :]].ravel()])
    cost = 0
    for arr in (odd, ev, ev2):
        c = np.zeros(N, dtype=bool)
        c[arr] = True
        cost += N - int(c.sum())
    return cost


def _haar_search(M, invT, N, d, rng, deadline):
    """Local search over d-element connection sets S with zero coverage cost."""
    S = rng.sample(range(N), d)
    Sa = np.array(S, dtype=np.int64)
    f = _haar_cost(M, invT, N, Sa)
    stall = 0
    while f > 0:
        if time.monotonic() >= deadline:
            return None
        i = rng.randrange(d)
        c = rng.randrange(N)
        if c in S:
            continue
        old = S[i]
        S[i] = c
        Sa[i] = c
        f2 = _haar_cost(M, invT, N, Sa)
        if f2 <= f:
            stall = 0 if f2 < f else stall + 1
            f = f2
        else:
            S[i] = old
            Sa[i] = old
            stall += 1
        if stall > 3000:
            j = rng.randrange(d)
            while True:
                c = rng.randrange(N)
                if c not in S:
                    break
            S[j] = c
            Sa[j] = c
            f = _haar_cost(M, invT, N, Sa)
            stall = 0
    return Sa


def _haar_graph_from(M, Sa, N):
    """Haar graph on 2N vertices: a_x = x, b_y = N + y."""
    Y = M[np.arange(N)[:, None], Sa[None, :]].tolist()
    edges = [(x, N + y) for x, row in enumerate(Y) for y in row]
    return 2 * N, edges


def _haar_route(d, lo, rng, deadline):
    """Search Haar graphs of order N = |G| >= lo, increasing N while time allows."""
    result = None
    N = max(lo, d)
    limit = lo + 150
    while N <= limit and time.monotonic() < deadline - 0.3:
        cands = _groups_of_order(N)
        rng.shuffle(cands)
        found = None
        for (m, k, r) in cands:
            now = time.monotonic()
            rem = deadline - now
            if rem <= 0.3:
                break
            end = now + min(rem, max(0.6, min(2.5, rem / 4.0)))
            M = _semidirect_table(m, k, r)
            invT = np.argmax(M == 0, axis=1)
            Sa = _haar_search(M, invT, N, d, rng, end)
            if Sa is not None:
                found = (M, Sa)
                break
        if found is not None:
            n2, edges = _haar_graph_from(found[0], found[1], N)
            result = (n2, edges)
        N += 1
    return result


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    # Parent route gets the first part of the budget; the Haar route uses the rest.
    deadline = start + max(0.5, 0.72 * time_limit - 4.0)
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

    # Blow-up route: base of degree exactly d-1 with q = d-2 a prime power.
    q = d - 2
    if 2 <= q <= 11 and lib.is_prime_power(q) and time.monotonic() < deadline - 2.0:
        if D >= 4:
            n0, e0 = _gq(q)
        elif D == 3:
            n0, e0 = lib.projective_plane_incidence(q)
        else:
            n0, e0 = 0, []
        if n0 > 0:
            consider(n0, e0)
            res = _blowup(n0, e0, d, deadline, rng, nprng)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))

    # Bold route (diameter 4 only): Haar graphs of non-abelian groups.
    if D == 4 and d >= 4:
        haar_deadline = start + max(0.0, 0.9 * time_limit - 2.0)
        try:
            res = _haar_route(d, best[0] // 2 + 1, rng, haar_deadline)
        except Exception:
            res = None
        if res is not None and res[0] > best[0] and lib.is_valid(res[0], res[1], d, D):
            best = res

    return best
