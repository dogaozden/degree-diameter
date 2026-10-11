import itertools
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q): points 0..P-1, lines as sorted point lists.
# ----------------------------------------------------------------------------

def _gq_lines(q):
    """Return (P, lines) for the symplectic generalized quadrangle W(q)."""
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
    return P, lines


def _gq_incidence(q):
    """Incidence graph of W(q): degree q+1, diameter 4."""
    P, lines = _gq_lines(q)
    return P + len(lines), [(p, P + j) for j, Ls in enumerate(lines) for p in Ls]


# ----------------------------------------------------------------------------
# Iterated local search for a large independent set (numpy-assisted).
# ----------------------------------------------------------------------------

def _mis(adj, rng, nprng, deadline, target):
    N = len(adj)
    if N == 0:
        return []
    nb = [np.asarray(a, dtype=np.int64) for a in adj]
    cnt = np.zeros(N, dtype=np.int64)
    inS = np.zeros(N, dtype=bool)
    tabu = np.zeros(N, dtype=np.int64)
    S = []
    conf = 0
    best = []
    it = 0
    last = 0

    def add(v):
        nonlocal conf
        conf += int(cnt[v])
        cnt[nb[v]] += 1
        inS[v] = True
        S.append(v)

    def remove(u):
        nonlocal conf
        conf -= int(cnt[u])
        cnt[nb[u]] -= 1
        inS[u] = False
        S.remove(u)

    def pick():
        mask = (~inS) & (tabu <= it)
        if not mask.any():
            mask = ~inS
            if not mask.any():
                return -1
        score = np.where(mask, cnt + nprng.random(N) * 0.5, np.inf)
        return int(np.argmin(score))

    while time.monotonic() < deadline:
        it += 1
        if conf == 0:
            if len(S) > len(best):
                best = list(S)
                last = it
            if len(best) >= target:
                break
            v = pick()
            if v < 0:
                break
            add(v)
        else:
            conflicting = [u for u in S if cnt[u] > 0]
            u = conflicting[rng.randrange(len(conflicting))]
            remove(u)
            tabu[u] = it + 5 + rng.randrange(8)
            v = pick()
            if v >= 0:
                add(v)
        if S and it - last > 15000:
            u = S[rng.randrange(len(S))]
            remove(u)
            tabu[u] = it + 5
            last = it
    if conf == 0 and len(S) > len(best):
        best = list(S)
    return best


# ----------------------------------------------------------------------------
# Twin construction on W(q), degree q+2:
#   point twins (pairwise non-collinear points I) attached to lines through p,
#   line twins (pairwise disjoint lines J, a spread) attached to points of L.
# Twins preserve distances, so diameter 4 is kept.
# ----------------------------------------------------------------------------

def _twin(q, deadline, rng, nprng):
    P, lines = _gq_lines(q)
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
    rem = max(0.0, deadline - now)
    J = _mis([sorted(s) for s in ladj], rng, nprng, now + 0.35 * rem, q * q + 1)
    I = _mis([sorted(s) for s in padj], rng, nprng, deadline, q * q + 1)

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
# Greedy extension by new vertices. Adding a vertex x adjacent to T keeps the
# diameter <= D iff every vertex lies within distance D-1 of T. This is checked
# exactly with bitmask balls, so no full validation is needed per step.
# ----------------------------------------------------------------------------

def _balls(n, adj, r):
    reach = [1 << v for v in range(n)]
    for _ in range(r):
        new = [0] * n
        for v in range(n):
            acc = reach[v]
            for u in adj[v]:
                acc |= reach[u]
            new[v] = acc
        reach = new
    return reach


def _cover(cands, balls, n, d, rng, tries):
    full = (1 << n) - 1
    for _ in range(tries):
        unc = full
        chosen = []
        avail = list(cands)
        while unc and len(chosen) < d and avail:
            bg, bv, bt = -1, -1, -1.0
            for v in avail:
                g = (balls[v] & unc).bit_count()
                if g == 0:
                    continue
                t = rng.random()
                if g > bg or (g == bg and t > bt):
                    bg, bv, bt = g, v, t
            if bv < 0:
                break
            chosen.append(bv)
            unc &= ~balls[bv]
            avail.remove(bv)
        if not unc:
            return chosen
    return None


def _two_colour(n, adj):
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


def _extend(n, edges, d, D, deadline, rng):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    color = _two_colour(n, adj)
    r = D - 1
    side = 0
    while time.monotonic() < deadline:
        balls = _balls(n, adj, r)
        placed = False
        for s in (side, 1 - side):
            cands = [v for v in range(n) if color[v] == 1 - s and deg[v] < d]
            if not cands:
                continue
            chosen = _cover(cands, balls, n, d, rng, 6)
            if chosen is None:
                continue
            x = n
            n += 1
            adj.append(list(chosen))
            deg.append(len(chosen))
            color.append(s)
            for t in chosen:
                adj[t].append(x)
                deg[t] += 1
            side = 1 - s
            placed = True
            break
        if not placed:
            break
    return n, [(u, v) for u in range(n) for v in adj[u] if u < v]


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 10.0))
    deadline = t0 + budget
    twin_deadline = t0 + 0.6 * budget
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

    if D >= 3 and lib.is_prime_power(d - 1):
        try:
            consider(*lib.projective_plane_incidence(d - 1))
        except Exception:
            pass

    if D >= 4 and 2 <= d - 1 <= 11 and lib.is_prime_power(d - 1):
        try:
            consider(*_gq_incidence(d - 1))
        except Exception:
            pass

    q = d - 2
    if D >= 4 and 2 <= q <= 11 and lib.is_prime_power(q):
        try:
            consider(*_twin(q, twin_deadline, rng, nprng))
        except Exception:
            pass

    # Use leftover time to add vertices exactly into spare degree slots.
    if time.monotonic() < deadline - 1.0:
        try:
            ext_n, ext_e = _extend(best[0], best[1], d, D, deadline, rng)
            if ext_n > best[0] and lib.is_valid(ext_n, ext_e, d, D):
                best = (ext_n, ext_e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return lib.haar_graph(d, range(d))
    return best
