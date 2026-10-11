import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe baseline families (unchanged from parent).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _largest_pp_le(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def _araujo_candidate(d):
    q = _largest_pp_le(d - 2)
    if q is None or q < 3:
        return None
    try:
        return lib.araujo_lopez_graph(q)
    except Exception:
        return None


def _fill_slack(n, edges, d, seed):
    adjs = [set() for _ in range(n)]
    for u, v in edges:
        adjs[u].add(v)
        adjs[v].add(u)
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for w in adjs[u]:
                if color[w] == -1:
                    color[w] = 1 - color[u]
                    stack.append(w)
    deg = [len(a) for a in adjs]
    rng = random.Random(seed)
    out = list(edges)
    for _ in range(4):
        A = [v for v in range(n) if color[v] == 0 and deg[v] < d]
        B = [v for v in range(n) if color[v] == 1 and deg[v] < d]
        rng.shuffle(A)
        rng.shuffle(B)
        added = False
        for a in A:
            for b in B:
                if deg[a] >= d:
                    break
                if deg[b] < d and b not in adjs[a]:
                    adjs[a].add(b)
                    adjs[b].add(a)
                    deg[a] += 1
                    deg[b] += 1
                    out.append((a, b))
                    added = True
        if not added:
            break
    return n, out


def _greedy_cover(cands, reach, full, d, rng):
    """Pick up to d candidates whose radius-(D-1) balls cover full; return list or None."""
    pool = list(cands)
    rng.shuffle(pool)
    covered = 0
    chosen = []
    while len(chosen) < d and covered != full:
        best = None
        best_gain = 0
        for c in pool:
            g = (reach[c] & ~covered).bit_count()
            if g > best_gain:
                best, best_gain = c, g
        if best is None:
            break
        chosen.append(best)
        covered |= reach[best]
        pool = [c for c in pool if c != best]
    if covered == full:
        return chosen
    return None


def _extend(n, edges, d, D, seed, deadline):
    """Attach new vertices to spare-degree vertices while keeping diameter <= D and bipartiteness."""
    if D < 2 or n == 0:
        return n, list(edges)
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    if any(len(a) > d for a in adj):
        return n, list(edges)
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
                elif color[w] == color[u]:
                    return n, list(edges)
    rng = random.Random(seed)
    out = list(edges)
    R = D - 1
    fails = 0
    while fails < 4 and time.monotonic() < deadline:
        N = len(adj)
        full = (1 << N) - 1
        reach = [1 << v for v in range(N)]
        for _ in range(R):
            nxt = []
            for v in range(N):
                r = reach[v]
                for u in adj[v]:
                    r |= reach[u]
                nxt.append(r)
            reach = nxt
        added = False
        sides = [0, 1]
        rng.shuffle(sides)
        for opp in sides:
            cands = [c for c in range(N) if color[c] == opp and len(adj[c]) < d]
            if not cands:
                continue
            chosen = _greedy_cover(cands, reach, full, d, rng)
            if chosen:
                x = N
                adj.append(set(chosen))
                color.append(1 - opp)
                for c in chosen:
                    adj[c].add(x)
                    out.append((c, x))
                added = True
                break
        if added:
            fails = 0
        else:
            fails += 1
    return len(adj), out


# ----------------------------------------------------------------------------
# NEW engine: bi-Cayley / Haar-type voltage lifts over semidirect products
# Z_m x| Z_kk, searched by simulated annealing with a numpy BFS cost.
#
# Base graph: k vertices on each side, d layers. Layer l pairs A_i with B_{p_l(i)}
# via voltage s_{l,i}. Vertex (A_i, g) joins (B_j, g*s). Left multiplication by
# the group is an automorphism, so distances from the 2k vertices (A_i, e) and
# (B_j, e) determine the whole diameter. Every vertex has degree exactly d.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _make_group(G, rng):
    """Random semidirect product Z_m x| Z_kk of order G (kk <= 12, m >= 2). Returns (m, kk, pw)."""
    divs = [kk for kk in range(1, 13) if G % kk == 0 and G // kk >= 2]
    if not divs:
        return None
    kk = rng.choice(divs)
    m = G // kk
    r = 1
    if kk > 1:
        for _ in range(80):
            rr = rng.randrange(1, m)
            if math.gcd(rr, m) == 1 and pow(rr, kk, m) == 1 % m:
                r = rr
                break
    pw = np.array([pow(r, b, m) for b in range(kk)], dtype=np.int64)
    return m, kk, pw


def _trial(d, D, k, G, rng, iters, deadline):
    """Anneal voltages for one (k, G) choice. Returns (n, edges) on success, else None."""
    grp = _make_group(G, rng)
    if grp is None:
        return None
    m, kk, pw = grp
    N = 2 * k * G
    codes = np.arange(G, dtype=np.int64)
    a_arr = codes // kk
    b_arr = codes % kk
    p = [rng.sample(range(k), k) for _ in range(d)]
    sv = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    nbr = np.zeros((N, d), dtype=np.int64)

    def set_dart(l, i, s):
        c, dd = divmod(s, kk)
        perm = ((((a_arr + pw[b_arr] * c) % m)) * kk + ((b_arr + dd) % kk)).astype(np.int64)
        inv = np.empty(G, dtype=np.int64)
        inv[perm] = codes
        j = p[l][i]
        nbr[i * G:(i + 1) * G, l] = (k + j) * G + perm
        nbr[(k + j) * G:(k + j + 1) * G, l] = i * G + inv

    def has_dup():
        seen = set()
        for l in range(d):
            for i in range(k):
                t = (i, p[l][i], sv[l][i])
                if t in seen:
                    return True
                seen.add(t)
        return False

    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]

    def cost():
        if has_dup():
            return _BIG
        total = 0
        for src in reps:
            seen = np.zeros(N, dtype=bool)
            seen[src] = True
            frontier = np.array([src], dtype=np.int64)
            cnt = 1
            for _ in range(D):
                nb = nbr[frontier].ravel()
                nb = nb[~seen[nb]]
                if nb.size == 0:
                    break
                nb = np.unique(nb)
                seen[nb] = True
                cnt += int(nb.size)
                frontier = nb
            total += N - cnt
        return total

    for l in range(d):
        for i in range(k):
            set_dart(l, i, sv[l][i])

    cur = cost()
    T0 = 2.0
    for t in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        T = T0 * (1.0 - t / iters) + 0.05
        l = rng.randrange(d)
        i = rng.randrange(k)
        old = sv[l][i]
        new = rng.randrange(G)
        if new == old:
            continue
        sv[l][i] = new
        set_dart(l, i, new)
        c2 = cost()
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
            cur = c2
        else:
            sv[l][i] = old
            set_dart(l, i, old)

    if cur != 0:
        return None
    A_idx = np.repeat(np.arange(k * G, dtype=np.int64), d)
    B_idx = nbr[:k * G].ravel()
    edges = list(zip(A_idx.tolist(), B_idx.tolist()))
    return N, edges


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, min(0.85 * time_limit, time_limit - 4.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    if d <= 1 or D == 2:
        return best
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Baseline families.
    bases = []
    try:
        if D >= 3:
            pg = _best_pg(d)
            if pg is not None:
                bases.append(pg)
            al = _araujo_candidate(d)
            if al is not None:
                n_al, e_al = al
                bases.append(_fill_slack(n_al, e_al, d, seed))
        if D >= 4 and time.monotonic() < deadline:
            gq = _best_gq(d)
            if gq is not None:
                bases.append(gq)
    except Exception:
        pass

    for b in bases:
        try:
            consider(b[0], b[1])
        except Exception:
            pass

    # Bounded slack extension of baselines.
    try:
        ext_end = start + 0.15 * (deadline - start)
        for idx, (n0, e0) in enumerate(bases):
            now = time.monotonic()
            if now >= ext_end:
                break
            slice_end = now + (ext_end - now) / (len(bases) - idx)
            n1, e1 = _extend(n0, e0, d, D, seed + idx, slice_end)
            consider(n1, e1)
    except Exception:
        pass

    # Main bold search: annealed bi-Cayley lifts over semidirect products.
    while time.monotonic() < deadline:
        try:
            k = rng.choice([1, 1, 1, 2, 2, 3])
            base = best_n // (2 * k)
            G = max(4, base + 1 + rng.randrange(0, max(2, base // 20 + 1)))
            res = _trial(d, D, k, G, rng, 3000, deadline)
            if res is not None:
                consider(res[0], res[1])
        except Exception:
            break

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
