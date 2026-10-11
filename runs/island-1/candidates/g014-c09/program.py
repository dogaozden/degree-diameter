import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe baseline families (unchanged from the parent).
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
# New construction: bi-Cayley graphs over finite groups.
#
# Vertices A_x = x and B_y = G + y for x, y in the group G. Pick a set S of d
# distinct group elements and join A_x to B_{x*s} for every s in S. This is
# d-regular and bipartite. Left multiplication by g is an automorphism
# (A_x -> A_{gx}, B_y -> B_{gy}), which is transitive on each side. So the
# diameter is at most D iff BFS from A_e and from B_e reaches everything
# within D steps. The search is annealing over S, with the group order
# sampled in a window that ratchets upward on each success.
# ----------------------------------------------------------------------------

def _sample_group(lo, hi, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k of a random order G in [lo, hi], or None."""
    for _ in range(40):
        G = rng.randrange(lo, hi + 1)
        divs = [k for k in range(1, 17) if G % k == 0 and G // k >= 2]
        if not divs:
            continue
        k = rng.choice(divs)
        m = G // k
        cands = [1]  # r = 1 gives the abelian group Z_m x Z_k
        if k > 1:
            cands += [r for r in rng.sample(range(2, m), min(m - 2, 120))
                      if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k, r)
        except ValueError:
            continue
        return order, mul
    return None


def _perm_pair(mul, G, s):
    """Right multiplication by s as a permutation list, and its inverse permutation."""
    p = [mul(x, s) for x in range(G)]
    iv = [0] * G
    for x, y in enumerate(p):
        iv[y] = x
    return p, iv


def _bc_eval(G, D, perms, invs):
    """Sum over the sources A_e and B_e of vertices not reached within distance D. Zero means valid."""
    N = 2 * G
    total = 0
    for src in (0, G):
        seen = bytearray(N)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < G:
                    for p in perms:
                        v = G + p[u]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    y = u - G
                    for iv in invs:
                        v = iv[y]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += N - count
    return total


def _bc_edges(G, perms):
    return [(x, G + p[x]) for p in perms for x in range(G)]


def _bc_anneal(G, mul, d, D, rng, iters, deadline):
    """Anneal the connection set S for a fixed group. Returns (G, perms) on success, else None."""
    if G < d:
        return None
    S = rng.sample(range(G), d)
    pairs = [_perm_pair(mul, G, s) for s in S]
    perms = [a for a, _ in pairs]
    invs = [b for _, b in pairs]
    inS = set(S)
    cost = _bc_eval(G, D, perms, invs)
    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = 1.5 * (1.0 - t / iters) + 0.05
        i = rng.randrange(d)
        new = rng.randrange(G)
        if new in inS:
            continue
        np_, niv = _perm_pair(mul, G, new)
        op, oiv = perms[i], invs[i]
        perms[i], invs[i] = np_, niv
        c2 = _bc_eval(G, D, perms, invs)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            inS.discard(S[i])
            inS.add(new)
            S[i] = new
            cost = c2
        else:
            perms[i], invs[i] = op, oiv
    if cost == 0:
        return G, perms
    return None


def _bc_phase(d, D, n0, rng, deadline):
    """Repeatedly search bi-Cayley graphs with order above n0, ratcheting the window upward on success."""
    best = None
    G_lo = max(d, n0 // 2 + 1)
    while time.monotonic() < deadline:
        G_hi = int(G_lo * 1.2) + 2
        g = _sample_group(G_lo, G_hi, rng)
        if g is None:
            continue
        G, mul = g
        res = _bc_anneal(G, mul, d, D, rng, 400, deadline)
        if res is None:
            continue
        Gg, perms = res
        n = 2 * Gg
        e = _bc_edges(Gg, perms)
        if lib.is_valid(n, e, d, D):
            best = (n, e)
            G_lo = Gg + 1
    return best


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, min(0.8 * time_limit, time_limit - 4.0))

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    if d == 1:
        return 2, [(0, 1)]

    # Safe fallback. For d = 2 use the cycle C_{2D} (diameter D); otherwise K_{d,d} (diameter 2).
    if d == 2:
        best = (2 * D, [(i, (i + 1) % (2 * D)) for i in range(2 * D)])
    else:
        best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    moore = lib._moore_bound(d, D)

    # Algebraic base constructions.
    bases = []
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

    for b in bases:
        consider(b[0], b[1])

    # Bounded share of the budget for extending each base.
    ext_frac = 0.3 if D == 3 else 0.1
    ext_end = start + ext_frac * (deadline - start)
    for idx, (n0, e0) in enumerate(bases):
        if best_n >= moore:
            break
        now = time.monotonic()
        if now >= ext_end:
            break
        slice_end = now + (ext_end - now) / (len(bases) - idx)
        n1, e1 = _extend(n0, e0, d, D, seed + idx, slice_end)
        consider(n1, e1)

    # New family: bi-Cayley graphs over semidirect products, using the rest of the budget.
    if D >= 3 and best_n < moore and time.monotonic() < deadline:
        rng = random.Random(seed * 7919 + D * 131 + d)
        res = _bc_phase(d, D, best_n, rng, deadline)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
