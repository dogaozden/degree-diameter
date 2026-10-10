import itertools
import math
import random
import time

import numpy as np

import lib

N_CAP = 6000                  # hard cap on vertex count of lifts
ITERS = 6000                  # annealing iterations per lift attempt
S_LIST = (1, 2, 3, 4, 5, 6)   # base vertices per side for voltage lifts
FAMILIES = (1, 2)             # 1: cyclic Z_m, 2: dihedral Z_m x| Z_2
GQ_Q_MAX = 9                  # largest q for which W(q) is built
RETRIES = 2                   # annealing restarts per lift size
TIME_FRAC = 0.8               # fraction of time_limit used before the final check
SAFETY = 1.0                  # seconds kept free at the end
EXTEND_SLICE = 0.7            # seconds per greedy-extension call
EXTEND_TRIES = 8              # randomized greedy restarts per extension call
BC_N_MAX = 1600               # largest group order for bi-Cayley graphs
BC_GROUPS_PER_ORDER = 3       # semidirect presentations tried per order
BC_PROBE_MAX = 6              # orders probed above the binary-search success


# ---------------------------------------------------------------- shared helpers

def _two_colour(n, edges):
    """Proper 2-colouring of a bipartite graph, component by component."""
    adj = lib.adjacency(n, edges)
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
    return color


def _extend(n, edges, d, D, rng, deadline):
    """Greedily add vertices whose neighbourhoods cover all old vertices within radius D-1.

    A new vertex attached to a cover keeps the diameter <= D and bipartiteness.
    """
    edges = list(edges)
    if D < 2 or n == 0:
        return n, edges
    color = _two_colour(n, edges)
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1

    while time.monotonic() < deadline:
        full = (1 << n) - 1
        balls = lib._balls(n, edges, D - 1)
        grown = False
        order = [0, 1] if rng.random() < 0.5 else [1, 0]
        for c in order:
            cand = [u for u in range(n) if color[u] == 1 - c and deg[u] < d]
            rng.shuffle(cand)
            covered, chosen = 0, []
            while covered != full and len(chosen) < d and cand:
                best_u, best_gain = -1, 0
                for u in cand:
                    g = (balls[u] & ~covered).bit_count()
                    if g > best_gain:
                        best_u, best_gain = u, g
                if best_u < 0:
                    break
                chosen.append(best_u)
                covered |= balls[best_u]
                cand.remove(best_u)
            if covered == full and chosen:
                x = n
                n += 1
                color.append(c)
                deg.append(len(chosen))
                for u in chosen:
                    edges.append((u, x))
                    deg[u] += 1
                grown = True
                break
        if not grown:
            break
    return n, edges


def _extend_best(n, edges, d, D, rng, deadline, tries=EXTEND_TRIES):
    """Run _extend several times with fresh tie-breaking and keep the largest result."""
    best = (n, list(edges))
    for t in range(tries):
        now = time.monotonic()
        if now >= deadline:
            break
        per = now + (deadline - now) / (tries - t)
        cand = _extend(n, edges, d, D, rng, per)
        if cand[0] > best[0]:
            best = cand
    return best


def _augment(n, edges, d, seed):
    """Add edges between opposite colour classes using spare degree (keeps diameter and bipartiteness)."""
    rng = random.Random(seed + 7)
    color = _two_colour(n, edges)
    deg = [0] * n
    adj = [set() for _ in range(n)]
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
        adj[u].add(v)
        adj[v].add(u)
    side0 = [u for u in range(n) if color[u] == 0]
    side1 = [v for v in range(n) if color[v] == 1]
    new_edges = list(edges)
    for _ in range(3):
        us = [u for u in side0 if deg[u] < d]
        rng.shuffle(us)
        for u in us:
            if deg[u] >= d:
                continue
            cands = [v for v in side1 if deg[v] < d and v not in adj[u]]
            if not cands:
                continue
            v = rng.choice(cands)
            adj[u].add(v)
            adj[v].add(u)
            deg[u] += 1
            deg[v] += 1
            new_edges.append((u, v))
    return n, new_edges


def _finish(cands, d, D):
    """Return the largest candidate that passes lib.is_valid, else K_{d,d}."""
    for n, e in sorted(cands, key=lambda c: -c[0]):
        if lib.is_valid(n, e, d, D):
            return n, e
    return lib.haar_graph(d, range(d))


def _ok(g, d, D):
    try:
        return lib.is_valid(g[0], g[1], d, D)
    except Exception:
        return False


def _largest_pp_le(x):
    """Largest prime power <= x, or None."""
    q = x
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    return q if q >= 2 else None


# ---------------------------------------------------------------- D = 3 : projective plane

def _pg_base(d):
    """Incidence graph of PG(2,q), q the largest prime power <= d-1."""
    q = _largest_pp_le(d - 1)
    if q is None:
        return None
    return lib.projective_plane_incidence(q)


# ---------------------------------------------------------------- D >= 4 : generalized quadrangle

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q).

    Degree q + 1, diameter 4, order 2(q+1)(q^2+1).
    """
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
    """W(q) for the largest prime power q <= min(d-1, GQ_Q_MAX)."""
    q = _largest_pp_le(min(d - 1, GQ_Q_MAX))
    if q is None:
        return None
    return _gq_w(q)


# ---------------------------------------------------------------- Haar graphs (hill-climb)

def _search_haar(d, D, m, rng, deadline, iters):
    """Hill-climb a connection set S (|S| = d, containing 0) in Z_m so the Haar graph has diameter <= D."""
    others = list(range(1, m))
    if len(others) < d - 1:
        return None

    def cost(S):
        n, edges = lib.haar_graph(m, S)
        return lib.bad_pairs(n, edges, D)

    S = [0] + rng.sample(others, d - 1)
    c = cost(S)
    for _ in range(iters):
        if c == 0:
            return S
        if time.monotonic() >= deadline:
            break
        cand = [x for x in others if x not in S]
        if not cand:
            break
        i = rng.randrange(1, d)
        T = S[:]
        T[i] = rng.choice(cand)
        ct = cost(T)
        if ct <= c:
            S, c = T, ct
    return S if c == 0 else None


# ---------------------------------------------------------------- groups for lifts

def _group(m, fam):
    """Return (order, inverse table) for fam 1 (Z_m) or fam 2 (Z_m x| Z_2, coded 2a+b)."""
    if fam == 1:
        G = m
        X = np.arange(G, dtype=np.int64)
        return G, (-X) % m
    G = 2 * m
    X = np.arange(G, dtype=np.int64)
    a, b = X // 2, X % 2
    pw = np.where(b == 0, 1, m - 1)
    INV = ((-pw * a) % m) * 2 + b
    return G, INV


def _mul(fam, m, g, v):
    """Array g * v (right multiplication by scalar element v)."""
    if fam == 1:
        return (g + v) % m
    a, b = g // 2, g % 2
    c, d = v // 2, v % 2
    pw = np.where(b == 0, 1, m - 1)
    return ((a + pw * c) % m) * 2 + (b + d) % 2


# ---------------------------------------------------------------- lifts (annealing)

def _neighbors(P, Pinv, V, s, ctx):
    """Neighbour table of the group lift of a d-regular bipartite base on s+s vertices."""
    fam, m, G, INV = ctx
    d = P.shape[0]
    g = np.arange(G, dtype=np.int64)
    nbr = np.empty((2 * s * G, d), dtype=np.int64)
    for kk in range(d):
        for i in range(s):
            j = int(P[kk, i])
            v = int(V[kk, i])
            nbr[i * G:(i + 1) * G, kk] = s * G + j * G + _mul(fam, m, g, v)
        for j in range(s):
            i = int(Pinv[kk, j])
            v_inv = int(INV[int(V[kk, i])])
            nbr[(s + j) * G:(s + j + 1) * G, kk] = i * G + _mul(fam, m, g, v_inv)
    return nbr


def _cost(nbr, sources, D):
    """Number of (source, vertex) pairs NOT within distance D. Zero iff the lift is valid."""
    n = nbr.shape[0]
    S = len(sources)
    R = np.zeros((S, n), dtype=bool)
    R[np.arange(S), sources] = True
    for _ in range(D):
        M = R.copy()
        for k in range(nbr.shape[1]):
            M |= R[:, nbr[:, k]]
        if np.array_equal(M, R):
            break
        R = M
    return int(S * n - np.count_nonzero(R))


def _swap(P, Pinv, k, a, b):
    P[k, a], P[k, b] = P[k, b], P[k, a]
    Pinv[k, P[k, a]] = a
    Pinv[k, P[k, b]] = b


def _anneal(s, ctx, d, D, rng, deadline):
    """Simulated annealing over permutations and voltages. Returns (P, V) with zero cost, or None."""
    G = ctx[2]
    P = np.array([rng.sample(range(s), s) for _ in range(d)], dtype=np.int64)
    Pinv = np.zeros_like(P)
    for k in range(d):
        for i in range(s):
            Pinv[k, P[k, i]] = i
    V = np.array([[rng.randrange(G) for _ in range(s)] for _ in range(d)], dtype=np.int64)
    sources = [i * G for i in range(2 * s)]
    nbr = _neighbors(P, Pinv, V, s, ctx)
    cur = _cost(nbr, sources, D)
    for it in range(ITERS):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = 2.0 * (1.0 - it / ITERS) + 0.05
        if s == 1 or rng.random() < 0.7:
            k, i = rng.randrange(d), rng.randrange(s)
            old = int(V[k, i])
            new_v = rng.randrange(G)
            if new_v == old:
                continue
            V[k, i] = new_v
            cand = _neighbors(P, Pinv, V, s, ctx)
            c = _cost(cand, sources, D)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur, nbr = c, cand
            else:
                V[k, i] = old
        else:
            k = rng.randrange(d)
            a, b = rng.sample(range(s), 2)
            _swap(P, Pinv, k, a, b)
            cand = _neighbors(P, Pinv, V, s, ctx)
            c = _cost(cand, sources, D)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur, nbr = c, cand
            else:
                _swap(P, Pinv, k, a, b)
    if cur == 0:
        return P.copy(), V.copy()
    return None


def _graph(s, ctx, P, V, d):
    """Materialise the lift as (n, edges), deduplicated."""
    G = ctx[2]
    Pinv = np.zeros_like(P)
    for k in range(d):
        for i in range(s):
            Pinv[k, P[k, i]] = i
    nbr = _neighbors(P, Pinv, V, s, ctx)
    edges = set()
    for x in range(s * G):
        for y in nbr[x].tolist():
            edges.add((x, y))
    return 2 * s * G, sorted(edges)


def _try_size(s, ctx, d, D, rng, deadline):
    for _ in range(RETRIES):
        if time.monotonic() > deadline:
            break
        st = _anneal(s, ctx, d, D, rng, deadline)
        if st is not None:
            return st
    return None


def _search(s, fam, d, D, rng, deadline, cap):
    """Find the largest m (doubling then bisection) whose lift anneals to zero cost.

    Returns (best, lo, hi): best is (ctx, P, V) or None.
    """
    best = None
    lo, hi = 0, None
    m = 2 if fam == 1 else 3
    while time.monotonic() < deadline:
        G = m if fam == 1 else 2 * m
        if 2 * s * G > cap:
            hi = m
        else:
            G, INV = _group(m, fam)
            ctx = (fam, m, G, INV)
            st = _try_size(s, ctx, d, D, rng, deadline)
            if st is not None:
                lo = m
                best = (ctx, st[0], st[1])
            else:
                hi = m
        if hi is None:
            m = 2 * lo
        else:
            if hi - lo <= 1:
                break
            m = (lo + hi) // 2
    return best, lo, hi


def _lift_phase(d, D, rng, end):
    """Annealed group lifts over base sizes s and families, sharing the time up to `end`."""
    cap = min(N_CAP, lib._moore_bound(d, D))
    out = []
    for idx, s in enumerate(S_LIST):
        now = time.monotonic()
        if now >= end:
            break
        slice_end = now + (end - now) / (len(S_LIST) - idx)
        for f_idx, fam in enumerate(FAMILIES):
            now = time.monotonic()
            if now >= slice_end:
                break
            fam_end = now + (slice_end - now) / (len(FAMILIES) - f_idx)
            best, lo, hi = _search(s, fam, d, D, rng, fam_end, cap)
            if best is not None:
                ctx, P, V = best
                out.append(_graph(s, ctx, P, V, d))
    return out


# ---------------------------------------------------------------- bi-Cayley graphs over semidirect groups
#
# G = Z_m x|_r Z_k, element (a, b) coded as a*k + b, product (a,b)(c,d) = (a + r^b c, b + d).
# Left x ~ right y iff x^{-1} y in S. Left multiplication is an automorphism transitive on
# each side, so diameter <= D iff the radius-D balls around (e, L) and (e, R) cover everything.

def _group_tables(m, k, r):
    """Return (N, tab, invs): tab[s, x] = x * s, invs[s] = s^{-1}, for G = Z_m x|_r Z_k."""
    N = m * k
    pw = [pow(r, b, m) for b in range(k)]
    pw_arr = np.array(pw, dtype=np.int64)
    X = np.arange(N, dtype=np.int64)
    A, B = X // k, X % k
    tab = np.empty((N, N), dtype=np.int32)
    invs = np.empty(N, dtype=np.int64)
    for s in range(N):
        c, dd = divmod(s, k)
        tab[s] = ((A + pw_arr[B] * c) % m) * k + (B + dd) % k
        nb = (-dd) % k
        na = (-pw[nb] * c) % m
        invs[s] = na * k + nb
    return N, tab, invs


def _groups_for_order(N, rng):
    """A few (m, k, r) semidirect presentations of groups of order N (cyclic always included)."""
    found = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        rs = [1 % m] if k == 1 else range(m)
        for r in rs:
            if math.gcd(r, m) != 1:
                continue
            if pow(r, k, m) != 1 % m:
                continue
            found.append((m, k, r))
    rng.shuffle(found)
    return found[:BC_GROUPS_PER_ORDER]


def _uncovered(tab, invs, S, N, D):
    """Number of (source, vertex) pairs not within distance D, sources (e, L) and (e, R)."""
    fwd = [tab[s] for s in S]
    bwd = [tab[invs[s]] for s in S]
    total = 0
    for src_side in (0, 1):
        visL = np.zeros(N, dtype=bool)
        visR = np.zeros(N, dtype=bool)
        if src_side == 0:
            visL[0] = True
            fL = np.array([0], dtype=np.int64)
            fR = np.empty(0, dtype=np.int64)
        else:
            visR[0] = True
            fR = np.array([0], dtype=np.int64)
            fL = np.empty(0, dtype=np.int64)
        for _ in range(D):
            nR = np.zeros(N, dtype=bool)
            for row in fwd:
                nR[row[fL]] = True
            nL = np.zeros(N, dtype=bool)
            for row in bwd:
                nL[row[fR]] = True
            nR &= ~visR
            nL &= ~visL
            visR |= nR
            visL |= nL
            fL = np.flatnonzero(nL)
            fR = np.flatnonzero(nR)
            if fL.size == 0 and fR.size == 0:
                break
        total += 2 * N - int(visL.sum()) - int(visR.sum())
    return total


def _anneal_bc(N, tab, invs, d, D, rng, budget_end):
    """Search a connection set S of size d with zero uncovered pairs. Returns S or None."""
    if d > N:
        return None
    S = rng.sample(range(N), d)
    cur = _uncovered(tab, invs, S, N, D)
    start = time.monotonic()
    span = max(1e-3, budget_end - start)
    while cur > 0:
        now = time.monotonic()
        if now >= budget_end:
            break
        frac = (now - start) / span
        temp = 1.0 * (1.0 - frac) + 0.05
        i = rng.randrange(d)
        t = rng.randrange(N)
        if t in S:
            continue
        T = S[:]
        T[i] = t
        c = _uncovered(tab, invs, T, N, D)
        if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
            S, cur = T, c
    return S if cur == 0 else None


def _bc_graph(N, tab, S):
    """Left x (0..N-1) joined to right N + x*s for s in S."""
    edges = []
    for s in S:
        row = tab[s].tolist()
        for x in range(N):
            edges.append((x, N + row[x]))
    return 2 * N, edges


def _try_order(N, groups, d, D, rng, end):
    """Try to realise a valid bi-Cayley graph of order N, splitting time across presentations."""
    for idx, (m, k, r) in enumerate(groups):
        now = time.monotonic()
        if now >= end:
            break
        per_end = now + (end - now) / (len(groups) - idx)
        _, tab, invs = _group_tables(m, k, r)
        S = _anneal_bc(N, tab, invs, d, D, rng, per_end)
        if S is not None:
            return _bc_graph(N, tab, S)
    return None


def _bicayley_best(d, D, seed, deadline):
    """Binary search over group orders, then probe a few larger orders.

    Existence is not monotone in N, so the next few larger orders are probed after success.
    Groups for each order are computed lazily, which keeps the setup cheap.
    """
    moore = lib._moore_bound(d, D)
    N_hi = min(N_CAP // 2, moore // 2, BC_N_MAX)
    N_lo = max(d, N_hi // 3)
    if N_hi < N_lo or N_hi < d:
        return None
    rng = random.Random(seed * 1000003 + 17 * d + D)
    orders = list(range(N_lo, N_hi + 1))
    cache = {}

    def groups_of(N):
        if N not in cache:
            cache[N] = _groups_for_order(N, rng)
        return cache[N]

    best, best_idx = None, -1
    lo, hi = 0, len(orders) - 1
    while lo <= hi and time.monotonic() < deadline - 0.2:
        mid = (lo + hi) // 2
        N = orders[mid]
        now = time.monotonic()
        budget_end = min(deadline, now + max(0.5, 0.25 * (deadline - now)))
        g = _try_order(N, groups_of(N), d, D, rng, budget_end)
        if g is not None:
            if best is None or g[0] > best[0]:
                best, best_idx = g, mid
            lo = mid + 1
        else:
            hi = mid - 1

    if best is not None:
        idx = best_idx + 1
        probes = 0
        while (idx < len(orders) and probes < BC_PROBE_MAX
               and time.monotonic() < deadline - 0.2):
            N = orders[idx]
            now = time.monotonic()
            budget_end = min(deadline, now + max(0.3, 0.15 * (deadline - now)))
            g = _try_order(N, groups_of(N), d, D, rng, budget_end)
            if g is not None and g[0] > best[0]:
                best = g
            idx += 1
            probes += 1
    return best


# ---------------------------------------------------------------- driver

def _solve(d, D, seed, start, time_limit):
    deadline = start + max(0.5, TIME_FRAC * time_limit - SAFETY)
    rng = random.Random(seed)
    cands = [lib.haar_graph(d, range(d))]   # K_{d,d}: diameter 2, always valid

    # D = 3: projective plane, extended into spare degree.
    if D == 3 and d >= 3:
        base = _pg_base(d)
        if base is not None:
            if lib.is_prime_power(d - 1):   # Moore-extremal, nothing to improve
                return _finish(cands + [base], d, D)
            cands.append(base)
            aug = _augment(base[0], base[1], d, seed)
            for g in (base, aug):
                cands.append(_extend_best(g[0], g[1], d, D, rng,
                                          min(deadline, time.monotonic() + EXTEND_SLICE)))

    # D >= 4: generalized quadrangle W(q), extended into spare degree.
    if D >= 4 and d >= 3:
        gq = _best_gq(d)
        if gq is not None:
            if D == 4 and d - 1 <= GQ_Q_MAX and lib.is_prime_power(d - 1):
                return _finish(cands + [gq], d, D)   # Moore-extremal for D = 4
            cands.append(gq)
            aug = _augment(gq[0], gq[1], d, seed)
            for g in (gq, aug):
                cands.append(_extend_best(g[0], g[1], d, D, rng,
                                          min(deadline, time.monotonic() + EXTEND_SLICE)))

    # Haar graphs with growing modulus (small slice).
    now = time.monotonic()
    haar_end = now + 0.1 * max(0.0, deadline - now)
    haar_m, haar_miss = d + 1, 0
    while time.monotonic() < haar_end and haar_miss < 4:
        S = _search_haar(d, D, haar_m, rng, haar_end, 120)
        if S is not None:
            cands.append(lib.haar_graph(haar_m, S))
            haar_miss = 0
        else:
            haar_miss += 1
        haar_m += 1

    # Voltage lifts (cyclic and dihedral) by annealing.
    two_phase = D >= 4 and d >= 3
    now = time.monotonic()
    remain = max(0.0, deadline - now)
    lift_end = now + (0.4 if two_phase else 1.0) * remain
    cands.extend(_lift_phase(d, D, rng, lift_end))

    # Bi-Cayley graphs over semidirect groups for D >= 4.
    if two_phase:
        bc = _bicayley_best(d, D, seed, deadline)
        if bc is not None:
            cands.append(bc)

    return _finish(cands, d, D)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D                       # even cycle: bipartite, diameter D, Moore-extremal
        return n, [(i, (i + 1) % n) for i in range(n)]
    if D == 2:
        return lib.haar_graph(d, range(d))   # K_{d,d} is extremal for D = 2

    fallback = lib.haar_graph(d, range(d))
    try:
        best = _solve(d, D, seed, start, time_limit)
    except Exception:
        best = None
    if best is not None and _ok(best, d, D):
        return best
    if _ok(fallback, d, D):
        return fallback
    return 2, [(0, 1)]
