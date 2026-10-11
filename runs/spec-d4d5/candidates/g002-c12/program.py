import math
import random
import time

import numpy as np

import lib

N_CAP = 6000
BC_N_MAX = 1600
BC_GROUPS_PER_ORDER = 3
BASE_FRAC = 0.5        # share of the budget for the bi-Cayley baseline (d >= 4, D >= 4)
GROW_FRAC = 0.25       # share of remaining growth time given to one insertion attempt
GROW_MIN_SLICE = 2.0   # seconds; minimum length of one insertion attempt
GROW_FAIL_MAX = 60     # consecutive failed insertion setups before growth stops
SAFETY = 1.0           # seconds kept back from the time limit


# ---------------------------------------------------------------- semidirect groups
# Group Z_m x|_r Z_k, element (a, b) coded as a*k + b, product (a,b)(c,d) = (a + r^b c, b + d).

def _presentations(M, rng, limit):
    """Random semidirect presentations (m, k, r) of groups of order M (k <= 8)."""
    out = []
    ks = [k for k in range(1, 9) if M % k == 0]
    rng.shuffle(ks)
    for k in ks:
        m = M // k
        if m == 1:
            out.append((1, k, 0))
        elif k == 1:
            out.append((m, 1, 1))
        else:
            cands = [m - 1] if k == 2 else []
            for _ in range(40):
                r = rng.randrange(1, m)
                if math.gcd(r, m) == 1 and pow(r, k, m) == 1:
                    cands.append(r)
            if cands:
                out.append((m, k, rng.choice(cands)))
        if len(out) >= limit:
            break
    return out


def _group_tables(m, k, r):
    """Return (N, tab, invs): tab[s, x] = x * s, invs[s] = s^{-1}."""
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


def _uncovered(tab, invs, S, N, D):
    """Number of (source, vertex) pairs at distance > D in the bi-Cayley graph, over both source sides."""
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
        temp = 1.0 * (1.0 - (now - start) / span) + 0.05
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
    """Bi-Cayley graph: left x joined to right N + x*s for s in S. Left side is 0..N-1."""
    edges = []
    for s in S:
        row = tab[s].tolist()
        for x in range(N):
            edges.append((x, N + row[x]))
    return 2 * N, edges


def _try_order(N, d, D, rng, end):
    pres = _presentations(N, rng, BC_GROUPS_PER_ORDER)
    for idx, (m, k, r) in enumerate(pres):
        now = time.monotonic()
        if now >= end:
            break
        per_end = now + (end - now) / (len(pres) - idx)
        _, tab, invs = _group_tables(m, k, r)
        S = _anneal_bc(N, tab, invs, d, D, rng, per_end)
        if S is not None:
            return _bc_graph(N, tab, S)
    return None


def _bicayley_best(d, D, seed, deadline):
    """Binary search over group orders for the largest order with a valid bi-Cayley graph."""
    moore = lib._moore_bound(d, D)
    N_hi = min(N_CAP // 2, moore // 2, BC_N_MAX)
    N_lo = max(d, N_hi // 3)
    if N_hi < N_lo or N_hi < d:
        return None
    rng = random.Random(seed * 1000003 + 17 * d + D)
    orders = list(range(N_lo, N_hi + 1))
    best = None
    lo, hi = 0, len(orders) - 1
    while lo <= hi and time.monotonic() < deadline - 0.2:
        mid = (lo + hi) // 2
        N = orders[mid]
        now = time.monotonic()
        budget_end = min(deadline, now + max(0.5, 0.25 * (deadline - now)))
        g = _try_order(N, d, D, rng, budget_end)
        if g is not None:
            if best is None or g[0] > best[0]:
                best = g
            lo = mid + 1
        else:
            hi = mid - 1
    return best


# ---------------------------------------------------------------- growth by edge-swap annealing
# State: adjl[v] = list of neighbours, E = list of (a, b) with a on the A side, b on the B side.
# Every vertex has degree d. Double edge swaps keep degrees and bipartiteness.

def _to_state(n, edges):
    adjl = [[] for _ in range(n)]
    E = []
    for a, b in edges:
        E.append((a, b))
        adjl[a].append(b)
        adjl[b].append(a)
    return adjl, E


def _bad_pairs(adjl, n, D):
    """Ordered (vertex, vertex) pairs not within distance D; zero iff the graph has diameter <= D."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adjl[v]:
                r |= reach[u]
            new.append(r)
        if new == reach:
            break
        reach = new
    return sum(n - r.bit_count() for r in reach)


def _rewire(adjl, E, i, j):
    """Replace (a1,b1),(a2,b2) by (a1,b2),(a2,b1). Applying it twice restores the original."""
    a1, b1 = E[i]
    a2, b2 = E[j]
    adjl[a1].remove(b1)
    adjl[b1].remove(a1)
    adjl[a2].remove(b2)
    adjl[b2].remove(a2)
    adjl[a1].append(b2)
    adjl[b2].append(a1)
    adjl[a2].append(b1)
    adjl[b1].append(a2)
    E[i] = (a1, b2)
    E[j] = (a2, b1)


def _anneal_graph(adjl, E, n, D, rng, end):
    """Anneal double edge swaps until the diameter is at most D. Returns True on success."""
    cur = _bad_pairs(adjl, n, D)
    start = time.monotonic()
    span = max(1e-3, end - start)
    m = len(E)
    while cur > 0:
        now = time.monotonic()
        if now >= end:
            break
        temp = 1.0 * (1.0 - (now - start) / span) + 0.05
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2 or b2 in adjl[a1] or b1 in adjl[a2]:
            continue
        _rewire(adjl, E, i, j)
        c = _bad_pairs(adjl, n, D)
        if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
            cur = c
        else:
            _rewire(adjl, E, i, j)
    return cur == 0


def _grow_state(adjl, E, n, d, rng):
    """Add one A vertex and one B vertex of degree d by splitting d random edges.

    Returns (adj2, E2, n + 2) or None if no simple completion was found.
    """
    m = len(E)
    if m < d:
        return None
    rem = rng.sample(range(m), d)
    gone = set(rem)
    adj2 = [list(x) for x in adjl]
    adj2.append([])
    adj2.append([])
    As = [n] * d
    Bs = [n + 1] * d
    for idx in rem:
        a, b = E[idx]
        adj2[a].remove(b)
        adj2[b].remove(a)
        As.append(a)
        Bs.append(b)
    E2 = [e for k, e in enumerate(E) if k not in gone]
    ok = False
    for _ in range(300):
        rng.shuffle(Bs)
        if len(set(zip(As, Bs))) == len(As) and all(b not in adj2[a] for a, b in zip(As, Bs)):
            ok = True
            break
    if not ok:
        return None
    for a, b in zip(As, Bs):
        adj2[a].append(b)
        adj2[b].append(a)
        E2.append((a, b))
    return adj2, E2, n + 2


def _grow(adjl, E, n, d, D, rng, end, best):
    """Repeatedly insert a vertex pair and anneal back to diameter D. Keeps the last valid graph."""
    fails = 0
    while fails < GROW_FAIL_MAX:
        now = time.monotonic()
        remaining = end - now
        if remaining < 0.3:
            break
        slice_end = now + min(remaining, max(GROW_MIN_SLICE, GROW_FRAC * remaining))
        g = _grow_state(adjl, E, n, d, rng)
        if g is None:
            fails += 1
            continue
        a2, e2, n2 = g
        if _anneal_graph(a2, e2, n2, D, rng, slice_end) and lib.is_valid(n2, e2, d, D):
            adjl, E, n = a2, e2, n2
            best = (n, list(E))
            fails = 0
        else:
            fails += 1
    return best


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()

    # Trivial cases.
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D                                  # even cycle: bipartite, diameter D
        return L, [(i, (i + 1) % L) for i in range(L)]
    if D == 2:
        return lib.haar_graph(d, range(d))         # K_{d,d} is extremal for D = 2

    budget = max(0.5, 0.85 * time_limit - SAFETY)
    deadline = start + budget
    rng = random.Random(seed)

    # Moore-extremal shortcut for D = 3 when d - 1 is a prime power.
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n, e, d, D):
            return n, e

    # Safe fallback, always valid.
    best = lib.haar_graph(d, range(d))

    # Baseline: bi-Cayley graphs over semidirect groups (D >= 4, d >= 4).
    if d >= 4 and D >= 4:
        now = time.monotonic()
        try:
            g = _bicayley_best(d, D, seed, now + BASE_FRAC * max(0.0, deadline - now))
        except Exception:
            g = None
        if g is not None and g[0] > best[0] and lib.is_valid(g[0], g[1], d, D):
            best = g

    # Bold stage: grow the best regular graph by vertex insertion plus edge-swap annealing.
    try:
        adjl, E = _to_state(best[0], best[1])
        best = _grow(adjl, E, best[0], d, D, rng, deadline, best)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        return lib.haar_graph(d, range(d))
    return best
