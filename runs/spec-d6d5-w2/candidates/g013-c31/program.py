import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bipartite random-regular graphs with exact diameter repair by 2-switch
# annealing, grown by vertex splicing. Left vertices are 0..L-1, right vertices
# are L..2L-1. nl[a] lists right-local neighbours of left a, nr[b] lists left
# neighbours of right b. Every vertex keeps degree d throughout.
# ----------------------------------------------------------------------------

def _prime_power_below(d):
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def _cost(nl, nr, D):
    """Ordered count of (vertex, vertex) pairs not within distance D (bitmask BFS). Zero means valid."""
    L = len(nl)
    N = 2 * L
    adj = [None] * N
    for a in range(L):
        adj[a] = [L + b for b in nl[a]]
    for b in range(L):
        adj[L + b] = nr[b]
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        new = []
        for v in range(N):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        if new == reach:
            break
        reach = new
    return sum(N - r.bit_count() for r in reach)


def _random_bip(L, d, rng):
    """d-regular bipartite graph on L+L vertices as the union of d random perfect matchings."""
    nl = [[] for _ in range(L)]
    E = set()
    for _ in range(d):
        perm = None
        for _t in range(3000):
            cand = list(range(L))
            rng.shuffle(cand)
            if all((a, cand[a]) not in E for a in range(L)):
                perm = cand
                break
        if perm is None:
            return None
        for a in range(L):
            E.add((a, perm[a]))
            nl[a].append(perm[a])
    nr = [[] for _ in range(L)]
    for a in range(L):
        for b in nl[a]:
            nr[b].append(a)
    return nl, nr


def _splice(nl, nr, d, rng):
    """Add one left vertex x and one right vertex y, each of degree d, by splicing d edges."""
    L = len(nl)
    if L < d:
        return False
    As = bs = None
    for _ in range(200):
        As = rng.sample(range(L), d)
        bs = [nl[a][rng.randrange(d)] for a in As]
        if len(set(bs)) == d:
            break
    else:
        return False
    x = L
    y = L
    nl.append([])
    nr.append([])
    for a, b in zip(As, bs):
        i = nl[a].index(b)
        nl[a][i] = y
        j = nr[b].index(a)
        nr[b][j] = x
        nl[x].append(b)
        nr[y].append(a)
    return True


def _anneal(nl, nr, D, d, deadline, rng):
    """2-switch annealing on the bad-pair count. Returns True when the graph has diameter <= D."""
    L = len(nl)
    cost = _cost(nl, nr, D)
    start = time.monotonic()
    span = max(1e-3, deadline - start)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        T = 0.5 + 8.0 * max(0.0, 1.0 - (now - start) / span)
        a1 = rng.randrange(L)
        i1 = rng.randrange(d)
        b1 = nl[a1][i1]
        a2 = rng.randrange(L)
        i2 = rng.randrange(d)
        b2 = nl[a2][i2]
        if a1 == a2 or b1 == b2 or b2 in nl[a1] or b1 in nl[a2]:
            continue
        nl[a1][i1] = b2
        nl[a2][i2] = b1
        j1 = nr[b1].index(a1)
        j2 = nr[b2].index(a2)
        nr[b1][j1] = a2
        nr[b2][j2] = a1
        new = _cost(nl, nr, D)
        if new <= cost or rng.random() < math.exp(-(new - cost) / T):
            cost = new
        else:
            nl[a1][i1] = b1
            nl[a2][i2] = b2
            nr[b1][j1] = a1
            nr[b2][j2] = a2
    return cost == 0


def _edges(nl):
    L = len(nl)
    return [(a, L + b) for a in range(L) for b in nl[a]]


def _grow(d, D, moore, deadline, rng):
    """Find a random valid start, then repeatedly splice in vertex pairs and repair. Returns (n, edges) or None."""
    nl = nr = None
    L = min(8 * d, moore // 2)
    while L >= d and nl is None:
        if time.monotonic() >= deadline:
            return None
        g = _random_bip(L, d, rng)
        if g is not None and _anneal(g[0], g[1], D, d,
                                     min(deadline, time.monotonic() + 6.0), rng):
            nl, nr = g
        else:
            L -= max(1, L // 6)
    if nl is None:
        return None

    best = (2 * len(nl), _edges(nl))
    s = 1
    while time.monotonic() < deadline:
        room = moore // 2 - len(nl)
        if room < 1:
            break
        step = min(s, room)
        cnl = [list(x) for x in nl]
        cnr = [list(x) for x in nr]
        ok = all(_splice(cnl, cnr, d, rng) for _ in range(step))
        if ok and _anneal(cnl, cnr, D, d, min(deadline, time.monotonic() + 4.0), rng):
            nl, nr = cnl, cnr
            best = (2 * len(nl), _edges(nl))
            s = min(2 * step, 32)
        else:
            s = max(1, step // 2)
    return best


# ----------------------------------------------------------------------------
# Main build: safe fallback first, then algebraic candidates for D = 3,
# then the splice-and-anneal growth. Every candidate is checked with lib.is_valid.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for every D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    best_e = list(best_e)

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    if D == 2:
        return best_n, best_e

    moore = lib.moore_bound(d, D)

    if D == 3 and d >= 3:
        q = _prime_power_below(d)
        if q is not None:
            n, e = lib.projective_plane_incidence(q)
            consider(n, e)
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                n, e = lib.araujo_lopez_graph(d - 2)
                consider(n, e)
            except Exception:
                pass

    if d >= 3 and D >= 3:
        g = _grow(d, D, moore, deadline, rng)
        if g is not None:
            consider(g[0], g[1])

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
        best_e = list(best_e)
    return best_n, best_e
