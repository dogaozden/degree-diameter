import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Algebraic baselines (exact or near-exact for D = 3).
# ----------------------------------------------------------------------------

def _pg_incidence(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1 (q <= 40)."""
    for q in range(min(d - 1, 40), 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez graph for d = q + 2 with q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# New helper 1: regular bipartite extension by matching removal.
#
# Given a d-regular bipartite graph with s vertices per side, pick d edges
# (a_i, b_i) with pairwise distinct endpoints. Remove them and add a new A
# vertex x joined to every b_i and a new B vertex y joined to every a_i.
# Every old vertex keeps its degree, the result is d-regular on s+1 per side,
# and it stays bipartite. The new vertices are at distance <= 3 from much of
# the graph, so the extension is a near-valid starting point for annealing.
# ----------------------------------------------------------------------------

def _extend(s, d, elist, rng):
    """Return (s+1, new_elist) by matching-removal extension, or None."""
    idx = list(range(len(elist)))
    rng.shuffle(idx)
    used_a, used_b, pick = set(), set(), []
    for k in idx:
        a, b = elist[k]
        if a in used_a or b in used_b:
            continue
        used_a.add(a)
        used_b.add(b)
        pick.append(k)
        if len(pick) == d:
            break
    if len(pick) < d:
        return None
    x = s  # new A local index
    y = s  # new B local index
    keep = set(pick)
    new = [e for k, e in enumerate(elist) if k not in keep]
    for k in pick:
        a, b = elist[k]
        new.append((a, y))
        new.append((x, b))
    return s + 1, new


# ----------------------------------------------------------------------------
# New helper 2: bitset defect map and switch annealing on bi-regular graphs.
#
# State: a d-regular bipartite graph on s + s vertices, stored as a list of
# edges (a, b) with a, b local indices. The cost is the number of
# (vertex, vertex) pairs not joined by a walk of length <= D (sum of
# defects, always even). A move is a double-edge switch
#   (a1,b1),(a2,b2) -> (a1,b2),(a2,b1),
# which keeps all degrees and bipartiteness. Moves are biased toward edges
# incident to a deficient vertex.
# ----------------------------------------------------------------------------

def _haar_start(s, d, rng):
    """Random d-regular bipartite start: Haar graph of Z_s with d distinct shifts."""
    shifts = rng.sample(range(s), d)
    return [(i, (i + t) % s) for i in range(s) for t in shifts]


def _graph_nb(s, elist):
    nb = [[] for _ in range(2 * s)]
    for a, b in elist:
        nb[a].append(s + b)
        nb[s + b].append(a)
    return nb


def _defects(N, nb, D):
    """Return (total defect, per-vertex defect) using bitset balls of radius D."""
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        nxt = [0] * N
        for v in range(N):
            x = reach[v]
            for u in nb[v]:
                x |= reach[u]
            nxt[v] = x
        reach = nxt
    defect = [N - r.bit_count() for r in reach]
    return sum(defect), defect


def _rep(lst, old, new):
    lst[lst.index(old)] = new


def _swap(i, j, a1, b1, a2, b2, s, elist, pos, nb):
    """Replace edges (a1,b1) at index i and (a2,b2) at index j by (a1,b2) and (a2,b1)."""
    del pos[(a1, b1)]
    del pos[(a2, b2)]
    elist[i] = (a1, b2)
    elist[j] = (a2, b1)
    pos[(a1, b2)] = i
    pos[(a2, b1)] = j
    _rep(nb[a1], s + b1, s + b2)
    _rep(nb[s + b1], a1, a2)
    _rep(nb[a2], s + b2, s + b1)
    _rep(nb[s + b2], a2, a1)


def _anneal(s, d, D, elist, rng, deadline):
    """Anneal switches until diameter <= D on the bipartite graph. Returns elist or None."""
    N = 2 * s
    elist = list(elist)
    pos = {e: i for i, e in enumerate(elist)}
    nb = _graph_nb(s, elist)
    cost, defect = _defects(N, nb, D)
    m = len(elist)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    T0, T1 = 2.5, 0.15
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            return None
        T = T0 * (T1 / T0) ** min(1.0, (now - t0) / span)
        if rng.random() < 0.6:
            bad = [v for v in range(N) if defect[v]]
            v = rng.choice(bad)
            u = rng.choice(nb[v])
            a, b = (v, u - s) if v < s else (u, v - s)
            i = pos[(a, b)]
        else:
            i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = elist[i]
        a2, b2 = elist[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in pos or (a2, b1) in pos:
            continue
        _swap(i, j, a1, b1, a2, b2, s, elist, pos, nb)
        nc, nd = _defects(N, nb, D)
        if nc <= cost or rng.random() < math.exp((cost - nc) / T):
            cost, defect = nc, nd
        else:
            _swap(i, j, a1, b2, a2, b1, s, elist, pos, nb)
    return elist


def _switch_search(d, D, rng, deadline, consider_s):
    """Grow a valid d-regular bipartite graph side by side, annealing after each extension."""
    s = max(d + 2, 6)
    elist = _anneal(s, d, D, _haar_start(s, d, rng), rng, deadline)
    if elist is None:
        return
    good_s, good_e = s, elist
    consider_s(good_s, good_e)
    step = max(1, s // 8)
    while time.monotonic() < deadline:
        cur_s, cur_e = good_s, good_e
        ok = True
        for _ in range(step):
            r = _extend(cur_s, d, cur_e, rng)
            if r is None:
                ok = False
                break
            cur_s, cur_e = r
        if not ok:
            step = max(1, step // 2)
            continue
        now = time.monotonic()
        slice_end = min(deadline, now + max(3.0, 0.3 * (deadline - now)))
        res = _anneal(cur_s, d, D, cur_e, rng, slice_end)
        if res is not None:
            good_s, good_e = cur_s, res
            consider_s(good_s, good_e)
            step = min(max(1, good_s // 6), step * 2)
        else:
            step = max(1, step // 2)


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D  # even cycle C_{2D} has diameter D
        return n, [(i, (i + 1) % n) for i in range(n)]

    best = {"n": 0, "edges": None}

    def consider(n, edges):
        if n > best["n"] and lib.is_valid(n, edges, d, D):
            best["n"] = n
            best["edges"] = edges

    # Safe fallback: K_{d,d} has diameter 2.
    kn, ke = lib.haar_graph(d, range(d))
    consider(kn, ke)

    if D >= 3:
        pg = _pg_incidence(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    # Search for graphs below the Moore bound.
    if best["n"] < lib.moore_bound(d, D):
        def consider_s(s, elist):
            consider(2 * s, [(a, s + b) for a, b in elist])

        _switch_search(d, D, rng, deadline, consider_s)

    n, e = best["n"], best["edges"]
    if n == 0 or e is None or not lib.is_valid(n, e, d, D):
        return kn, ke
    return n, e
