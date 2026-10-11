import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe base constructions.
# ----------------------------------------------------------------------------

def _k_dd(d):
    """K_{d,d}: diameter 2, degree d."""
    return 2 * d, [(i, d + j) for i in range(d) for j in range(d)]


def _cycle(D):
    """Even cycle C_{2D}: degree 2, bipartite, diameter D."""
    n = 2 * D
    return n, [(i, (i + 1) % n) for i in range(n)]


def _largest_pp_at_most(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def _pg_adj(q):
    """Point/line adjacency of PG(2, q). pl[point] = lines through it, lp[line] = points on it."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    pl = [[] for _ in range(m)]
    lp = [[] for _ in range(m)]
    for u, v in edges:
        pl[u].append(v - m)
        lp[v - m].append(u)
    return m, pl, lp


def _conic(q):
    """Conic (plus nucleus for even q) as a set of vector indices; no three collinear."""
    F = lib.GF(q)
    pts = lib.projective_points(q)
    index = {p: i for i, p in enumerate(pts)}
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


# ----------------------------------------------------------------------------
# Bipartite state: ax[x] = set of Y-local neighbours of X-vertex x,
# ay[y] = set of X-local neighbours of Y-vertex y. Both sides have H vertices.
# Global ids: X vertex x -> x, Y vertex y -> H + y.
# ----------------------------------------------------------------------------

def _arc_state(m, pl, lp, S):
    """PG(2,q) incidence plus, for each t, an X-vertex m+t (joined to the lines through S[t])
    and a Y-vertex m+t (joined to the points on line S[t]). With S empty this is plain PG."""
    k = len(S)
    ax = [set() for _ in range(m + k)]
    ay = [set() for _ in range(m + k)]
    for x in range(m):
        for y in pl[x]:
            ax[x].add(y)
            ay[y].add(x)
    for t, P in enumerate(S):
        x = m + t
        for y in pl[P]:
            ax[x].add(y)
            ay[y].add(x)
    for t, L in enumerate(S):
        y = m + t
        for x in lp[L]:
            ax[x].add(y)
            ay[y].add(x)
    return ax, ay


def _edges_of(ax):
    H = len(ax)
    return 2 * H, [(x, H + y) for x in range(H) for y in ax[x]]


def _saturate(ax, ay, d, rng):
    """Greedily join deficient X and Y vertices (random order)."""
    H = len(ax)
    dx = [x for x in range(H) if len(ax[x]) < d]
    dy = [y for y in range(H) if len(ay[y]) < d]
    rng.shuffle(dx)
    rng.shuffle(dy)
    for x in dx:
        for y in dy:
            if len(ax[x]) >= d:
                break
            if len(ay[y]) < d and y not in ax[x]:
                ax[x].add(y)
                ay[y].add(x)


def _bad_count(ax, ay):
    """Number of unordered vertex pairs at distance > 3 (bitmask balls)."""
    H = len(ax)
    n = 2 * H
    adj = [None] * n
    for x in range(H):
        adj[x] = [H + y for y in ax[x]]
    for y in range(H):
        adj[H + y] = list(ay[y])
    b1 = [0] * n
    for v in range(n):
        acc = 1 << v
        for u in adj[v]:
            acc |= 1 << u
        b1[v] = acc
    b2 = [0] * n
    for v in range(n):
        acc = b1[v]
        for u in adj[v]:
            acc |= b1[u]
        b2[v] = acc
    bad = 0
    for v in range(n):
        acc = b2[v]
        for u in adj[v]:
            acc |= b2[u]
        bad += n - acc.bit_count()
    return bad // 2


def _anneal(ax, ay, d, deadline, rng):
    """Simulated annealing on a fixed-size bipartite graph with max degree d, diameter-3 cost.

    Moves: degree-preserving double-edge switches, and adding an edge between
    two deficient vertices (never increases cost). Returns the solved state
    (cost 0) or None.
    """
    H = len(ax)
    cost = _bad_count(ax, ay)
    t_start = time.monotonic()
    span = max(deadline - t_start, 1e-3)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        T = 1.0 * (0.08 ** ((now - t_start) / span))
        if rng.random() < 0.25:
            dx = [x for x in range(H) if len(ax[x]) < d]
            dy = [y for y in range(H) if len(ay[y]) < d]
            if dx and dy:
                x = rng.choice(dx)
                y = rng.choice(dy)
                if y not in ax[x]:
                    ax[x].add(y)
                    ay[y].add(x)
                    cost = _bad_count(ax, ay)
                continue
        x1 = rng.randrange(H)
        if not ax[x1]:
            continue
        y1 = rng.choice(tuple(ax[x1]))
        x2 = rng.randrange(H)
        if x2 == x1 or not ax[x2]:
            continue
        y2 = rng.choice(tuple(ax[x2]))
        if y2 in ax[x1] or y1 in ax[x2]:
            continue
        # apply switch: (x1,y1),(x2,y2) -> (x1,y2),(x2,y1)
        ax[x1].remove(y1)
        ay[y1].remove(x1)
        ax[x2].remove(y2)
        ay[y2].remove(x2)
        ax[x1].add(y2)
        ay[y2].add(x1)
        ax[x2].add(y1)
        ay[y1].add(x2)
        new = _bad_count(ax, ay)
        delta = new - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = new
        else:
            # undo
            ax[x1].remove(y2)
            ay[y2].remove(x1)
            ax[x2].remove(y1)
            ay[y1].remove(x2)
            ax[x1].add(y1)
            ay[y1].add(x1)
            ax[x2].add(y2)
            ay[y2].add(x2)
    return (ax, ay) if cost == 0 else None


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline = t0 + max(1.0, min(0.8 * time_limit, time_limit - 8.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        return _cycle(D)
    if D == 2:
        return _k_dd(d)

    # D >= 3, d >= 3: projective-plane base, possibly with conic arc extension.
    best = _k_dd(d)
    q = _largest_pp_at_most(d - 1)
    m, pl, lp = _pg_adj(q)
    s = d - q - 1
    cands = []
    if s >= 2:
        try:
            cands.append(_conic(q))
        except Exception:
            pass
    cands.append([])

    base = None
    for S in cands:
        ax, ay = _arc_state(m, pl, lp, S)
        n0, E0 = _edges_of(ax)
        if lib.is_valid(n0, E0, d, D):
            base = (ax, ay, n0, E0)
            break
    if base is None:
        return best

    ax, ay, n0, E0 = base
    best = (n0, E0)

    # Bold step (D == 3 only): grow by one vertex per side and anneal toward diameter 3.
    if D == 3:
        bound = 2 * sum((d - 1) ** i for i in range(D))
        while 2 * (len(ax) + 1) <= bound and time.monotonic() < deadline:
            nax = [set(x) for x in ax] + [set()]
            nay = [set(y) for y in ay] + [set()]
            _saturate(nax, nay, d, rng)
            res = _anneal(nax, nay, d, deadline, rng)
            if res is None:
                break
            ax, ay = res
            n1, E1 = _edges_of(ax)
            if not lib.is_valid(n1, E1, d, D):
                break
            best = (n1, E1)

    if not lib.is_valid(best[0], best[1], d, D):
        return _k_dd(d)
    return best
