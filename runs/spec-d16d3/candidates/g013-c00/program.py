import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane incidence data.
# Points are 0..m-1 and lines are m..2m-1 in lib.projective_plane_incidence.
# ----------------------------------------------------------------------------

def _incidence(q):
    """Return (m, edges, pl, lp): pl[P] = lines through point P, lp[L] = points on line L (both 0-based)."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    pl = [[] for _ in range(m)]
    lp = [[] for _ in range(m)]
    for u, v in edges:
        pl[u].append(v - m)
        lp[v - m].append(u)
    return m, edges, pl, lp


# ----------------------------------------------------------------------------
# Twin-copy weighting (diameter-3 growth on PG(2, q)).
#
# A point P has q+1 lines. A "twin" of P is a new vertex joined to exactly the
# same lines, so it is at distance 2 from P and every other vertex keeps its
# distances. Likewise a "line twin" of L is joined to exactly the points of L.
# Twins of points sit on the point side, twins of lines on the line side, so the
# graph stays bipartite.
#
# Each point P gets c_P in {0..s} twins and each line L gets e_L in {0..s} twins,
# where s = d - q - 1 is the spare degree. The degree constraints decouple:
#   line L:  (q+1) + sum_{P on L} c_P <= d       (cap on c over lines)
#   point P: (q+1) + sum_{L through P} e_L <= d  (cap on e over points)
# so the two weightings are independent packings. The diameter stays <= 3 for
# every choice of weights. (Checked by lib.is_valid anyway.)
#
# This is a weighted packing, not an arc. An arc gives weight 0/1 and is at most
# q+1 points for odd q. Weights up to s can reach roughly s(q^2+q+1)/(q+1) per side.
# ----------------------------------------------------------------------------

def _pack(num_items, num_cons, item_cons, cap, rng, deadline):
    """Maximize sum of weights w_i in 0..cap with every constraint's load (sum of w_i over items using it) <= cap.

    Simulated annealing over unit removals followed by greedy refilling.
    Returns the best weight vector found.
    """
    cnt = [0] * num_items
    load = [0] * num_cons
    total = 0

    def can_add(i):
        if cnt[i] >= cap:
            return False
        for c in item_cons[i]:
            if load[c] >= cap:
                return False
        return True

    def fill():
        nonlocal total
        order = list(range(num_items))
        rng.shuffle(order)
        for i in order:
            while can_add(i):
                cnt[i] += 1
                total += 1
                for c in item_cons[i]:
                    load[c] += 1

    def remove(i):
        nonlocal total
        cnt[i] -= 1
        total -= 1
        for c in item_cons[i]:
            load[c] -= 1

    fill()
    best_total, best = total, cnt[:]
    T = 0.6
    while time.monotonic() < deadline:
        old_cnt, old_load, old_total = cnt[:], load[:], total
        nz = [i for i in range(num_items) if cnt[i] > 0]
        if nz:
            for _ in range(1 + (rng.random() < 0.3)):
                nz = [i for i in range(num_items) if cnt[i] > 0]
                if not nz:
                    break
                remove(rng.choice(nz))
        fill()
        if total < old_total and rng.random() >= math.exp((total - old_total) / T):
            cnt[:] = old_cnt
            load[:] = old_load
            total = old_total
        if total > best_total:
            best_total, best = total, cnt[:]
    return best


def _twin_graph(m, edges, pl, lp, cw, ew):
    """Base incidence graph plus cw[P] twins of each point P and ew[L] twins of each line L."""
    n = 2 * m
    E = list(edges)
    for P in range(m):
        for _ in range(cw[P]):
            v = n
            n += 1
            for L in pl[P]:
                E.append((v, m + L))
    for L in range(m):
        for _ in range(ew[L]):
            w = n
            n += 1
            for P in lp[L]:
                E.append((P, w))
    return n, E


# ----------------------------------------------------------------------------
# Main entry.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2, so it is a safe fallback for any D >= 2.
    fallback = lib.haar_graph(d, range(d))
    if D == 2 or d < 2:
        return fallback

    best, best_n = fallback, fallback[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best, best_n = (n, e), n

    # Candidate prime powers q with q + 1 <= d; take the three largest.
    qs = [q for q in range(min(d - 1, 40), 1, -1) if lib.is_prime_power(q)][:3]
    for idx, q in enumerate(qs):
        now = time.monotonic()
        if now >= deadline:
            break
        share = (deadline - now) / (len(qs) - idx)
        m, edges, pl, lp = _incidence(q)
        consider(2 * m, list(edges))  # plain PG(2, q) incidence
        s = d - q - 1
        if s >= 1:
            half = share / 2
            cw = _pack(m, m, pl, s, rng, time.monotonic() + half)
            ew = _pack(m, m, lp, s, rng, time.monotonic() + half)
            n, E = _twin_graph(m, edges, pl, lp, cw, ew)
            consider(n, E)

    if not lib.is_valid(best[0], best[1], d, D):
        return fallback
    return best
