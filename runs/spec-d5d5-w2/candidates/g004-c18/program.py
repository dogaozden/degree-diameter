import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Multiplier-invariant bi-Cayley lifts over Z_m.
#
# Vertices A_x and B_y (x, y in Z_m) with A_x ~ B_{x+s} for s in S. Taking
# S = {0} union (orbits of a unit u under multiplication) makes the map
# A_x -> A_{ux}, B_y -> B_{uy} an automorphism, so the search space shrinks to
# unions of orbits. Translation-invariance means checking BFS from A_0 and B_0
# suffices for the whole graph.
# ----------------------------------------------------------------------------

ITERS = 500  # plateau-walk steps per attempt before restarting with a new unit


def _orbits(m, u):
    """Orbits of the nonzero residues under x -> u*x (mod m), as lists."""
    seen = [False] * m
    seen[0] = True
    orbs = []
    for x in range(1, m):
        if seen[x]:
            continue
        orb = []
        y = x
        while not seen[y]:
            seen[y] = True
            orb.append(y)
            y = (y * u) % m
        orbs.append(orb)
    return orbs


def _elems(orbs, chosen):
    return [x for j in chosen for x in orbs[j]]


def _random_fill(orbs, need, rng):
    """Pick orbit indices whose sizes sum exactly to `need`; None if no luck."""
    for _ in range(100):
        order = list(range(len(orbs)))
        rng.shuffle(order)
        chosen = []
        total = 0
        for j in order:
            if total + len(orbs[j]) <= need:
                chosen.append(j)
                total += len(orbs[j])
                if total == need:
                    return chosen
    return None


def _cost(m, S, D):
    """Vertex pairs (source, target) not within distance D, from A_0 and B_0. Zero means valid."""
    N2 = 2 * m
    total = 0
    for src in (0, m):
        seen = bytearray(N2)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < m:
                    for s in S:
                        v = m + (u + s) % m
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    y = u - m
                    for s in S:
                        v = (y - s) % m
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            cnt += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N2 - cnt
    return total


def _search_m(m, d, D, rng, deadline):
    """Search a connection set S (|S| = d, 0 in S) for order m. Returns S or None."""
    units = [u for u in range(1, m) if math.gcd(u, m) == 1]
    need = d - 1
    while time.monotonic() < deadline:
        u = 1 if rng.random() < 0.25 else rng.choice(units)
        orbs = _orbits(m, u)
        by_size = {}
        for j, o in enumerate(orbs):
            by_size.setdefault(len(o), []).append(j)
        chosen = _random_fill(orbs, need, rng)
        if chosen is None:
            continue
        cur = _cost(m, [0] + _elems(orbs, chosen), D)
        for _ in range(ITERS):
            if cur == 0 or time.monotonic() >= deadline:
                break
            i = rng.randrange(len(chosen))
            sz = len(orbs[chosen[i]])
            cs = [j for j in by_size[sz] if j not in chosen]
            if not cs:
                continue
            new = chosen[:]
            new[i] = rng.choice(cs)
            c2 = _cost(m, [0] + _elems(orbs, new), D)
            if c2 <= cur:  # sideways moves allowed
                chosen, cur = new, c2
        if cur == 0:
            return [0] + _elems(orbs, chosen)
    return None


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D  # even cycle C_{2D} has diameter D and is bipartite
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib._moore_bound(d, D)

    # Projective plane meets the Moore bound when d-1 is a prime power (D = 3).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n, e, d, D):
            return n, e

    rng = random.Random(seed)
    hi = moore // 2
    lo = best[0] // 2 + 1
    m = lo
    slice_len = max(0.3, 0.06 * budget)

    while time.monotonic() < deadline:
        if lo > hi:
            break
        if m > hi:
            m = lo
        slice_end = min(deadline, time.monotonic() + slice_len)
        S = _search_m(m, d, D, rng, slice_end)
        if S is not None:
            n = 2 * m
            e = [(x, m + (x + s) % m) for x in range(m) for s in S]
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
                lo = m + 1
                m = lo
                continue
        m += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
