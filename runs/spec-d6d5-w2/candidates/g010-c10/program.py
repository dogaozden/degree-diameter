import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Baselines: complete bipartite graphs, cycles, and projective-plane incidence.
# ----------------------------------------------------------------------------

def _complete_bipartite(d):
    """K_{d,d}: d-regular, bipartite, diameter 2."""
    return 2 * d, [(i, d + j) for i in range(d) for j in range(d)]


def _cycle(length):
    """Cycle C_length; bipartite when length is even, diameter length // 2."""
    return length, [(i, (i + 1) % length) for i in range(length)]


def _pg_baseline(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1 (diameter 3)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# New construction: bipartite "vertex-pair insertion" growth with edge-swap
# annealing.
#
# State: S vertices per side. A-vertex i is labelled i, B-vertex j is labelled
# S + j. Every vertex has degree exactly d, edges are stored as local (a, b)
# pairs with no duplicates.
#
# Growth step (_insert_pair): choose d pairwise-disjoint edges (a_i, b_i).
# Replace each by (a_i, new_B) and add (new_A, b_i). Then new_A and new_B both
# have degree d, every old vertex keeps degree d, and bipartiteness holds.
#
# Repair (_anneal): double-edge swaps (a1,b1),(a2,b2) -> (a1,b2),(a2,b1).
# These preserve all degrees and bipartiteness. The cost is the number of
# ordered vertex pairs at distance > D, computed with bitmask balls.
# ----------------------------------------------------------------------------

def _bad_pairs_local(S, E, D):
    """Ordered pairs of vertices at distance > D in the state (E, S). Zero means valid."""
    N = 2 * S
    adj = [[] for _ in range(N)]
    for a, b in E:
        bb = S + b
        adj[a].append(bb)
        adj[bb].append(a)
    ball = [1 << v for v in range(N)]
    for _ in range(D):
        new = []
        for v in range(N):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return sum(N - x.bit_count() for x in ball)


def _insert_pair(S, E, Es, d, rng):
    """Insert one new A-vertex S and one new B-vertex S, keeping all degrees equal to d.

    Picks d disjoint edges (a_i, b_i). Each becomes (a_i, S) and a new edge (S, b_i) is added.
    Returns False if d disjoint edges cannot be found.
    """
    order = list(range(len(E)))
    rng.shuffle(order)
    used_a, used_b, chosen = set(), set(), []
    for t in order:
        a, b = E[t]
        if a in used_a or b in used_b:
            continue
        used_a.add(a)
        used_b.add(b)
        chosen.append(t)
        if len(chosen) == d:
            break
    if len(chosen) < d:
        return False
    for t in chosen:
        a, b = E[t]
        Es.discard((a, b))
        E[t] = (a, S)
        Es.add((a, S))
        E.append((S, b))
        Es.add((S, b))
    return True


def _anneal(S, E, Es, D, rng, deadline, max_evals, T0):
    """Double-edge-swap annealing on E until the state has zero bad pairs.

    Returns (cost, evals). Mutates E and Es in place.
    """
    cost = _bad_pairs_local(S, E, D)
    evals = 0
    T = T0
    m = len(E)
    while cost > 0 and evals < max_evals:
        if time.monotonic() > deadline:
            break
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        n1 = (a1, b2)
        n2 = (a2, b1)
        if n1 in Es or n2 in Es:
            continue
        Es.discard((a1, b1))
        Es.discard((a2, b2))
        E[i] = n1
        E[j] = n2
        Es.add(n1)
        Es.add(n2)
        c2 = _bad_pairs_local(S, E, D)
        evals += 1
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
        else:
            Es.discard(n1)
            Es.discard(n2)
            E[i] = (a1, b1)
            E[j] = (a2, b2)
            Es.add((a1, b1))
            Es.add((a2, b2))
        T = max(0.5, T * 0.998)
    return cost, evals


def _grow_search(d, D, deadline, rng):
    """Repeat insert-then-anneal from K_{d,d}, keeping the last valid state.

    Returns (S, E) for the largest valid state reached. Final graph has 2S vertices.
    """
    S0 = d
    E0 = [(i, j) for i in range(d) for j in range(d)]
    Sv, Ev = S0, list(E0)
    fails = 0
    while time.monotonic() < deadline and fails < 3:
        E = list(Ev)
        Es = set(E)
        S = Sv
        if not _insert_pair(S, E, Es, d, rng):
            break
        S += 1
        cost, _ = _anneal(S, E, Es, D, rng, deadline, 400, 2.0)
        if cost == 0:
            Sv, Ev = S, list(E)
            fails = 0
        else:
            fails += 1
    return Sv, Ev


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit - 1.0
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    if d == 1:
        return 2, [(0, 1)]
    if d == 2:
        n, e = _cycle(2 * D)
        return n, e

    # D >= 2 and d >= 3 here.
    best_n, best_e = _complete_bipartite(d)

    if D >= 3:
        pg = _pg_baseline(d)
        if pg is not None and pg[0] > best_n:
            best_n, best_e = pg

    if d >= 3:
        Sv, Ev = _grow_search(d, D, deadline, rng)
        if 2 * Sv > best_n:
            cand_n = 2 * Sv
            cand_e = [(a, Sv + b) for a, b in Ev]
            if lib.is_valid(cand_n, cand_e, d, D):
                best_n, best_e = cand_n, cand_e

    if not lib.is_valid(best_n, best_e, d, D):
        return _complete_bipartite(d)
    return best_n, best_e
