import random
import time

import lib


def _pg_data(q):
    """Return (m, edges, point_lines, line_points) for PG(2, q); points are 0..m-1, lines are indexed 0..m-1."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    return m, edges, point_lines, line_points


# ----------------------------------------------------------------------------
# Capped packing (new helper).
#
# Element e carries a list cons[e] of constraint ids in 0..m-1. A chosen set S
# is feasible when every constraint c is used by at most `cap` chosen elements.
# Local search: a random unchosen element enters if it is feasible; otherwise,
# if it blocks exactly one chosen element (plateau swap), or occasionally two,
# those blockers leave and it enters. The state is restored to the best set
# seen whenever the current set drifts too far below it.
# ----------------------------------------------------------------------------

def _capped_packing(m, cons, cap, rng, deadline):
    load = [0] * m
    members = [set() for _ in range(m)]
    chosen = [False] * m
    S = set()

    def add(e):
        chosen[e] = True
        S.add(e)
        for c in cons[e]:
            load[c] += 1
            members[c].add(e)

    def remove(e):
        chosen[e] = False
        S.discard(e)
        for c in cons[e]:
            load[c] -= 1
            members[c].discard(e)

    order = list(range(m))
    rng.shuffle(order)
    for e in order:
        if all(load[c] < cap for c in cons[e]):
            add(e)
    best = list(S)

    it = 0
    while True:
        it += 1
        if (it & 127) == 0 and time.monotonic() > deadline:
            break
        if len(S) < len(best) - 2:
            for e in list(S):
                remove(e)
            for e in best:
                add(e)
        e = rng.randrange(m)
        if chosen[e]:
            continue
        full = [c for c in cons[e] if load[c] >= cap]
        if not full:
            add(e)
        else:
            B = set()
            for c in full:
                B |= members[c]
            if len(B) == 1 or (len(B) == 2 and rng.random() < 0.03):
                for r in B:
                    remove(r)
                add(e)
            else:
                continue
        if len(S) > len(best):
            best = list(S)
    return best


def _graph_from_sets(m, edges, point_lines, line_points, A, B):
    """PG(2,q) incidence plus one new vertex per point in A (joined to its lines)
    and one new vertex per line in B (joined to its points). A and B are chosen
    independently, so the two sides use separate spare degree. Diameter stays 3."""
    na, nb = len(A), len(B)
    n = 2 * m + na + nb
    E = list(edges)
    for i, P in enumerate(A):
        x = 2 * m + i
        for L in point_lines[P]:
            E.append((x, m + L))
    for j, L in enumerate(B):
        y = 2 * m + na + j
        for Q in line_points[L]:
            E.append((Q, y))
    return n, E


def _twin_saturate(n, edges, d, rng, deadline):
    """Repeatedly add twins (same neighbourhood) of vertices whose neighbours all have spare degree."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    while time.monotonic() < deadline:
        elig = [v for v in range(n)
                if adj[v] and all(len(adj[u]) < d for u in adj[v])]
        if not elig:
            break
        v = rng.choice(elig)
        t = n
        n += 1
        nb = list(adj[v])
        adj.append(nb)
        for u in nb:
            adj[u].append(t)
            edges.append((u, t))
    return n, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    twin_deadline = start + 0.9 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best_n = 2 * d
    best_e = [(i, d + j) for i in range(d) for j in range(d)]

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    if D >= 3:
        # Plain projective plane of the largest prime-power order q with q + 1 <= d.
        base_qs = [q for q in range(2, d) if lib.is_prime_power(q)]
        if base_qs:
            n0, e0 = lib.projective_plane_incidence(base_qs[-1])
            consider(n0, e0)

        # Independent-capped-packing extensions, one candidate per prime power q.
        cands = []
        for q in range(2, min(d - 1, 23) + 1):
            if not lib.is_prime_power(q):
                continue
            s = d - q - 1
            if s < 1:
                continue
            m = q * q + q + 1
            bound = 2 * m + 2 * (s * m // (q + 1))
            cands.append((bound, q, s))
        cands.sort(reverse=True)

        for idx, (bound, q, s) in enumerate(cands):
            if bound <= best_n:
                continue
            now = time.monotonic()
            if now >= deadline:
                break
            frac = 0.85 if idx == 0 else 1.0
            q_deadline = now + (deadline - now) * frac
            m, edges, pl, lp = _pg_data(q)
            bestA, bestB = [], []
            rounds = 4
            for r in range(rounds):
                t0 = time.monotonic()
                if t0 >= q_deadline:
                    break
                slot = (q_deadline - t0) / (rounds - r)
                # The two sides are independent problems, so each keeps its own best.
                A = _capped_packing(m, pl, s, rng, t0 + 0.5 * slot)
                B = _capped_packing(m, lp, s, rng, t0 + slot)
                if len(A) > len(bestA):
                    bestA = A
                if len(B) > len(bestB):
                    bestB = B
                if bestA and bestB:
                    n, e = _graph_from_sets(m, edges, pl, lp, bestA, bestB)
                    consider(n, e)

    # Spend the remaining margin on diameter-preserving twins.
    n3, e3 = _twin_saturate(best_n, best_e, d, rng, twin_deadline)
    consider(n3, e3)

    if not lib.is_valid(best_n, best_e, d, D):
        return 2 * d, [(i, d + j) for i in range(d) for j in range(d)]
    return best_n, best_e
