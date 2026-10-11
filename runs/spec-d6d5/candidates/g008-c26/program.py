import random
import time

import lib

# Bold change for D >= 3: instead of voltage lifts, grow a d-regular bipartite
# graph one vertex pair at a time. Each step adds a new A-B pair by splicing d
# matching edges, then anneals with degree-preserving double-edge swaps until
# every pair is within distance D. Untested: no runs were done, so the outer
# validation with lib.is_valid and the PG/K_{d,d} fallbacks guard the output.


def _bad(M, adj, D):
    """Ordered pairs at distance > D (bitset BFS). Zero iff diameter <= D."""
    reach = [1 << v for v in range(M)]
    for _ in range(D):
        new = []
        for v in range(M):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(M - r.bit_count() for r in reach)


def _rewire(adj, a, b, c, e):
    """Replace edges a-b and c-e (a, c on side A; b, e on side B) by a-e and c-b."""
    adj[a].discard(b)
    adj[b].discard(a)
    adj[c].discard(e)
    adj[e].discard(c)
    adj[a].add(e)
    adj[e].add(a)
    adj[c].add(b)
    adj[b].add(c)


def _circulant(d):
    """Bipartite circulant K_{d,d}: A_i ~ B_{(i+s) mod d} for s in 0..d-1."""
    h = d
    M = 2 * h
    adj = [set() for _ in range(M)]
    E = []
    for i in range(h):
        for s in range(d):
            a, b = i, h + (i + s) % h
            adj[a].add(b)
            adj[b].add(a)
            E.append((a, b))
    return M, adj, E


def _randomize(adj, E, rng, steps):
    """Degree-preserving random double-edge swaps (no cost check)."""
    if len(E) < 2:
        return
    for _ in range(steps):
        i = rng.randrange(len(E))
        j = rng.randrange(len(E))
        if i == j:
            continue
        a, b = E[i]
        c, e = E[j]
        if a == c or b == e or e in adj[a] or b in adj[c]:
            continue
        _rewire(adj, a, b, c, e)
        E[i] = (a, e)
        E[j] = (c, b)


def _grow(st, d, rng):
    """Add one A vertex and one B vertex, each of degree d, by splicing a matching of d edges."""
    M, adj, E = st
    order = list(range(len(E)))
    rng.shuffle(order)
    used_a, used_b, pick = set(), set(), []
    for idx in order:
        a, b = E[idx]
        if a in used_a or b in used_b:
            continue
        used_a.add(a)
        used_b.add(b)
        pick.append(idx)
        if len(pick) == d:
            break
    if len(pick) < d:
        return None
    adj2 = [set(s) for s in adj]
    adj2.append(set())  # new A vertex, index M
    adj2.append(set())  # new B vertex, index M + 1
    na, nb = M, M + 1
    picked = set(pick)
    for idx in pick:
        a, b = E[idx]
        adj2[a].discard(b)
        adj2[b].discard(a)
    newE = [e for k, e in enumerate(E) if k not in picked]
    for idx in pick:
        a, b = E[idx]
        adj2[a].add(nb)
        adj2[nb].add(a)
        newE.append((a, nb))
        adj2[b].add(na)
        adj2[na].add(b)
        newE.append((na, b))
    return M + 2, adj2, newE


def _anneal(st, D, deadline, rng):
    """Swap-anneal st in place until diameter <= D or deadline. Returns remaining bad count."""
    M, adj, E = st
    cost = _bad(M, adj, D)
    while cost and time.monotonic() < deadline:
        i = rng.randrange(len(E))
        j = rng.randrange(len(E))
        if i == j:
            continue
        a, b = E[i]
        c, e = E[j]
        if a == c or b == e or e in adj[a] or b in adj[c]:
            continue
        _rewire(adj, a, b, c, e)
        new = _bad(M, adj, D)
        if new <= cost or rng.random() < 0.02:
            cost = new
            E[i] = (a, e)
            E[j] = (c, b)
        else:
            _rewire(adj, a, e, c, b)
    return cost


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.80 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    fallback = lib.haar_graph(d, range(d))
    if D < 3 or d < 3:
        return fallback

    best = fallback
    # Projective plane incidence graph when d-1 (or a smaller prime power) allows it.
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            n, e = lib.projective_plane_incidence(q)
            if lib.is_valid(n, e, d, D):
                best = (n, e)
            break
    best_n = best[0]

    good = None  # (n, edges) of the largest state reached with cost 0
    while time.monotonic() < deadline:
        M, adj, E = _circulant(d)
        _randomize(adj, E, rng, 10 * len(E))
        st = (M, adj, E)
        fails = 0
        while fails < 6 and time.monotonic() < deadline:
            nxt = _grow(st, d, rng)
            if nxt is None:
                break
            now = time.monotonic()
            budget = min(deadline, now + max(0.5, 0.15 * (deadline - now)))
            cost = _anneal(nxt, D, budget, rng)
            if cost == 0:
                st = nxt
                fails = 0
                if good is None or nxt[0] > good[0]:
                    good = (nxt[0], [(a, b) for a, b in nxt[2]])
            else:
                fails += 1

    if good is not None and good[0] > best_n and lib.is_valid(good[0], good[1], d, D):
        best = good
    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
