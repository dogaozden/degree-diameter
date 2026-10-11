import math
import random
import time

import lib


def _pg_base(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d (points 0..m-1, lines m..2m-1)."""
    for q in range(d - 1, 1, -1):
        if q <= 32 and lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _make_adj(n, E):
    adj = [set() for _ in range(n)]
    for a, b in E:
        adj[a].add(b)
        adj[b].add(a)
    return adj


def _bad_pairs(n, adj):
    """Number of unordered vertex pairs at distance > 3 (bitmask radius-3 balls)."""
    reach = [1 << v for v in range(n)]
    for _ in range(3):
        nxt = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            nxt.append(r)
        reach = nxt
    return sum(n - r.bit_count() for r in reach) // 2


def _ball2(v, adj):
    m = 1 << v
    for u in adj[v]:
        m |= 1 << u
        for w in adj[u]:
            m |= 1 << w
    return m


def _cover(cands, adj, n_cov, d, rng):
    """Greedy choice of up to d candidates whose radius-2 balls cover vertices 0..n_cov-1.

    Returns (chosen, complete). If incomplete, chosen is still usable as a starting wiring.
    """
    full = (1 << n_cov) - 1
    masks = {c: _ball2(c, adj) & full for c in cands}
    covered = 0
    chosen = []
    remaining = sorted(cands)
    while covered != full and len(chosen) < d and remaining:
        best_c, best_g = None, -1.0
        for c in remaining:
            g = (masks[c] & ~covered).bit_count() + 0.5 * rng.random()
            if g > best_g:
                best_c, best_g = c, g
        remaining.remove(best_c)
        chosen.append(best_c)
        covered |= masks[best_c]
    return chosen, covered == full


def _repair(n, side, E, d, deadline, rng):
    """Anneal degree-respecting edits (edge additions and 2-switches) to drive bad-pair count to 0.

    Mutates E in place. Returns the edge list on success, None on timeout.
    """
    adj = _make_adj(n, E)
    A = [v for v in range(n) if side[v] == 0]
    B = [v for v in range(n) if side[v] == 1]
    cost = _bad_pairs(n, adj)
    t0 = time.monotonic()
    span = max(deadline - t0, 1e-3)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            return None
        T = 0.8 * (0.02 ** ((now - t0) / span))
        if rng.random() < 0.5:
            defA = [a for a in A if len(adj[a]) < d]
            defB = [b for b in B if len(adj[b]) < d]
            if defA and defB:
                a = rng.choice(defA)
                b = rng.choice(defB)
                if b not in adj[a]:
                    adj[a].add(b)
                    adj[b].add(a)
                    E.append((a, b))
                    c2 = _bad_pairs(n, adj)
                    if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                        cost = c2
                    else:
                        adj[a].discard(b)
                        adj[b].discard(a)
                        E.pop()
                continue
        if len(E) < 2:
            continue
        i = rng.randrange(len(E))
        j = rng.randrange(len(E))
        a, b = E[i]
        c, e = E[j]
        if a == c or b == e or e in adj[a] or b in adj[c]:
            continue
        # 2-switch: (a,b),(c,e) -> (a,e),(c,b); degrees unchanged.
        adj[a].discard(b); adj[b].discard(a)
        adj[c].discard(e); adj[e].discard(c)
        adj[a].add(e); adj[e].add(a)
        adj[c].add(b); adj[b].add(c)
        c2 = _bad_pairs(n, adj)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
            E[i] = (a, e)
            E[j] = (c, b)
        else:
            adj[a].discard(e); adj[e].discard(a)
            adj[c].discard(b); adj[b].discard(c)
            adj[a].add(b); adj[b].add(a)
            adj[c].add(e); adj[e].add(c)
    return E


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit - 0.5
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2, valid for D >= 2.
    fb_n, fb_E = lib.haar_graph(d, range(d))
    best_n, best_E = fb_n, list(fb_E)

    pg = None
    if D >= 3:
        pg = _pg_base(d)
        if pg is not None and lib.is_valid(pg[0], pg[1], d, D):
            best_n, best_E = pg[0], list(pg[1])
        else:
            pg = None

    # Bold path for D = 3: grow by adding vertex pairs, then repair.
    if D == 3 and pg is not None and d >= 5:
        best_side = [0] * (best_n // 2) + [1] * (best_n // 2)
        while time.monotonic() < deadline - 0.5:
            n = best_n
            side = best_side + [0, 1]
            x, y = n, n + 1
            adj = _make_adj(n, best_E)
            adj.append(set())
            adj.append(set())
            E = list(best_E)

            # New x (side 0) joins side-1 vertices that cover the old graph within distance 2.
            Bc = [v for v in range(n) if side[v] == 1 and len(adj[v]) < d]
            S, _ = _cover(Bc, adj, n, d, rng)
            for b in S:
                E.append((x, b))
                adj[x].add(b)
                adj[b].add(x)

            # New y (side 1) joins side-0 vertices covering everything including x.
            Ac = [v for v in range(n + 1) if side[v] == 0 and len(adj[v]) < d]
            T2, _ = _cover(Ac, adj, n + 1, d, rng)
            for a in T2:
                E.append((a, y))
                adj[a].add(y)
                adj[y].add(a)

            att_deadline = min(deadline, time.monotonic() + 8.0)
            res = _repair(n + 2, side, E, d, att_deadline, rng)
            if res is not None and lib.is_valid(n + 2, res, d, D):
                best_n, best_E = n + 2, list(res)
                best_side = side

    if lib.is_valid(best_n, best_E, d, D):
        return best_n, best_E
    return fb_n, list(fb_E)
