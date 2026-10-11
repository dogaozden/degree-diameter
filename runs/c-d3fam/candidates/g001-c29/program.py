import random
import time

import lib

TIME_FRAC = 0.85     # fraction of time_limit used before returning
SAFETY = 1.5         # seconds reserved for final validation and output
SLICE = 3.0          # seconds per randomized extension attempt
MAX_ROUNDS = 40      # cap on randomized extension attempts


# ---------------------------------------------------------------- shared helpers

def _two_colour(n, edges):
    """Return a proper 2-colouring (0/1 per vertex) of a bipartite graph, component by component."""
    adj = lib.adjacency(n, edges)
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
    return color


def _extend(n, edges, d, D, rng, deadline):
    """Greedily add new vertices, each attached to a set cover of the radius-(D-1) balls.

    A new vertex x with neighbour set N is within distance D of every old vertex iff the
    radius-(D-1) balls of N cover all vertices. Old pairs only get closer, so the diameter
    bound is preserved. Degree and bipartiteness are preserved by construction.
    """
    edges = list(edges)
    if D < 2 or n == 0:
        return n, edges
    color = _two_colour(n, edges)
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1

    while time.monotonic() < deadline:
        full = (1 << n) - 1
        balls = lib._balls(n, edges, D - 1)
        grown = False
        order = [0, 1] if rng.random() < 0.5 else [1, 0]
        for c in order:
            cand = [u for u in range(n) if color[u] == 1 - c and deg[u] < d]
            rng.shuffle(cand)
            covered, chosen = 0, []
            while covered != full and len(chosen) < d and cand:
                best_u, best_gain = -1, 0
                for u in cand:
                    g = (balls[u] & ~covered).bit_count()
                    if g > best_gain:
                        best_u, best_gain = u, g
                if best_u < 0:
                    break
                chosen.append(best_u)
                covered |= balls[best_u]
                cand.remove(best_u)
            if covered == full and chosen:
                x = n
                n += 1
                color.append(c)
                deg.append(len(chosen))
                for u in chosen:
                    edges.append((u, x))
                    deg[u] += 1
                grown = True
                break
        if not grown:
            break
    return n, edges


def _augment(n, edges, d, seed):
    """Add edges between opposite colour classes using spare degree (keeps bipartite and diameter)."""
    rng = random.Random(seed + 7)
    color = _two_colour(n, edges)
    deg = [0] * n
    adj = [set() for _ in range(n)]
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
        adj[u].add(v)
        adj[v].add(u)
    side0 = [u for u in range(n) if color[u] == 0]
    side1 = [v for v in range(n) if color[v] == 1]
    new_edges = list(edges)
    for _ in range(3):
        us = [u for u in side0 if deg[u] < d]
        rng.shuffle(us)
        for u in us:
            if deg[u] >= d:
                continue
            cands = [v for v in side1 if deg[v] < d and v not in adj[u]]
            if not cands:
                continue
            v = rng.choice(cands)
            adj[u].add(v)
            adj[v].add(u)
            deg[u] += 1
            deg[v] += 1
            new_edges.append((u, v))
    return n, new_edges


def _finish(cands, d, D):
    """Return the largest candidate that passes lib.is_valid, else K_{d,d}."""
    for n, e in sorted(cands, key=lambda c: -c[0]):
        try:
            if lib.is_valid(n, e, d, D):
                return n, e
        except Exception:
            continue
    return lib.haar_graph(d, range(d))


# ---------------------------------------------------------------- base constructions

def _pg_base(d):
    """Incidence graph of PG(2,q), q the largest prime power <= d-1 (diameter 3)."""
    q = d - 1
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    if q < 2:
        return None
    return lib.projective_plane_incidence(q)


def _ar_base(d):
    """Araujo-Pardo & Lopez record graph for degree d = q+2 with q a prime power >= 3 (diameter 3).

    Order 2(q^2+q+5). This is the record for d = 11, 13, 15 (orders 190, 274, 374).
    """
    q = d - 2
    if q < 3 or not lib.is_prime_power(q):
        return None
    try:
        return lib.araujo_lopez_graph(q)
    except Exception:
        return None


# ---------------------------------------------------------------- randomized growth

def _grow_loop(bases, d, D, seed, deadline):
    """Repeatedly augment and greedily extend randomly chosen bases with random tie-breaking.

    Every produced graph keeps max degree d, bipartiteness, and diameter D (by construction),
    and the caller still validates each candidate with lib.is_valid.
    """
    rng = random.Random(seed)
    out = []
    if not bases:
        return out
    rounds = 0
    while time.monotonic() < deadline and rounds < MAX_ROUNDS:
        rounds += 1
        n, e = bases[rng.randrange(len(bases))]
        aug = _augment(n, e, d, rng.randrange(1 << 30))
        slice_end = min(deadline, time.monotonic() + SLICE)
        out.append(_extend(aug[0], aug[1], d, D, rng, slice_end))
    return out


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, TIME_FRAC * time_limit - SAFETY)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if D == 2:
        return lib.haar_graph(d, range(d))

    cands = [lib.haar_graph(d, range(d))]   # K_{d,d}: diameter 2, always valid

    if D == 3 and d >= 3:
        # Moore-extremal when d-1 is a prime power: nothing to improve.
        if lib.is_prime_power(d - 1):
            pg = lib.projective_plane_incidence(d - 1)
            return _finish(cands + [pg], d, D)

        bases = []
        pg = _pg_base(d)
        if pg is not None:
            cands.append(pg)
            bases.append(pg)

        # Bold switch: the record construction, which beats the projective-plane route.
        ar = _ar_base(d)
        if ar is not None:
            cands.append(ar)
            bases.insert(0, ar)
            bases.append(ar)  # weight the record base more heavily

        if bases:
            cands.extend(_grow_loop(bases, d, D, seed + 11, deadline))
    else:
        # Outside the D = 3 targets: projective-plane start, extended with the same loop.
        if d >= 3:
            pg = _pg_base(d)
            if pg is not None:
                cands.append(pg)
                cands.extend(_grow_loop([pg], d, D, seed + 13, deadline))

    return _finish(cands, d, D)
