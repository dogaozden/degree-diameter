import random
import time

import lib


def _two_coloring(n, edges):
    """Return a side label (0 or 1) for each vertex, from a BFS 2-colouring of the graph."""
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


def _augment_with_pairs(n, edges, d, D, deadline, rng):
    """Greedily add vertex pairs (a in side 0, b in side 1) that use spare degree.

    The new pair is joined to each other, a is joined to up to d-1 deficient side-1
    vertices and b to up to d-1 deficient side-0 vertices. A pair is kept only if the
    whole graph still passes lib.is_valid, so the result is always valid.
    """
    edges = list(edges)
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    col = _two_coloring(n, edges)

    while time.monotonic() < deadline:
        dA = [v for v in range(n) if col[v] == 0 and deg[v] < d]
        dB = [v for v in range(n) if col[v] == 1 and deg[v] < d]
        if not dA or not dB:
            break
        ks = min(d - 1, len(dB))
        kt = min(d - 1, len(dA))
        accepted = False
        # Random trials; each trial is one full validity check.
        for _ in range(60):
            if time.monotonic() >= deadline:
                break
            S = rng.sample(dB, ks)
            T = rng.sample(dA, kt)
            a, b = n, n + 1
            new = [(a, b)] + [(a, s) for s in S] + [(t, b) for t in T]
            trial = edges + new
            if lib.is_valid(n + 2, trial, d, D):
                edges = trial
                n += 2
                deg.extend([0, 0])
                for u, v in new:
                    deg[u] += 1
                    deg[v] += 1
                col.extend([0, 1])
                accepted = True
                break
        if not accepted and time.monotonic() < deadline:
            # Also try a few trials with a smaller neighbourhood to diversify.
            ks2 = max(1, ks // 2)
            kt2 = max(1, kt // 2)
            for _ in range(20):
                if time.monotonic() >= deadline:
                    break
                S = rng.sample(dB, min(ks2, len(dB)))
                T = rng.sample(dA, min(kt2, len(dA)))
                a, b = n, n + 1
                new = [(a, b)] + [(a, s) for s in S] + [(t, b) for t in T]
                trial = edges + new
                if lib.is_valid(n + 2, trial, d, D):
                    edges = trial
                    n += 2
                    deg.extend([0, 0])
                    for u, v in new:
                        deg[u] += 1
                        deg[v] += 1
                    col.extend([0, 1])
                    accepted = True
                    break
        if not accepted:
            # Nothing extends the current graph in this round; keep sampling until the
            # deadline in case a different deficient set works, but avoid a busy loop.
            if time.monotonic() >= deadline:
                break
    return n, edges


def _haar_search(d, D, deadline, rng):
    """Fallback: random Haar-graph search (always valid)."""
    best = lib.haar_graph(d, range(d))  # K_{d,d}, always valid
    m, misses = d + 1, 0
    while time.monotonic() < deadline and misses < 10:
        found = None
        for _ in range(30):
            if time.monotonic() >= deadline:
                break
            S = [0] + rng.sample(range(1, m), d - 1)
            n, edges = lib.haar_graph(m, S)
            if lib.within_diameter(n, edges, D):
                found = (n, edges)
                break
        if found:
            best, misses = found, 0
        else:
            misses += 1
        m += 1
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.8 * time_limit)
    rng = random.Random(seed)

    if D == 3:
        # Case 1: d-1 is a prime power -> projective plane incidence graph (optimal).
        q = d - 1
        if q >= 2 and lib.is_prime_power(q):
            try:
                n, edges = lib.projective_plane_incidence(q)
                if lib.is_valid(n, edges, d, D):
                    return n, edges
            except (ValueError, AssertionError):
                pass

        # Case 2: q = d-2 is a prime power -> Araujo-Pardo & Lopez record graph,
        # then greedy augmentation with spare degree, verified at every step.
        q2 = d - 2
        if q2 >= 3 and lib.is_prime_power(q2):
            try:
                n, edges = lib.araujo_lopez_graph(q2)
                if lib.is_valid(n, edges, d, D):
                    best_n, best_edges = n, edges
                    aug_n, aug_edges = _augment_with_pairs(
                        n, edges, d, D, deadline, rng)
                    if aug_n > best_n and lib.is_valid(aug_n, aug_edges, d, D):
                        return aug_n, aug_edges
                    return best_n, best_edges
            except (ValueError, AssertionError):
                pass

    # Fallback for every other case.
    best = _haar_search(d, D, deadline, rng)
    n, edges = best
    if lib.is_valid(n, edges, d, D):
        return n, edges
    n, edges = lib.haar_graph(d, range(d))
    return n, edges
