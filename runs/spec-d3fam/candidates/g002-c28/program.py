# Bold variant for D=3: start from the best known D=3 base graph (projective plane or
# Araujo-Pardo-Lopez graph), then grow it one vertex per side at a time. Each growth step
# is repaired by simulated annealing over bipartite edge moves (spare-capacity edge adds,
# degree-preserving 2-switches, and transfers that attach new vertices), with the cost
# counting pairs at distance > 3 computed from biadjacency matrix products. Every returned
# graph is checked with lib.is_valid, and the best valid graph seen is always returned.
# Untested: no run has confirmed that this beats the records on d=11, 13, 15.

import math
import random
import time

import numpy as np

import lib


def _bipart_colors(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
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


def _base(d, D):
    """Best valid base graph among a few safe constructions, or None."""
    cands = []
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            cands.append(lib.projective_plane_incidence(q))
            break
    if d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            cands.append(lib.araujo_lopez_graph(d - 2))
        except (ValueError, StopIteration, KeyError):
            pass
    cands.append(lib.haar_graph(d, range(d)))  # K_{d,d}, diameter 2
    best = None
    for n, e in cands:
        if (best is None or n > best[0]) and lib.is_valid(n, e, d, D):
            best = (n, e)
    return best


def _bad(X):
    """Number of unordered vertex pairs at distance > 3 in the bipartite graph with biadjacency X."""
    nA, nB = X.shape
    Y = X @ X.T          # A-A common-neighbour counts
    Yb = X.T @ X         # B-B common-neighbour counts
    Z = Y @ X            # walks a - b' - a' - b
    sa = int(np.count_nonzero(np.triu(Y > 0, 1)))
    sb = int(np.count_nonzero(np.triu(Yb > 0, 1)))
    cr = int(np.count_nonzero((Z + X) > 0))
    return (nA * (nA - 1) // 2 - sa) + (nB * (nB - 1) // 2 - sb) + (nA * nB - cr)


def _anneal(X, E, degA, degB, d, deadline, rng):
    """Anneal in place until cost 0 or deadline. Returns the final cost."""
    cost = _bad(X)
    T = 1.0
    it = 0
    while cost > 0 and time.monotonic() < deadline:
        it += 1
        if it % 100 == 0:
            T = max(0.25, T * 0.93)
        nA, nB = X.shape
        spA = [a for a in range(nA) if degA[a] < d]
        spB = [b for b in range(nB) if degB[b] < d]
        r = rng.random()
        if spA and spB and r < 0.2:
            # Spare add: always non-increasing in cost, so always accept.
            a = rng.choice(spA)
            b = rng.choice(spB)
            if X[a, b] != 0:
                continue
            X[a, b] = 1
            degA[a] += 1
            degB[b] += 1
            E.append((a, b))
            cost = _bad(X)
        elif spA and spB and r < 0.55 and E:
            # Transfer: (a,b) -> (v,b) and (a,w), with v, w spare.
            i = rng.randrange(len(E))
            a, b = E[i]
            v = rng.choice(spA)
            w = rng.choice(spB)
            if v == a or w == b or X[v, b] != 0 or X[a, w] != 0:
                continue
            X[a, b] = 0
            X[v, b] = 1
            X[a, w] = 1
            E[i] = (v, b)
            E.append((a, w))
            degA[v] += 1
            degB[w] += 1
            new = _bad(X)
            if new <= cost or rng.random() < math.exp(-(new - cost) / T):
                cost = new
            else:
                X[a, w] = 0
                X[v, b] = 0
                X[a, b] = 1
                E.pop()
                E[i] = (a, b)
                degA[v] -= 1
                degB[w] -= 1
        elif len(E) >= 2:
            # Degree-preserving 2-switch: (a,b),(c,e) -> (a,e),(c,b).
            i, j = rng.sample(range(len(E)), 2)
            a, b = E[i]
            c, e = E[j]
            if a == c or b == e or X[a, e] != 0 or X[c, b] != 0:
                continue
            X[a, b] = 0
            X[c, e] = 0
            X[a, e] = 1
            X[c, b] = 1
            E[i] = (a, e)
            E[j] = (c, b)
            new = _bad(X)
            if new <= cost or rng.random() < math.exp(-(new - cost) / T):
                cost = new
            else:
                X[a, e] = 0
                X[c, b] = 0
                X[a, b] = 1
                X[c, e] = 1
                E[i] = (a, b)
                E[j] = (c, e)
    return cost


def _to_graph(X):
    nA = X.shape[0]
    rows, cols = np.nonzero(X)
    edges = [(int(a), nA + int(b)) for a, b in zip(rows.tolist(), cols.tolist())]
    return nA + X.shape[1], edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.7 * time_limit

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Moore-optimal D=3 case: PG(2, d-1) incidence graph.
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n, e, d, D):
            return n, e

    best = _base(d, D)
    if best is None:
        return 2, [(0, 1)]
    if D != 3 or d < 3:
        return best

    # Bold growth-and-repair search for D = 3.
    n0, e0 = best
    colors = _bipart_colors(n0, e0)
    idx = [0] * n0
    nA = nB = 0
    for v in range(n0):
        if colors[v] == 0:
            idx[v] = nA
            nA += 1
        else:
            idx[v] = nB
            nB += 1
    X = np.zeros((nA, nB), dtype=np.float32)
    E = []
    degA = [0] * nA
    degB = [0] * nB
    for u, v in e0:
        if colors[u] == 0:
            a, b = idx[u], idx[v]
        else:
            a, b = idx[v], idx[u]
        X[a, b] = 1
        E.append((a, b))
        degA[a] += 1
        degB[b] += 1

    rng = random.Random(seed)
    fails = 0
    while fails < 3 and time.monotonic() < deadline:
        remaining = deadline - time.monotonic()
        sub = time.monotonic() + 0.5 * remaining
        X2 = np.pad(X, ((0, 1), (0, 1)))
        E2 = list(E)
        dA = degA + [0]
        dB = degB + [0]
        cost = _anneal(X2, E2, dA, dB, d, sub, rng)
        if cost == 0:
            n, e = _to_graph(X2)
            if not lib.is_valid(n, e, d, D):
                break
            if n > best[0]:
                best = (n, e)
            X, E, degA, degB = X2, E2, dA, dB
            fails = 0
        else:
            fails += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
