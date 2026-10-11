import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bipartition helper.
# ----------------------------------------------------------------------------

def _colors(n, edges):
    """Two-colouring of a bipartite graph (BFS); entries may be -1 if isolated and uncoloured."""
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


# ----------------------------------------------------------------------------
# New idea: pair insertion by edge-switching, then bad-pair annealing.
#
# Given a near-regular bipartite graph G with max degree d, add one new vertex x
# on side 0 and one new vertex y on side 1. Each new vertex is wired in by
# "switching": an existing edge (a, b) is replaced by (x, b) (or (a, y)), which
# keeps b (resp. a) at its degree. The leftover deficient vertices are paired
# greedily. A simulated annealing then rewires edges (2-switches, endpoint
# rewires, and additions between deficient vertices), minimising the number of
# vertex pairs at distance more than D. Any zero-cost state is a valid graph
# with two more vertices.
# ----------------------------------------------------------------------------

def _extend_pair(n, edges, color, d, rng):
    """Insert x (side 0) and y (side 1) by edge switching; return (n+2, edges, colors)."""
    x, y = n, n + 1
    color = list(color) + [0, 1]
    E = [(u, v) if color[u] == 0 else (v, u) for u, v in edges]
    S = set(E)
    deg = [0] * (n + 2)
    for a, b in E:
        deg[a] += 1
        deg[b] += 1

    def pick():
        for _ in range(10000):
            i = rng.randrange(len(E))
            a, b = E[i]
            if a != x and b != x and a != y and b != y:
                return i
        return None

    # Attach x by switching d edges (a, b) -> (x, b).
    for _ in range(d):
        for _try in range(50):
            i = pick()
            if i is None:
                break
            a, b = E[i]
            if (x, b) in S:
                continue
            E[i] = (x, b)
            S.discard((a, b))
            S.add((x, b))
            deg[a] -= 1
            deg[x] += 1
            break

    # Attach y by switching d edges (a, b) -> (a, y).
    for _ in range(d):
        for _try in range(50):
            i = pick()
            if i is None:
                break
            a, b = E[i]
            if (a, y) in S:
                continue
            E[i] = (a, y)
            S.discard((a, b))
            S.add((a, y))
            deg[b] -= 1
            deg[y] += 1
            break

    # Greedily pair leftover deficient vertices across the bipartition.
    A = [v for v in range(n + 2) if color[v] == 0 and deg[v] < d]
    B = [v for v in range(n + 2) if color[v] == 1 and deg[v] < d]
    rng.shuffle(A)
    rng.shuffle(B)
    for a in A:
        for b in B:
            if deg[a] >= d:
                break
            if deg[b] < d and (a, b) not in S:
                E.append((a, b))
                S.add((a, b))
                deg[a] += 1
                deg[b] += 1
    return n + 2, E, color


def _repair(n, E, color, d, D, rng, deadline):
    """Anneal on bad-pair count over edge sets with degree <= d; return a zero-cost edge list or None."""
    side0 = [v for v in range(n) if color[v] == 0]
    side1 = [v for v in range(n) if color[v] == 1]
    E = list(E)
    S = set(E)
    deg = [0] * n
    for a, b in E:
        deg[a] += 1
        deg[b] += 1
    cost = lib.bad_pairs(n, E, D)
    if cost == 0:
        return E
    best_cost, best_E = cost, list(E)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)

    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        T = 0.6 + 2.0 * max(0.0, 1.0 - (now - t0) / span)
        r = rng.random()
        undo = None

        if r < 0.4 and len(E) >= 2:
            # 2-switch: preserves all degrees.
            i = rng.randrange(len(E))
            j = rng.randrange(len(E))
            if i == j:
                continue
            a, b = E[i]
            c, e = E[j]
            if a == c or b == e:
                continue
            n1, n2 = (a, e), (c, b)
            if n1 in S or n2 in S:
                continue
            S.discard((a, b))
            S.discard((c, e))
            S.add(n1)
            S.add(n2)
            E[i], E[j] = n1, n2
            undo = ("sw", i, j, (a, b), (c, e), n1, n2)

        elif r < 0.8 and E:
            # Endpoint rewire: keep one endpoint, move the other to a vertex with spare degree.
            i = rng.randrange(len(E))
            a, b = E[i]
            new = None
            if rng.random() < 0.5:
                for _ in range(20):
                    x = rng.choice(side1)
                    if x != b and deg[x] < d and (a, x) not in S:
                        new = (a, x)
                        p = b
                        break
            else:
                for _ in range(20):
                    x = rng.choice(side0)
                    if x != a and deg[x] < d and (x, b) not in S:
                        new = (x, b)
                        p = a
                        break
            if new is None:
                continue
            deg[p] -= 1
            deg[new[0] if new[0] != a or new[1] != b and new[0] != a else new[0]] += 0  # placeholder, fixed below
            xv = new[1] if new[0] == a else new[0]
            deg[xv] += 1
            S.discard((a, b))
            S.add(new)
            E[i] = new
            undo = ("rw", i, (a, b), new, p, xv)

        else:
            # Add an edge between two vertices with spare degree.
            found = None
            for _ in range(30):
                a = rng.choice(side0)
                b = rng.choice(side1)
                if deg[a] < d and deg[b] < d and (a, b) not in S:
                    found = (a, b)
                    break
            if found is None:
                continue
            E.append(found)
            S.add(found)
            deg[found[0]] += 1
            deg[found[1]] += 1
            undo = ("add", found)

        new_cost = lib.bad_pairs(n, E, D)
        delta = new_cost - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = new_cost
            if cost < best_cost:
                best_cost, best_E = cost, list(E)
        else:
            # Revert the move.
            if undo[0] == "sw":
                _, i, j, old1, old2, n1, n2 = undo
                S.discard(n1)
                S.discard(n2)
                S.add(old1)
                S.add(old2)
                E[i], E[j] = old1, old2
            elif undo[0] == "rw":
                _, i, old, new, p, xv = undo
                S.discard(new)
                S.add(old)
                E[i] = old
                deg[p] += 1
                deg[xv] -= 1
            else:
                found = undo[1]
                E.pop()
                S.discard(found)
                deg[found[0]] -= 1
                deg[found[1]] -= 1

    return best_E if best_cost == 0 else None


# ----------------------------------------------------------------------------
# Build.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    best = [best_n, best_e]

    def consider(n, e):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best[0], best[1] = n, e
            return True
        return False

    if D >= 3:
        # Incidence graph of PG(2, q) for the largest prime power q <= d - 1.
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                consider(*lib.projective_plane_incidence(q))
                break
        # Araujo-Pardo and Lopez record family, degree q + 2 with q = d - 2.
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            consider(*lib.araujo_lopez_graph(d - 2))

    # Pair-insertion plus bad-pair annealing, repeated while it succeeds.
    if D == 3:
        rng = random.Random(seed * 1000003 + d)
        while time.monotonic() < deadline:
            n0, e0 = best[0], best[1]
            color = _colors(n0, e0)
            n2, E2, c2 = _extend_pair(n0, e0, color, d, rng)
            res = _repair(n2, E2, c2, d, D, rng, deadline)
            if res is None or not consider(n2, res):
                break

    if not lib.is_valid(best[0], best[1], d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
        return best_n, best_e
    return best[0], best[1]
