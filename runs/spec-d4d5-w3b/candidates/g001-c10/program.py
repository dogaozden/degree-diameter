import math
import random
import time

import lib

# Idea: a Haar-type graph over a finite group G with connection set S (|S| = d) has
# vertices A_x, B_y (x, y in G), with A_x ~ B_{x*s} for s in S. Left multiplication
# is an automorphism that moves A_x to A_{hx}, so the graph is transitive on each side.
# Hence diameter <= D is equivalent to: BFS from A_e and from B_e reaches every
# vertex within D steps. This replaces an all-pairs check with two BFS runs.
# Non-abelian groups Z_m x| Z_k avoid the abelian limitations of cyclic Haar graphs.

TRIES_PER_ORDER = 2500


def _specs(N):
    """Groups of order N as (m, k, r): Z_m x| Z_k with generator action r. (N, 1, 1) is cyclic."""
    specs = [(N, 1, 1)]
    for k in range(2, N):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                specs.append((m, k, r))
    return specs


class _Group:
    def __init__(self, m, k, r):
        order, mul, inv = lib.semidirect_group(m, k, r)
        self.order = order
        self.table = [[mul(x, y) for y in range(order)] for x in range(order)]
        self.inv = [inv(x) for x in range(order)]


def _adjacency(G, S):
    """Adjacency lists of the group Haar graph; A_x = x, B_y = G.order + y."""
    N = G.order
    T = G.table
    adj = [None] * (2 * N)
    for x in range(N):
        row = T[x]
        adj[x] = [N + row[s] for s in S]
    for y in range(N):
        row = T[y]
        adj[N + y] = [row[G.inv[s]] for s in S]
    return adj


def _two_root_ok(adj, total, D):
    """True if BFS from A_e (vertex 0) and B_e (vertex total/2) reaches all vertices within D steps."""
    for src in (0, total // 2):
        seen = bytearray(total)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            count += len(nxt)
            if count == total:
                break
            frontier = nxt
            if not frontier:
                break
        if count != total:
            return False
    return True


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit

    if D < 2:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid for D >= 2

    if D == 3:
        if lib.is_prime_power(d - 1):
            return lib.projective_plane_incidence(d - 1)
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                cand = lib.araujo_lopez_graph(d - 2)
                if lib.is_valid(cand[0], cand[1], d, D):
                    best = cand
            except Exception:
                pass

    rng = random.Random(seed)
    N = max(d, 3)
    fails = 0
    while fails < 8 and time.monotonic() < deadline:
        specs = _specs(N)
        groups = {}  # cache per order, keeps memory bounded

        def group(spec):
            if spec not in groups:
                groups[spec] = _Group(*spec)
            return groups[spec]

        found = None
        tries = 0
        while tries < TRIES_PER_ORDER and time.monotonic() < deadline:
            tries += 1
            spec = specs[rng.randrange(len(specs))]
            G = group(spec)
            S = rng.sample(range(G.order), d)
            if _two_root_ok(_adjacency(G, S), 2 * N, D):
                found = (spec, S)
                break

        if found is not None:
            spec, S = found
            G = group(spec)
            edges = [(x, N + G.table[x][s]) for x in range(N) for s in S]
            n = 2 * N
            if lib.is_valid(n, edges, d, D) and n > best[0]:
                best = (n, edges)
                fails = 0
            else:
                fails += 1
        else:
            fails += 1
        N += 1

    return best
