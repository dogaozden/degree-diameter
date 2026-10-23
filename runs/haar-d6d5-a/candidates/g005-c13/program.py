"""Voltage-lift search for the d=6, D=5 bipartite degree-diameter target (numpy-free, stdlib + lib only).

NEW CONSTRUCTION (replaces the single-orbit Haar search).
  Base graph: 4 vertices, A0, A1 (one side) and B0, B1 (other side). Each base vertex has degree 6.
  Blocks: the number of darts from A_i to B_j is c[i][j] = [[a, 6-a], [6-a, a]] for some a in 1..5.
  Voltages: each dart (i, j, g) with g in a group G of order N. The lift has vertices (b, x) for base vertex b
  and x in G, and dart (i, j, g) joins (A_i, x) to (B_j, x*g). Within one block the voltages are distinct, so the
  lift is simple and 6-regular, with 4N vertices.

WHY THE CHECK IS CHEAP.  Left multiplication by h in G is an automorphism of the lift, and it preserves each base
fibre. So every vertex lies in the orbit of one of the four representatives (A0, e), (A1, e), (B0, e), (B1, e).
Diameter <= 5 holds iff each representative reaches all 4N vertices within 5 steps. The cost is the total number of
unreached vertices over these four BFS runs. Cost 0 means valid, and the annealer minimises the cost.

SEARCH.  Non-abelian metacyclic groups of order N in [172, 200] are visited round-robin. Each gets a time slice of
simulated annealing over the voltages (one voltage replaced at a time, Metropolis acceptance, restarts when stuck).
A cost-0 lift is verified with lib.is_valid and kept only if it beats the current best.

SAFETY.  A verified 660-vertex Haar graph is the initial fallback. If nothing better is found, it is returned.
If anything raises, the trivial valid graph is returned.
"""
import math
import random
import time

import lib


TEMP = 2.0
PATIENCE = 2500
SLICE = 4.0
TIME_FRACTION = 0.75


def trivial(d, D):
    """Always-valid small graph for any other (d, D) the evaluator may ask for."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


def _group(N, k, lam):
    """Semidirect group Z_(N/k) x| Z_k of order N. Returns (order, multiplication table, inverse list)."""
    order, mul, inv = lib.semidirect_group(N // k, k, lam)
    MT = [[mul(x, y) for y in range(order)] for x in range(order)]
    invl = [inv(x) for x in range(order)]
    return order, MT, invl


def _candidates(lo, hi, cap):
    """Non-abelian metacyclic (N, k, lam) with lo <= N <= hi, at most one lam per (N, k)."""
    out = []
    for N in range(lo, hi + 1):
        for k in range(2, N):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            for lam in range(2, m):
                if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1 % m:
                    out.append((N, k, lam))
                    break
    return out[:cap]


def _flat(volt):
    """Flatten the voltage blocks to darts (i, j, g)."""
    return [(i, j, g) for i in range(2) for j in range(2) for g in volt[i][j]]


def _lift_cost(N, MT, darts):
    """Number of (representative, vertex) pairs at distance > 5. Zero iff the lift has diameter <= 5."""
    tot = 4 * N
    adj = [[] for _ in range(tot)]
    for i, j, g in darts:
        jb = (2 + j) * N
        for x in range(N):
            a = i * N + x
            b = jb + MT[x][g]
            adj[a].append(b)
            adj[b].append(a)
    cost = 0
    for r in (0, N, 2 * N, 3 * N):
        seen = bytearray(tot)
        seen[r] = 1
        frontier = [r]
        cnt = 1
        for _ in range(5):
            nxt = []
            for u in frontier:
                for w in adj[u]:
                    if not seen[w]:
                        seen[w] = 1
                        nxt.append(w)
            if not nxt:
                break
            cnt += len(nxt)
            frontier = nxt
        cost += tot - cnt
    return cost


def _lift_graph(N, MT, volt):
    """Edge list of the lift for the given voltages (vertex (b, x) is b*N + x)."""
    edges = set()
    for i, j, g in _flat(volt):
        for x in range(N):
            edges.add((i * N + x, (2 + j) * N + MT[x][g]))
    return 4 * N, sorted(edges)


def _anneal(N, MT, rng, deadline):
    """Random restarts of annealing over voltages. Returns voltage blocks with cost 0, or None."""
    while time.monotonic() < deadline:
        a = rng.randint(1, 5)
        c = [[a, 6 - a], [6 - a, a]]
        volt = [[rng.sample(range(N), c[i][j]) for j in range(2)] for i in range(2)]
        cur = _lift_cost(N, MT, _flat(volt))
        best_local = cur
        since = 0
        while cur > 0 and since < PATIENCE and time.monotonic() < deadline:
            i = rng.randrange(2)
            j = rng.randrange(2)
            vs = volt[i][j]
            idx = rng.randrange(len(vs))
            old = vs[idx]
            used = set(vs)
            g = rng.randrange(N)
            while g in used:
                g = rng.randrange(N)
            vs[idx] = g
            nc = _lift_cost(N, MT, _flat(volt))
            delta = nc - cur
            if delta <= 0 or rng.random() < math.exp(-delta / TEMP):
                cur = nc
            else:
                vs[idx] = old
            if cur < best_local:
                best_local = cur
                since = 0
            else:
                since += 1
        if cur == 0:
            return volt
    return None


def _haar660():
    """Verified 660-vertex Haar graph (group order 330), used as the safe fallback."""
    try:
        N = 330
        _, MT, invl = _group(N, 10, 26)
        S = [0, 179, 116, 180, 47, 306]
        Sp = [invl[s] for s in S]
        edges = sorted({(x, N + MT[x][s]) for x in range(N) for s in Sp})
        n = 2 * N
        return (n, edges) if lib.is_valid(n, edges, 6, 5) else None
    except Exception:
        return None


def _search(seed, time_limit):
    t0 = time.monotonic()
    deadline = t0 + TIME_FRACTION * time_limit
    rng = random.Random(seed)

    best, bestn = None, 0
    fb = _haar660()
    if fb is not None:
        best, bestn = fb, fb[0]

    cands = _candidates(172, 200, 12)
    if not cands:
        return best if best is not None else trivial(6, 5)

    groups = {}
    turn = 0
    while time.monotonic() < deadline:
        if all(4 * c[0] <= bestn for c in cands):
            break
        N, k, lam = cands[turn % len(cands)]
        turn += 1
        if 4 * N <= bestn:
            continue
        key = (N, k, lam)
        if key not in groups:
            groups[key] = _group(N, k, lam)
        _, MT, _ = groups[key]
        slice_end = min(deadline, time.monotonic() + SLICE)
        volt = _anneal(N, MT, rng, slice_end)
        if volt is not None:
            n, edges = _lift_graph(N, MT, volt)
            if n > bestn and lib.is_valid(n, edges, 6, 5):
                best, bestn = (n, edges), n

    return best if best is not None else trivial(6, 5)


def build(d, D, seed, time_limit):
    if (d, D) != (6, 5):
        return trivial(d, D)
    try:
        return _search(seed, time_limit)
    except Exception:
        return trivial(d, D)
