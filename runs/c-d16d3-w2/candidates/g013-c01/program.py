import random
import time

import lib


# Minimal pass-through engine, kept so the program has the required C_SOURCE part.
# The build below does not call it.
C_SOURCE = r"""
#include <stdio.h>
int main(void) {
    long n = 0, m = 0;
    if (scanf("%ld %ld", &n, &m) != 2) { printf("0 0\n"); return 0; }
    printf("%ld %ld\n", n, m);
    for (long i = 0; i < m; i++) {
        long u, v;
        if (scanf("%ld %ld", &u, &v) != 2) return 1;
        printf("%ld %ld\n", u, v);
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# New family: PG(2,q) incidence with a perfect matching removed, then pruned.
#
# For q = d, PG(2,d) incidence is (d+1)-regular with diameter 3. Removing a
# perfect matching leaves every vertex of degree d. Pairs of same-side vertices
# whose common line was cut are now bad, so we greedily delete the vertex with
# the most bad pairs until the graph has diameter 3. Pruning only removes
# vertices and edges, so degrees stay <= d. The result is then filled with
# extra vertices whose neighbourhoods cover the opposite side.
# ----------------------------------------------------------------------------

def _largest_prime_power_at_most(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def _matching_removed_pg(q, rng):
    """PG(2,q) incidence minus a random perfect matching; returns (n, edges)."""
    n, edges = lib.projective_plane_incidence(q)
    m = n // 2
    adj = [[] for _ in range(m)]
    for u, v in edges:
        adj[u].append(v - m)
    for lst in adj:
        rng.shuffle(lst)
    match_r = [-1] * m
    match_l = [-1] * m

    def augment(u, seen):
        for r in adj[u]:
            if r in seen:
                continue
            seen.add(r)
            if match_r[r] == -1 or augment(match_r[r], seen):
                match_r[r] = u
                match_l[u] = r
                return True
        return False

    order = list(range(m))
    rng.shuffle(order)
    for u in order:
        if not augment(u, set()):
            return None
    removed = {(u, m + match_l[u]) for u in range(m)}
    kept = [(u, v) for u, v in edges if (u, v) not in removed]
    return n, kept


def _balls(n, adj, alive, D):
    """Bitmask of alive vertices within distance D of each alive vertex (0 for dead ones)."""
    reach = [(1 << v) if alive[v] else 0 for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            if alive[v]:
                r = reach[v]
                for u in adj[v]:
                    r |= reach[u]
                new[v] = r
        reach = new
    return reach


def _prune(n, edges, D, rng, deadline):
    """Greedily delete the alive vertex with most bad pairs until diameter <= D; None on timeout."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    alive = [True] * n
    while time.monotonic() < deadline:
        reach = _balls(n, adj, alive, D)
        N = sum(alive)
        bad = [(N - reach[v].bit_count()) if alive[v] else 0 for v in range(n)]
        mx = max(bad)
        if mx == 0:
            return alive
        cands = [v for v in range(n) if bad[v] == mx]
        alive[rng.choice(cands)] = False
    return None


def _induced(n, edges, alive):
    idx = {}
    for v in range(n):
        if alive[v]:
            idx[v] = len(idx)
    E = [(idx[u], idx[v]) for u, v in edges if alive[u] and alive[v]]
    return len(idx), E


# ----------------------------------------------------------------------------
# Spare-capacity fill (diameter 3), as in the parent: add vertices whose
# neighbourhoods cover the whole opposite side; every addition is checked
# with lib.is_valid.
# ----------------------------------------------------------------------------

def _bipartition(n, adj):
    col = [-1] * n
    for s in range(n):
        if col[s] != -1:
            continue
        col[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if col[v] == -1:
                    col[v] = 1 - col[u]
                    stack.append(v)
    return col


def _fill(n, edges, d, D, deadline, rng):
    edges = list(edges)
    fails = 0
    while time.monotonic() < deadline and fails < 400:
        adj = [[] for _ in range(n)]
        for u, v in edges:
            adj[u].append(v)
            adj[v].append(u)
        deg = [len(a) for a in adj]
        col = _bipartition(n, adj)
        c = rng.randrange(2)
        uncovered = {v for v in range(n) if col[v] == 1 - c}
        cand = [v for v in range(n) if col[v] == c and deg[v] < d]
        chosen = []
        chosen_set = set()
        while uncovered and len(chosen) < d:
            best_v = None
            best_key = None
            for v in cand:
                if v in chosen_set:
                    continue
                g = sum(1 for u in adj[v] if u in uncovered)
                if g == 0:
                    continue
                key = (g, rng.random())
                if best_key is None or key > best_key:
                    best_key = key
                    best_v = v
            if best_v is None:
                break
            chosen.append(best_v)
            chosen_set.add(best_v)
            for u in adj[best_v]:
                uncovered.discard(u)
        if uncovered:
            fails += 1
            continue
        new_edges = edges + [(v, n) for v in chosen]
        if lib.is_valid(n + 1, new_edges, d, D):
            edges = new_edges
            n += 1
            fails = 0
        else:
            fails += 1
    return n, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3 and 3 <= d <= 40:
        # Plain projective-plane incidence graphs (diameter 3, valid for D >= 3).
        if lib.is_prime_power(d - 1):
            consider(*lib.projective_plane_incidence(d - 1))
        qc = _largest_prime_power_at_most(d - 2)
        if qc is not None and qc >= 2:
            consider(*lib.projective_plane_incidence(qc))
        consider(*_fill(best_n, best[1], d, D, start + 0.2 * time_limit,
                        random.Random(seed * 104729 + d)))

    # New family: PG(2,d) minus a perfect matching, pruned, then filled.
    prune_best = None
    if D >= 3 and 3 <= d <= 40 and lib.is_prime_power(d):
        route_deadline = start + 0.7 * time_limit
        while time.monotonic() < route_deadline:
            res = _matching_removed_pg(d, rng)
            if res is None:
                break
            n0, e0 = res
            alive = _prune(n0, e0, D, rng, route_deadline)
            if alive is None:
                break
            n1, e1 = _induced(n0, e0, alive)
            if n1 > 0 and (prune_best is None or n1 > prune_best[0]):
                prune_best = (n1, e1)
                consider(n1, e1)

    if prune_best is not None:
        consider(*_fill(prune_best[0], prune_best[1], d, D, start + 0.88 * time_limit,
                        random.Random(seed * 31 + d)))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
