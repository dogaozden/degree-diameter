import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base constructions: projective plane and the Araujo-Pardo & Lopez graph.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo & Lopez record graph for degree d when q = d-2 is a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


def _bipartition(n, adj):
    """Two-colouring of a bipartite graph given by adjacency lists."""
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
# Bi-Cayley voltage lifts over semidirect products Z_m x| Z_k (annealed).
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    for _ in range(80):
        k2 = rng.choice([1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 60))
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _right_perm(mul, G, s):
    return [mul(g, s) for g in range(G)]


def _cost(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs not reached within distance D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        base_a = i * G
        base_b = (k + j) * G
        for g in range(G):
            a = base_a + g
            b = base_b + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen = [False] * N
        seen[src] = True
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = True
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer B-assignments."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    T0 = max(1.0, 0.05 * cost) if cost < _BIG else 1.0
    T_end = 0.5
    decay = (T_end / T0) ** (1.0 / max(1, iters)) if T0 > T_end else 1.0
    T = T0

    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(T_end, T * decay)

        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _right_perm(mul, G, new_s)
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_perm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# NEW: incremental growth by vertex-pair splitting, then 2-switch annealing.
#
# _insert_pair adds one vertex x on side A and one vertex y on side B without
# changing any old degree: it picks up to d edges (a_i, b_i) with distinct a_i
# and distinct b_i, and rewires each into (x, b_i) and (a_i, y). The new pair is
# then fixed by degree-preserving 2-switches (a1,b1),(a2,b2) -> (a1,b2),(a2,b1),
# minimising the number of ordered vertex pairs at distance > D, computed with
# bitset ball expansion.
# ----------------------------------------------------------------------------

def _bitcost(n, adj, D):
    """Number of ordered vertex pairs at distance > D (zero iff diameter <= D and connected)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach)


def _insert_pair(n, adj, color, d, rng):
    """Degree-preserving insertion of one A-vertex and one B-vertex. Returns the new vertex count."""
    edges_list = [(a, b) for a in range(n) if color[a] == 0 for b in adj[a]]
    rng.shuffle(edges_list)
    used_a, used_b, chosen = set(), set(), []
    for a, b in edges_list:
        if len(chosen) >= d:
            break
        if a in used_a or b in used_b:
            continue
        used_a.add(a)
        used_b.add(b)
        chosen.append((a, b))
    x, y = n, n + 1
    adj.append([])
    adj.append([])
    color.append(0)
    color.append(1)
    for a, b in chosen:
        adj[a].remove(b)
        adj[b].remove(a)
        adj[x].append(b)
        adj[b].append(x)
        adj[y].append(a)
        adj[a].append(y)
    return n + 2


def _saturate(n, adj, color, d, rng):
    """Add edges between deficient opposite-side non-adjacent vertices, in random order."""
    left = [v for v in range(n) if color[v] == 0 and len(adj[v]) < d]
    right = [v for v in range(n) if color[v] == 1 and len(adj[v]) < d]
    nbr = [set(a) for a in adj]
    pairs = [(a, b) for a in left for b in right if b not in nbr[a]]
    rng.shuffle(pairs)
    for a, b in pairs:
        if len(adj[a]) < d and len(adj[b]) < d:
            adj[a].append(b)
            adj[b].append(a)


def _switch_anneal(n, adj, color, d, D, rng, deadline):
    """Anneal degree-preserving 2-switches until the diameter is <= D. Returns True on success."""
    eset = set()
    E = []
    for a in range(n):
        if color[a] == 0:
            for b in adj[a]:
                E.append((a, b))
                eset.add((a, b))
    if not E:
        return False
    cost = _bitcost(n, adj, D)
    if cost == 0:
        return True

    start = time.monotonic()
    total = max(1e-3, deadline - start)
    T0, T1 = 3.0, 0.2
    T = T0
    it = 0
    while cost > 0:
        if (it & 15) == 0:
            now = time.monotonic()
            if now >= deadline:
                break
            T = T0 * (T1 / T0) ** min(1.0, (now - start) / total)
        it += 1
        i = rng.randrange(len(E))
        j = rng.randrange(len(E))
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        n1, n2 = (a1, b2), (a2, b1)
        if n1 in eset or n2 in eset:
            continue
        adj[a1].remove(b1)
        adj[b1].remove(a1)
        adj[a2].remove(b2)
        adj[b2].remove(a2)
        adj[a1].append(b2)
        adj[b2].append(a1)
        adj[a2].append(b1)
        adj[b1].append(a2)
        c2 = _bitcost(n, adj, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
            eset.discard((a1, b1))
            eset.discard((a2, b2))
            eset.add(n1)
            eset.add(n2)
            E[i] = n1
            E[j] = n2
        else:
            adj[a1].remove(b2)
            adj[b2].remove(a1)
            adj[a2].remove(b1)
            adj[b1].remove(a2)
            adj[a1].append(b1)
            adj[b1].append(a1)
            adj[a2].append(b2)
            adj[b2].append(a2)
    return cost == 0


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    moore = lib.moore_bound(d, D)

    try:
        if D >= 3:
            ap = _araujo(d)
            if ap is not None:
                consider(ap[0], ap[1])
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])

        # Calibration-type cases already at the Moore bound: return immediately.
        if best_n < moore and D >= 3:
            # Phase 1: annealed group voltage lifts.
            group_deadline = start + 0.45 * time_limit
            if D >= 5:
                ks = [1, 1, 2, 2, 3, 4]
                anneal_iters = 1500
            else:
                ks = [1, 1, 2, 3]
                anneal_iters = 400
            while time.monotonic() < group_deadline and best_n < moore:
                k = rng.choice(ks)
                base = best_n // (2 * k)
                if D >= 5:
                    G = max(2, base + 1 + rng.randrange(0, 3))
                else:
                    G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
                g = _sample_group(G, rng)
                if g is None:
                    continue
                order, mul = g
                res = _anneal(d, D, k, order, mul, rng, group_deadline, iters=anneal_iters)
                if res is not None:
                    consider(res[0], res[1])

            # Phase 2: grow the best graph by vertex-pair insertion + 2-switch annealing.
            if best_n < moore:
                cur_n = best_n
                adjbase = [[] for _ in range(cur_n)]
                for u, v in best[1]:
                    adjbase[u].append(v)
                    adjbase[v].append(u)
                colbase = _bipartition(cur_n, adjbase)
                while time.monotonic() < deadline and cur_n < moore:
                    adj2 = [list(a) for a in adjbase]
                    col2 = list(colbase)
                    n2 = _insert_pair(cur_n, adj2, col2, d, rng)
                    _saturate(n2, adj2, col2, d, rng)
                    step_dl = min(deadline, time.monotonic() + 8.0)
                    if _switch_anneal(n2, adj2, col2, d, D, rng, step_dl):
                        e2 = [(a, b) for a in range(n2) if col2[a] == 0 for b in adj2[a]]
                        consider(n2, e2)
                        if n2 > cur_n:
                            cur_n = n2
                            adjbase = adj2
                            colbase = col2
    except Exception:
        pass

    try:
        valid = lib.is_valid(best[0], best[1], d, D)
    except Exception:
        valid = False
    if not valid:
        best = lib.haar_graph(d, range(d))
    return best
