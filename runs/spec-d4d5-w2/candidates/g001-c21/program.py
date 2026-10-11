import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Time fractions (of time_limit). The lift phase ends at FRAC_LIFT; the
# remaining time goes to the new repair annealer, which must finish by
# FRAC_TOTAL.
# ----------------------------------------------------------------------------
FRAC_LIFT = 0.30
FRAC_TOTAL = 0.85
_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Algebraic base (diameter 3): PG(2, q) incidence graph, q the largest prime
# power <= d - 1. It is Moore-optimal when d - 1 is a prime power.
# ----------------------------------------------------------------------------

def _best_pg(d):
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Group voltage lifts over Z_m x| Z_k2 (seed phase).
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    for _ in range(80):
        k2 = rng.choice([1, 1, 2, 3, 4, 5, 6, 8])
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


def _lift_cost(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs at distance > D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            a = i * G + g
            b = (k + j) * G + pm[g]
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


def _anneal_lift(d, D, k, G, mul, rng, deadline, iters):
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [[mul(g, s) for g in range(G)] for _, _, s in darts]
    cost = _lift_cost(k, G, D, darts, perms)
    T0 = max(1.0, 0.05 * cost) if cost < _BIG else 1.0
    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = T0 * (0.5 / T0) ** (it / iters)
        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_p = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = [mul(g, new_s) for g in range(G)]
            c2 = _lift_cost(k, G, D, darts, perms)
            if c2 - cost <= 0 or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_p
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _lift_cost(k, G, D, darts, perms)
            if c2 - cost <= 0 or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
    if cost != 0:
        return None
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


# ----------------------------------------------------------------------------
# NEW: bipartite degree-preserving repair annealer with growth.
#
# State: bipartite graph with sides A (size hA) and B (size hB) and max degree d.
# Moves:
#   swap  : double-edge swap (a1,b1),(a2,b2) -> (a1,b2),(a2,b1); keeps degrees.
#   shift : move one endpoint of an edge onto a deficient vertex (moves slack).
# Cost = number of vertex pairs at distance > D. Any accepted step that leaves
# a deficient pair of opposite sides not joined is immediately saturated with
# the new edge, which can only shrink distances.
# Growth: add one vertex to each side and "subdivide" d edges with distinct
# endpoints: (x,y) -> (a,y),(x,b). This keeps every old degree and gives the
# new pair degree d, so the annealer only has to repair the new pair.
# ----------------------------------------------------------------------------

def _bad_pairs(n, nb, D):
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in nb[v]:
                r |= reach[u]
            new.append(r)
        if new == reach:
            break
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


class _State:
    def __init__(self, hA, hB, E, d):
        self.hA = hA
        self.hB = hB
        self.d = d
        self.E = list(E)
        self.S = set(self.E)
        self.dA = [0] * hA
        self.dB = [0] * hB
        for a, b in self.E:
            self.dA[a] += 1
            self.dB[b] += 1

    def n(self):
        return self.hA + self.hB

    def nbr(self):
        h = self.hA
        nb = [[] for _ in range(h + self.hB)]
        for a, b in self.E:
            nb[a].append(h + b)
            nb[h + b].append(a)
        return nb

    def cost(self, D):
        return _bad_pairs(self.n(), self.nbr(), D)

    def edges_out(self):
        h = self.hA
        return self.n(), [(a, h + b) for a, b in self.E]

    def _replace(self, i, new):
        old = self.E[i]
        a0, b0 = old
        a1, b1 = new
        self.S.discard(old)
        self.S.add(new)
        self.dA[a0] -= 1
        self.dB[b0] -= 1
        self.dA[a1] += 1
        self.dB[b1] += 1
        self.E[i] = new
        return old

    def _add(self, a, b):
        self.E.append((a, b))
        self.S.add((a, b))
        self.dA[a] += 1
        self.dB[b] += 1

    def undo(self, ops):
        for i, old in ops:
            self._replace(i, old)

    def saturate(self, rng):
        da = [a for a in range(self.hA) if self.dA[a] < self.d]
        db = [b for b in range(self.hB) if self.dB[b] < self.d]
        rng.shuffle(da)
        rng.shuffle(db)
        added = 0
        for a in da:
            for b in db:
                if self.dA[a] >= self.d:
                    break
                if self.dB[b] < self.d and (a, b) not in self.S:
                    self._add(a, b)
                    added += 1
        return added

    def swap_move(self, rng):
        m = len(self.E)
        if m < 2:
            return None
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            return None
        a1, b1 = self.E[i]
        a2, b2 = self.E[j]
        if a1 == a2 or b1 == b2:
            return None
        n1 = (a1, b2)
        n2 = (a2, b1)
        if n1 in self.S or n2 in self.S:
            return None
        o1 = self._replace(i, n1)
        o2 = self._replace(j, n2)
        return [(j, o2), (i, o1)]

    def shift_move(self, rng):
        if not self.E:
            return None
        i = rng.randrange(len(self.E))
        x, y = self.E[i]
        if rng.random() < 0.5:
            defs = [a for a in range(self.hA)
                    if self.dA[a] < self.d and a != x and (a, y) not in self.S]
            if not defs:
                return None
            new = (rng.choice(defs), y)
        else:
            defs = [b for b in range(self.hB)
                    if self.dB[b] < self.d and b != y and (x, b) not in self.S]
            if not defs:
                return None
            new = (x, rng.choice(defs))
        old = self._replace(i, new)
        return [(i, old)]


def _anneal_state(st, D, rng, deadline, iters, T0, T1):
    """Metropolis search at fixed size; returns st when cost reaches 0, else None."""
    cost = st.cost(D)
    for it in range(iters):
        if cost == 0:
            break
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        T = T0 * (T1 / T0) ** (it / iters)
        undo = st.shift_move(rng) if rng.random() < 0.25 else st.swap_move(rng)
        if not undo:
            continue
        c2 = st.cost(D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
            if st.saturate(rng):
                cost = st.cost(D)
        else:
            st.undo(undo)
    return st if cost == 0 else None


def _grow(st, rng):
    """Add one vertex per side; subdivide d edges with distinct endpoints."""
    d = st.d
    a = st.hA
    b = st.hB
    st.hA += 1
    st.hB += 1
    st.dA.append(0)
    st.dB.append(0)
    order = list(range(len(st.E)))
    rng.shuffle(order)
    used_x = set()
    used_y = set()
    count = 0
    for i in order:
        if count >= d:
            break
        x, y = st.E[i]
        if x in used_x or y in used_y:
            continue
        st._replace(i, (a, y))
        st._add(x, b)
        used_x.add(x)
        used_y.add(y)
        count += 1
    return st


def _bipartite_color(n, adj):
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
                elif color[v] == color[u]:
                    return None
    return color


def _state_from_graph(n, edges, d, color):
    idx = [0] * n
    hA = 0
    hB = 0
    for v in range(n):
        if color[v] == 0:
            idx[v] = hA
            hA += 1
        else:
            idx[v] = hB
            hB += 1
    E = []
    for u, v in edges:
        if color[u] == 0:
            E.append((idx[u], idx[v]))
        else:
            E.append((idx[v], idx[u]))
    return _State(hA, hB, E, d)


# ----------------------------------------------------------------------------
# Driver
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    lift_deadline = start + FRAC_LIFT * time_limit
    final = start + FRAC_TOTAL * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D
        return L, [(i, (i + 1) % L) for i in range(L)]

    fallback = lib.haar_graph(d, range(d))  # K_{d,d}, diameter 2
    if D == 2:
        return fallback

    moore = lib.moore_bound(d, D)
    best = fallback

    def consider(c):
        nonlocal best
        if c is None:
            return
        n, e = c
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        pg = _best_pg(d)
        consider(pg)
        if best[0] >= moore:
            return best

    # Seed phase: voltage lifts.
    try:
        if D >= 4:
            ks = [1, 1, 2, 2, 3, 4]
            while time.monotonic() < lift_deadline and best[0] < moore:
                k = rng.choice(ks)
                base = best[0] // (2 * k)
                G = max(2, base + 1 + rng.randrange(0, 3))
                g = _sample_group(G, rng)
                if g is None:
                    continue
                order, mul = g
                consider(_anneal_lift(d, D, k, order, mul, rng, lift_deadline, 1200))
    except Exception:
        pass

    # Main phase: grow the best graph by one vertex pair at a time, repairing
    # each enlarged graph with degree-preserving annealing.
    try:
        color = _bipartite_color(best[0], lib.adjacency(best[0], best[1]))
        if color is not None:
            st = _state_from_graph(best[0], best[1], d, color)
            st.saturate(rng)
            while time.monotonic() < final and best[0] < moore:
                _grow(st, rng)
                st.saturate(rng)
                ok = False
                while time.monotonic() < final:
                    res = _anneal_state(st, D, rng, final, 1500, 1.5, 0.2)
                    if res is not None:
                        ok = True
                        break
                if not ok:
                    break
                consider(st.edges_out())
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
