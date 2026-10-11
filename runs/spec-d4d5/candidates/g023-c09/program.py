import math
import random
import time

import lib

_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Bitmask cost: number of unordered vertex pairs at distance > D.
# ----------------------------------------------------------------------------

def _bad_pairs(n, adj, D):
    full = (1 << n) - 1
    ball = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
        if all(b == full for b in ball):
            return 0
    return sum(n - b.bit_count() for b in ball) // 2


# ----------------------------------------------------------------------------
# Family 1: annealed voltage lifts over Z_m x| Z_k (from the previous program).
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
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
# Family 2 (new): degree-bounded bipartite repair search with vertex growth.
# Maintains a bipartite graph with max degree d and anneals on the number of
# pairs at distance > D. Vertices are added in side pairs and the search
# repairs the graph until it is valid again.
# ----------------------------------------------------------------------------

class _Rep:
    def __init__(self, n, edges, color, d):
        self.n = n
        self.d = d
        self.color = list(color)
        self.adj = [set() for _ in range(n)]
        self.el = []
        self.pos = {}
        for u, v in edges:
            a, b = (u, v) if self.color[u] == 0 else (v, u)
            self._link(a, b)

    def _link(self, a, b):
        self.pos[(a, b)] = len(self.el)
        self.el.append((a, b))
        self.adj[a].add(b)
        self.adj[b].add(a)

    def _unlink(self, a, b):
        i = self.pos.pop((a, b))
        last = self.el.pop()
        if i < len(self.el):
            self.el[i] = last
            self.pos[last] = i
        self.adj[a].discard(b)
        self.adj[b].discard(a)

    def apply(self, ops):
        done = []
        for sign, a, b in ops:
            if sign == '+':
                ok = (a != b and b not in self.adj[a]
                      and len(self.adj[a]) < self.d and len(self.adj[b]) < self.d)
                if ok:
                    self._link(a, b)
            else:
                ok = (a, b) in self.pos
                if ok:
                    self._unlink(a, b)
            if not ok:
                self.undo(done)
                return None
            done.append((sign, a, b))
        return done

    def undo(self, done):
        for sign, a, b in reversed(done):
            if sign == '+':
                self._unlink(a, b)
            else:
                self._link(a, b)

    def _deficient(self, side):
        return [v for v in range(self.n)
                if self.color[v] == side and len(self.adj[v]) < self.d]

    def propose(self, rng):
        t = rng.random()
        el = self.el
        if t < 0.35:
            if len(el) < 2:
                return None
            a, b = el[rng.randrange(len(el))]
            c, e = el[rng.randrange(len(el))]
            if a == c or b == e:
                return None
            if e in self.adj[a] or b in self.adj[c]:
                return None
            return [('-', a, b), ('-', c, e), ('+', a, e), ('+', c, b)]
        if t < 0.6:
            A = self._deficient(0)
            B = self._deficient(1)
            if not A or not B:
                return None
            a = rng.choice(A)
            b = rng.choice(B)
            if b in self.adj[a]:
                return None
            return [('+', a, b)]
        if not el:
            return None
        a, b = el[rng.randrange(len(el))]
        if t < 0.7:
            return [('-', a, b)]
        if rng.random() < 0.5:
            A = self._deficient(0)
            if not A:
                return None
            x = rng.choice(A)
            if x == a or x in self.adj[b]:
                return None
            return [('-', a, b), ('+', x, b)]
        B = self._deficient(1)
        if not B:
            return None
        y = rng.choice(B)
        if y == b or y in self.adj[a]:
            return None
        return [('-', a, b), ('+', a, y)]


def _repair(rep, D, rng, deadline, iters):
    cost = _bad_pairs(rep.n, rep.adj, D)
    T0, T1 = 1.5, 0.15
    for it in range(iters):
        if cost == 0:
            break
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        T = T0 * (T1 / T0) ** (it / max(1, iters))
        ops = rep.propose(rng)
        if ops is None:
            continue
        done = rep.apply(ops)
        if done is None:
            continue
        c2 = _bad_pairs(rep.n, rep.adj, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            rep.undo(done)
    return cost


def _grow(n, edges, color, d, D, rng, deadline):
    """Repeatedly add one vertex on each side and repair until valid; return the last valid graph."""
    cur = (n, list(edges), list(color))
    while time.monotonic() < deadline:
        n0, e0, c0 = cur
        rep = _Rep(n0 + 2, e0, c0 + [0, 1], d)
        cost = _repair(rep, D, rng, deadline, 3000)
        if cost != 0:
            break
        cur = (n0 + 2, list(rep.el), list(rep.color))
    return cur


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for every D >= 2.
    fb_n, fb_e = lib.haar_graph(d, range(d))
    if D == 2:
        return fb_n, list(fb_e)

    # best = [n, edges, colour]
    best = [fb_n, list(fb_e), [0] * d + [1] * d]

    def consider(n, e, col):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best[:] = [n, list(e), list(col)]

    hard = start + max(1.0, min(0.85 * time_limit, time_limit - 5.0))

    # Projective plane incidence graph when d-1 is a prime power (optimal for D = 3).
    q = d - 1
    if D >= 3 and q >= 2 and lib.is_prime_power(q):
        n, e = lib.projective_plane_incidence(q)
        m = n // 2
        consider(n, e, [0] * m + [1] * m)
        if D == 3:
            return best[0], best[1]

    # Lift search gets the first part of the budget, repair growth the rest.
    span = max(0.0, hard - time.monotonic())
    lift_end = time.monotonic() + 0.6 * span
    ks = [1, 1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
    anneal_iters = 1500 if D >= 5 else 400
    while time.monotonic() < lift_end:
        k = rng.choice(ks)
        G = max(2, best[0] // (2 * k) + 1 + rng.randrange(0, 3))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        res = _anneal(d, D, k, order, mul, rng, lift_end, anneal_iters)
        if res is not None:
            n, e = res
            consider(n, e, [0] * (k * order) + [1] * (k * order))

    # Repair growth from the best valid graph found so far.
    if best[0] >= 4 and time.monotonic() < hard:
        n, e, col = _grow(best[0], best[1], best[2], d, D, rng, hard)
        consider(n, e, col)

    if not lib.is_valid(best[0], best[1], d, D):
        return fb_n, list(fb_e)
    return best[0], best[1]
