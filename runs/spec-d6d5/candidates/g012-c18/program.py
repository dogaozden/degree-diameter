import math
import random
import time

import lib

_BIG = 10 ** 9
_K2 = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]


# ----------------------------------------------------------------------------
# Baselines (always valid): projective plane incidence, Araujo-Pardo-Lopez.
# ----------------------------------------------------------------------------

def _pg_baseline(d):
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# Group sampling: semidirect products Z_m x| Z_k2 (k2 = 1 gives cyclic).
# ----------------------------------------------------------------------------

def _sample_group(G, rng, k2_choices):
    """Return (order, mul, inv) for a random semidirect product of order G, or None."""
    for _ in range(100):
        k2 = rng.choice(k2_choices)
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [x for x in range(1, m)
                     if math.gcd(x, m) == 1 and pow(x, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, inv = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul, inv
    return None


def _reach(adj, src, D, N):
    """Number of vertices within distance D of src (src included)."""
    seen = bytearray(N)
    seen[src] = 1
    frontier = [src]
    cnt = 1
    for _ in range(D):
        nxt = []
        for u in frontier:
            for v in adj[u]:
                if not seen[v]:
                    seen[v] = 1
                    nxt.append(v)
        if not nxt:
            break
        cnt += len(nxt)
        frontier = nxt
    return cnt


# ----------------------------------------------------------------------------
# NEW ARM: bipartite Cayley-type graphs over a group G.
# Vertices a_g = g and b_h = G + h. Edge a_g ~ b_{g s} for s in S (|S| = d).
# Left multiplication is an automorphism, so the diameter is <= D iff
# ecc(a_e) <= D and ecc(b_e) <= D. That needs only two BFS per candidate.
# ----------------------------------------------------------------------------

class _Cayley:
    def __init__(self, G, mul, inv):
        self.G = G
        self.mul = mul
        self.inv = inv
        self.cache = {}

    def perm(self, s):
        p = self.cache.get(s)
        if p is None:
            mul = self.mul
            p = [mul(g, s) for g in range(self.G)]
            self.cache[s] = p
        return p


def _cayley_cost(C, S, D):
    G = C.G
    N = 2 * G
    adj = [[] for _ in range(N)]
    for s in S:
        p = C.perm(s)
        q = C.perm(C.inv(s))
        for g in range(G):
            adj[g].append(G + p[g])
            adj[G + g].append(q[g])
    return (N - _reach(adj, 0, D, N)) + (N - _reach(adj, G, D, N))


def _cayley_search(d, D, C, rng, deadline, iters):
    G = C.G
    S = rng.sample(range(G), d)
    cost = _cayley_cost(C, S, D)
    T = 2.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(d)
        x = rng.randrange(G)
        if x in S:
            continue
        old = S[i]
        S[i] = x
        c2 = _cayley_cost(C, S, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
        else:
            S[i] = old
        T = max(0.2, T * 0.99)
    return list(S) if cost == 0 else None


def _cayley_graph(C, S):
    G = C.G
    E = []
    for s in S:
        p = C.perm(s)
        for g in range(G):
            E.append((g, G + p[g]))
    return 2 * G, E


def _cayley_arm(d, D, rng, deadline, best, consider):
    while time.monotonic() < deadline:
        lo = max(d + 1, best[0] // 2 + 1)
        G = lo + rng.randrange(0, 10)
        g = _sample_group(G, rng, _K2)
        if g is None:
            continue
        order, mul, inv = g
        C = _Cayley(order, mul, inv)
        S = _cayley_search(d, D, C, rng, deadline, 250)
        if S is not None:
            n, e = _cayley_graph(C, S)
            consider(n, e)


# ----------------------------------------------------------------------------
# Voltage lifts over a group with k base vertices per side (annealed).
# Vertices: A_{i,g} = i*G + g, B_{j,h} = (k+j)*G + h.
# Dart (i, j, s) joins A_{i,g} to B_{j, g*s}.
# ----------------------------------------------------------------------------

def _right_perm(mul, G, s):
    return [mul(g, s) for g in range(G)]


def _lift_cost(k, G, D, darts, perms):
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
    total = 0
    for src in [i * G for i in range(k)] + [(k + j) * G for j in range(k)]:
        total += N - _reach(adj, src, D, N)
    return total


def _random_darts(d, k, G, rng):
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    return darts


def _lift_anneal(d, D, k, G, mul, rng, deadline, iters):
    darts = _random_darts(d, k, G, rng)
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _lift_cost(k, G, D, darts, perms)
    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.997)
        if k == 1 or rng.random() < 0.7:
            idx = rng.randrange(len(darts))
            old_s, old_p = darts[idx][2], perms[idx]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            darts[idx][2] = new_s
            perms[idx] = _right_perm(mul, G, new_s)
            c2 = _lift_cost(k, G, D, darts, perms)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
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
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
    return darts, perms, cost


def _lift_edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _balls_radius(n, adj, r):
    ball = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return ball


def _compact(n, edges, keep):
    new = {}
    for v in range(n):
        if keep[v]:
            new[v] = len(new)
    return len(new), [(new[u], new[v]) for u, v in edges if keep[u] and keep[v]]


def _repair(n, edges, D, deadline, rng):
    """Delete far-off vertices in batches until diameter <= D. Returns (n, edges) or None."""
    cur_n, cur_e = n, list(edges)
    while time.monotonic() < deadline and cur_n > 0:
        adj = [[] for _ in range(cur_n)]
        for u, v in cur_e:
            adj[u].append(v)
            adj[v].append(u)
        ball = _balls_radius(cur_n, adj, D)
        bad = [cur_n - b.bit_count() for b in ball]
        if not any(bad):
            return cur_n, cur_e
        bad_v = sorted((v for v in range(cur_n) if bad[v] > 0), key=lambda v: -bad[v])
        batch = max(1, len(bad_v) // 12)
        dead = set(bad_v[:batch])
        keep = [v not in dead for v in range(cur_n)]
        cur_n, cur_e = _compact(cur_n, cur_e, keep)
    return None


def _lift_arm(d, D, rng, deadline, best, consider):
    ks = [1, 1, 1, 2, 2, 3]
    while time.monotonic() < deadline:
        k = rng.choice(ks)
        lo = max(2, best[0] // (2 * k) + 1)
        G = rng.randint(lo, lo + max(3, lo // 6))
        g = _sample_group(G, rng, _K2)
        if g is None:
            continue
        order, mul, _inv = g
        darts, perms, c = _lift_anneal(d, D, k, order, mul, rng, deadline,
                                       500 if k == 1 else 250)
        if c == 0:
            n, e = _lift_edges(k, order, darts, perms)
            consider(n, e)
        elif c <= 60 and rng.random() < 0.5 and time.monotonic() < deadline:
            n, e = _lift_edges(k, order, darts, perms)
            rep = _repair(n, e, D, min(deadline, time.monotonic() + 4.0), rng)
            if rep is not None:
                consider(rep[0], rep[1])


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, 0.8 * time_limit - 1.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    fb_n, fb_e = lib.haar_graph(d, range(d))
    best = [fb_n, fb_e]

    def consider(n, e):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best[0], best[1] = n, e

    if D >= 3:
        pg = _pg_baseline(d)
        if pg is not None:
            consider(pg[0], pg[1])
            # Moore-optimal for D = 3 when d - 1 is a prime power.
            if D == 3 and lib.is_prime_power(d - 1):
                return best[0], best[1]
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

        # Cayley-type search first, then voltage-lift search with the remaining time.
        mid = start + 0.5 * (deadline - start)
        _cayley_arm(d, D, rng, mid, best, consider)
        _lift_arm(d, D, rng, deadline, best, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = [fb_n, fb_e]
    return best[0], best[1]
