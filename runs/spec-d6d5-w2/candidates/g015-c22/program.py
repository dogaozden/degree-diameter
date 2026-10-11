"""Bi-regular voltage lifts searched by dense numpy annealing (untested in this session).

Family: bipartite lifts of a k+k base multigraph over a finite group G (cyclic,
semidirect Z_m x| Z_k2, or AGL(1,p)). Left multiplication is an automorphism, so
checking distances from one representative per base vertex decides the diameter.
Annealing runs on the dense adjacency matrix with batched matrix products, and
near-misses get vertex-deletion repair. Every output passes lib.is_valid, with
fallbacks to K_{d,d} and PG(2,q) incidence graphs.
"""
import math
import random
import time

import numpy as np

import lib


def _is_prime(p):
    if p < 2:
        return False
    i = 2
    while i * i <= p:
        if p % i == 0:
            return False
        i += 1
    return True


def _affine_mul(p):
    """Multiplication in AGL(1,p); element (u-1)*p + b encodes x -> u*x + b."""
    def mul(x, y):
        u, b = divmod(x, p)
        u += 1
        v, c = divmod(y, p)
        v += 1
        return (((u * v) % p) - 1) * p + (u * c + b) % p
    return mul


def _table(G, mul):
    M = np.empty((G, G), dtype=np.int64)
    for x in range(G):
        M[x, :] = [mul(x, y) for y in range(G)]
    return M


def _group_specs(G, rng):
    specs = []
    for p in range(3, 200):
        if p * (p - 1) == G and _is_prime(p):
            specs.append(("aff", p))
        if p * (p - 1) > G:
            break
    for k2 in range(1, 13):
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            specs.append(("sd", m, 1, 1))
            continue
        rs = [r for r in range(2, m)
              if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m and r != 1]
        if rs:
            specs.append(("sd", m, k2, rng.choice(rs)))
    return specs


def _mul_from_spec(spec):
    if spec[0] == "aff":
        p = spec[1]
        return p * (p - 1), _affine_mul(p)
    _, m, k2, r = spec
    order, mul, _ = lib.semidirect_group(m, k2, r)
    return order, mul


class _Lift:
    """Bipartite lift: A_i,g ~ B_j,g*s for darts (i, j, s); one dart per (layer, a)."""

    def __init__(self, d, D, k, G, M, rng):
        self.d, self.D, self.k, self.G = d, D, k, G
        self.N = 2 * k * G
        self.MT = np.ascontiguousarray(M.T)  # MT[s][g] = g*s
        self.ar = np.arange(G, dtype=np.int64)
        self.rng = rng
        self.A = np.zeros((self.N, self.N), dtype=np.float32)
        self.reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
        self.darts = []
        self.trip = set()
        for _ in range(d):
            p = list(range(k))
            rng.shuffle(p)
            for a in range(k):
                while True:
                    s = rng.randrange(G)
                    t = (a, p[a], s)
                    if t not in self.trip:
                        break
                self.trip.add(t)
                self.darts.append([a, p[a], s])
        for idx in range(len(self.darts)):
            self._edge(idx, 1.0)

    def _edge(self, idx, sign):
        i, j, s = self.darts[idx]
        a = i * self.G + self.ar
        b = (self.k + j) * self.G + self.MT[s]
        self.A[a, b] += sign
        self.A[b, a] += sign

    def cost(self):
        S = len(self.reps)
        reach = np.zeros((S, self.N), dtype=np.float32)
        reach[np.arange(S), self.reps] = 1.0
        for _ in range(self.D):
            new = np.maximum(reach, ((reach @ self.A) > 0).astype(np.float32))
            if np.array_equal(new, reach):
                break
            reach = new
        return int(round(S * self.N - float(reach.sum())))

    def _replace(self, changes):
        """Apply [(idx, (i, j, s)), ...]; return the list that undoes it."""
        old = []
        for idx, _ in changes:
            self._edge(idx, -1.0)
            t = tuple(self.darts[idx])
            self.trip.discard(t)
            old.append((idx, t))
        for idx, t in changes:
            self.darts[idx] = list(t)
            self.trip.add(t)
            self._edge(idx, 1.0)
        return old

    def random_move(self):
        rng = self.rng
        if self.k == 1 or rng.random() < 0.5:
            idx = rng.randrange(len(self.darts))
            i, j, s = self.darts[idx]
            s2 = rng.randrange(self.G)
            if s2 == s or (i, j, s2) in self.trip:
                return None
            return self._replace([(idx, (i, j, s2))])
        L = rng.randrange(self.d)
        a, b = rng.sample(range(self.k), 2)
        ia, ib = L * self.k + a, L * self.k + b
        ta = tuple(self.darts[ia])
        tb = tuple(self.darts[ib])
        n1 = (ta[0], tb[1], ta[2])
        n2 = (tb[0], ta[1], tb[2])
        if n1 in self.trip or n2 in self.trip:
            return None
        return self._replace([(ia, n1), (ib, n2)])

    def edges(self):
        E = []
        for i, j, s in self.darts:
            a = i * self.G + self.ar
            b = (self.k + j) * self.G + self.MT[s]
            E.extend(zip(a.tolist(), b.tolist()))
        return E


def _anneal(lift, deadline, rng):
    cur = lift.cost()
    T = 1.0
    steps = 0
    while cur > 0:
        steps += 1
        if (steps & 7) == 0 and time.monotonic() > deadline:
            break
        T = max(0.1, T * 0.9995)
        old = lift.random_move()
        if old is None:
            continue
        new = lift.cost()
        if new <= cur or rng.random() < math.exp((cur - new) / T):
            cur = new
        else:
            lift._replace(old)
    return cur


def _repair(A, D, deadline):
    """Delete the worst-reached vertices in batches until diameter <= D; return kept indices or None."""
    keep = np.arange(A.shape[0])
    while time.monotonic() < deadline and keep.size > 0:
        sub = A[np.ix_(keep, keep)]
        m = keep.size
        reach = np.eye(m, dtype=np.float32)
        for _ in range(D):
            reach = np.maximum(reach, ((reach @ sub) > 0).astype(np.float32))
        bad = m - reach.sum(axis=1)
        if bad.max() < 0.5:
            return keep
        order = np.argsort(-bad, kind="stable")
        nbad = int((bad > 0.5).sum())
        drop = max(1, nbad // 10)
        keep = keep[np.sort(order[drop:])]
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = 2, [(0, 1)]

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e
            return True
        return False

    try:
        # PG(2,q) incidence graph, q the largest prime power <= d-1 (diameter 3).
        if D >= 3:
            for q in range(min(d - 1, 30), 1, -1):
                if lib.is_prime_power(q):
                    n, e = lib.projective_plane_incidence(q)
                    consider(n, e)
                    break

        # Bi-regular voltage-lift search for D >= 4.
        if D >= 4 and d >= 3:
            moore = lib.moore_bound(d, D)
            tgt = max(best_n + 2, int(0.43 * moore))
            fails = 0
            rng = random.Random(seed * 1000003 + d * 131 + D)
            while time.monotonic() < deadline - 0.5:
                k = rng.choice((1, 2, 2, 3, 3, 4))
                G = -(-tgt // (2 * k)) + rng.randint(0, 3)
                if G < d + 1:
                    G = d + 1
                specs = _group_specs(G, rng)
                if not specs:
                    fails += 1
                    continue
                spec = rng.choice(specs)
                try:
                    order, mul = _mul_from_spec(spec)
                except Exception:
                    fails += 1
                    continue
                if order != G:
                    fails += 1
                    continue
                M = _table(G, mul)
                lift = _Lift(d, D, k, G, M, rng)
                budget = min(deadline, time.monotonic() + 4.0)
                cur = _anneal(lift, budget, rng)
                N = 2 * k * G
                if cur == 0:
                    consider(N, lift.edges())
                    tgt = max(best_n + 2, int(best_n * 1.03))
                    fails = 0
                    continue
                fails += 1
                # Near miss: repair by vertex deletion, then keep if it beats the best.
                if cur <= 3 * N and rng.random() < 0.3 and time.monotonic() < deadline:
                    keep = _repair(lift.A, D, min(deadline, time.monotonic() + 3.0))
                    if keep is not None and len(keep) > best_n:
                        sub = lift.A[np.ix_(keep, keep)]
                        u, v = np.nonzero(np.triu(sub, 1))
                        consider(len(keep), list(zip(u.tolist(), v.tolist())))
                if fails % 2 == 0:
                    tgt = max(best_n + 2, int(tgt * 0.99))
    except Exception:
        pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, best_e
