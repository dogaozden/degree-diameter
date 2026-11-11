"""Degree-6, diameter-5 target: voltage lifts of small bipartite base graphs over non-abelian groups.

Base graph: K_{p,p} where every pair is joined by r parallel darts, with p*r = 6, so every base vertex has degree 6.
A voltage lift over a group G of order m has 2*p*m vertices. Dart (i, j, t) with voltage g joins A-vertex (i, x)
to B-vertex (j, x*g) for every x in G. The lift is bipartite with max degree 6.

Left multiplication by any h in G is an automorphism, so dist((u,x),(v,y)) = dist((u,e),(v,x^-1 y)). The diameter
is therefore at most 5 iff, for each of the 2p base vertices, the BFS from its identity sheet reaches every vertex
within 5 steps. cost(VOL) = total number of vertices missed by those 2p searches (0 means valid).

Search: every candidate (base shape, group), sorted by vertex count and starting just above the record of 684, gets a
resumable simulated annealing state. Candidates are then run in successive-halving rounds: each round gives every
live candidate a time slice, then keeps the half with the lowest best cost, with the slice doubling each round. This
concentrates time on near-miss candidates instead of spreading a fixed share over all of them. Every returned graph
is checked with lib.is_valid. If nothing beats the record, the Haar fallback (660 vertices) is returned, and a tiny
always-valid graph backs that up.
"""
import math
import time

import numpy as np

import lib

TARGET = (6, 5)
RECORD = 684
TEMP = 1.0          # annealing temperature in units of uncovered vertices
PATIENCE = 2000     # steps without local improvement before a restart

FALLBACK_SPEC = (33, 10, 26)            # semidirect Z_33 x| Z_10, order 330
FALLBACK_S = [0, 179, 116, 180, 47, 306]


# ----------------------------------------------------------------------------- groups

def group_table(order, mul):
    """Multiplication table MT[x, y] = mul(x, y) (identity must be index 0) and the inverse array."""
    MT = np.empty((order, order), dtype=np.int64)
    for x in range(order):
        MT[x] = [mul(x, y) for y in range(order)]
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
    return MT, inv


def heis_mul(p):
    """Heisenberg group mod p, element (a, b, c) coded as a*p^2 + b*p + c, (a,b,c)(a',b',c') = (a+a', b+b', c+c'+a*b')."""
    q2 = p * p

    def mul(x, y):
        a1, rest1 = divmod(x, q2)
        b1, c1 = divmod(rest1, p)
        a2, rest2 = divmod(y, q2)
        b2, c2 = divmod(rest2, p)
        return ((a1 + a2) % p) * q2 + ((b1 + b2) % p) * p + (c1 + c2 + a1 * b2) % p
    return mul


def make_group(spec):
    """Build (MT, inv) for a group spec."""
    if spec[0] == 'sd':
        _, a, b, s = spec
        order, mul, _ = lib.semidirect_group(a, b, s)
        return group_table(order, mul)
    if spec[0] == 'heis':
        p = spec[1]
        return group_table(p ** 3, heis_mul(p))
    G = spec[1]
    return group_table(G, lambda x, y: (x + y) % G)


def specs_of_order(G):
    """Candidate groups of order G: a few non-abelian metacyclic ones, Heisenberg if applicable, then cyclic."""
    sd = []
    for b in range(2, G):
        if G % b:
            continue
        a = G // b
        if a < 3:
            continue
        for s in range(2, a):
            if math.gcd(s, a) == 1 and pow(s, b, a) == 1:
                sd.append(('sd', a, b, s))
    picked = sd[::max(1, len(sd) // 3)][:4]
    p = round(G ** (1.0 / 3.0))
    if p >= 2 and p ** 3 == G and lib.is_prime_power(p):
        picked.append(('heis', p))
    picked.append(('cyc', G))
    return picked


# ----------------------------------------------------------------------------- lifts

def lift_nb(MT, inv, p, r, VOL):
    """Neighbour table: row v lists the neighbours of vertex v (A-vertex i*m+x, B-vertex (p+j)*m+x)."""
    m = MT.shape[0]
    nb = np.empty((2 * p * m, p * r), dtype=np.int64)
    for i in range(p):
        cols = [(p + j) * m + MT[:, VOL[i, j, t]] for j in range(p) for t in range(r)]
        nb[i * m:(i + 1) * m] = np.stack(cols, axis=1)
    for j in range(p):
        cols = [i * m + MT[:, inv[VOL[i, j, t]]] for i in range(p) for t in range(r)]
        nb[(p + j) * m:(p + j + 1) * m] = np.stack(cols, axis=1)
    return nb


def lift_cost(nb, m, p):
    """Number of (source, vertex) pairs at distance > 5 over the 2p identity sheets. 0 means diameter <= 5."""
    n = nb.shape[0]
    total = 0
    for u in range(2 * p):
        src = u * m
        seen = np.zeros(n, dtype=bool)
        seen[src] = True
        front = np.array([src], dtype=np.int64)
        for _ in range(5):
            nxt = nb[front].ravel()
            nxt = np.unique(nxt[~seen[nxt]])
            if nxt.size == 0:
                break
            seen[nxt] = True
            front = nxt
        total += n - int(seen.sum())
    return total


def lift_graph(nb, p, m):
    """Edge list of the lift (A-rows determine all edges)."""
    n = 2 * p * m
    edges = set()
    for a in range(p * m):
        for b in nb[a].tolist():
            edges.add((a, b))
    return n, sorted(edges)


class Anneal:
    """Resumable annealing state for one (base shape, group) candidate."""

    def __init__(self, MT, inv, p, r, rng):
        self.MT, self.inv, self.p, self.r, self.rng = MT, inv, p, r, rng
        self.m = MT.shape[0]
        self.n = 2 * p * self.m
        self.dead = False
        self.best_cost = float('inf')
        self._fresh()

    def _cost(self, VOL):
        return lift_cost(lift_nb(self.MT, self.inv, self.p, self.r, VOL), self.m, self.p)

    def _fresh(self):
        self.VOL = self.rng.integers(0, self.m, size=(self.p, self.p, self.r))
        self.cur = self._cost(self.VOL)
        self.local_best = self.cur
        self.since = 0
        self.best_cost = min(self.best_cost, self.cur)

    def run(self, deadline):
        """Anneal until cost 0 (return True) or the deadline (return False). Resumes where it left off."""
        p, r, m = self.p, self.r, self.m
        while self.cur > 0 and time.monotonic() < deadline:
            i, j, t = int(self.rng.integers(p)), int(self.rng.integers(p)), int(self.rng.integers(r))
            old = int(self.VOL[i, j, t])
            new = int(self.rng.integers(m))
            if new == old:
                continue
            self.VOL[i, j, t] = new
            c = self._cost(self.VOL)
            if c <= self.cur or self.rng.random() < math.exp(-(c - self.cur) / TEMP):
                self.cur = c
                self.best_cost = min(self.best_cost, c)
                if c < self.local_best:
                    self.local_best = c
                    self.since = 0
                else:
                    self.since += 1
            else:
                self.VOL[i, j, t] = old
                self.since += 1
            if self.since > PATIENCE:
                self._fresh()
        return self.cur == 0


# ----------------------------------------------------------------------------- fallbacks

def haar(MT, S):
    """Haar graph: A-vertex g ~ B-vertex s*g for s in S; returns (2N, edges)."""
    N = MT.shape[0]
    S = sorted(set(int(s) for s in S))
    edges = [(g, N + int(MT[s, g])) for s in S for g in range(N)]
    return 2 * N, edges


def safe_small(d, D):
    """Small graph that is valid for (d, D), chosen among a few simple constructions."""
    cands = []
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        cands.append(lib.projective_plane_incidence(d - 1))
    if D >= 2 and d >= 1:
        cands.append((2 * d, [(i, d + j) for i in range(d) for j in range(d)]))
    if D >= 1 and d >= 1:
        cands.append((2, [(0, 1)]))
    cands.append((1, []))
    for n, edges in cands:
        try:
            if lib.is_valid(n, edges, d, D):
                return n, edges
        except Exception:
            pass
    return 1, []


# ----------------------------------------------------------------------------- entry point

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return safe_small(d, D)

    t0 = time.monotonic()
    budget = max(0.5, min(0.75 * time_limit, time_limit - 10.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)

    # Candidates: (p, r, group spec), with 2*p*|G| just above the record, smallest first.
    jobs = []
    for p, r in ((6, 1), (3, 2), (2, 3), (1, 6)):
        g_lo = RECORD // (2 * p) + 1          # 2*p*G > RECORD
        for G in range(g_lo, g_lo + 3):
            for spec in specs_of_order(G):
                jobs.append((2 * p * G, p, r, spec))
    jobs.sort(key=lambda x: x[0])

    cache = {}
    searches = []
    for n_target, p, r, spec in jobs:
        if time.monotonic() >= deadline:
            break
        try:
            if spec not in cache:
                cache[spec] = make_group(spec)
            MT, inv = cache[spec]
            searches.append(Anneal(MT, inv, p, r, rng))
        except Exception:
            continue

    best = None
    alive = searches
    slice_t = 0.2
    while alive and time.monotonic() < deadline:
        for s in alive:
            now = time.monotonic()
            if now >= deadline:
                break
            if s.dead or (best is not None and s.n <= best[0]):
                continue
            if s.run(min(deadline, now + slice_t)):
                try:
                    nb = lift_nb(s.MT, s.inv, s.p, s.r, s.VOL)
                    n, edges = lift_graph(nb, s.p, s.m)
                    if lib.is_valid(n, edges, d, D):
                        if best is None or n > best[0]:
                            best = (n, edges)
                    else:
                        s.dead = True
                except Exception:
                    s.dead = True
        # Successive halving: keep the most promising half, favouring low cost and small n.
        alive = [s for s in alive if not s.dead and (best is None or s.n > best[0])]
        alive.sort(key=lambda s: (s.best_cost, s.n))
        alive = alive[:max(1, len(alive) // 2)]
        slice_t *= 2

    if best is not None:
        return best

    try:
        MT, inv = group_table(*lib.semidirect_group(*FALLBACK_SPEC)[:2])
        n, edges = haar(MT, FALLBACK_S)
        if lib.is_valid(n, edges, d, D):
            return n, edges
    except Exception:
        pass
    return safe_small(d, D)
