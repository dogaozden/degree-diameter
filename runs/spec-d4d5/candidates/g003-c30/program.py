import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bounded-degree bipartite graph search by simulated annealing over edge swaps.
#
# State: a bipartite graph with sides A (0..NA-1) and B (0..NB-1), every degree
# <= d. Cost = number of unordered pairs at distance > D. Moves are degree-
# preserving double-edge swaps, random edge deletions, and a "grow" step that
# adds one vertex per side by splicing new vertices into existing edges.
# Missing edges are filled greedily, since adding edges never increases distance.
# Only graphs with cost 0 are recorded, and each one is checked by lib.is_valid.
# ----------------------------------------------------------------------------


def _bad(n, adj, D):
    """Number of unordered vertex pairs at distance > D (bitset BFS, unreachable pairs included)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        if new == reach:
            break
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


class _State:
    def __init__(self, d, D, NA, NB, edges):
        self.d = d
        self.D = D
        self.NA = NA
        self.NB = NB
        self.adjA = [set() for _ in range(NA)]
        self.adjB = [set() for _ in range(NB)]
        self.E = []
        self.pos = {}
        self.log = []
        for a, b in edges:
            self._add_raw(a, b)

    def _add_raw(self, a, b):
        self.pos[(a, b)] = len(self.E)
        self.E.append((a, b))
        self.adjA[a].add(b)
        self.adjB[b].add(a)

    def _rem_raw(self, a, b):
        i = self.pos.pop((a, b))
        last = self.E.pop()
        if i < len(self.E):
            self.E[i] = last
            self.pos[last] = i
        self.adjA[a].discard(b)
        self.adjB[b].discard(a)

    def add(self, a, b):
        self._add_raw(a, b)
        self.log.append((0, a, b))

    def rem(self, a, b):
        self._rem_raw(a, b)
        self.log.append((1, a, b))

    def undo(self):
        for t, a, b in reversed(self.log):
            if t == 0:
                self._rem_raw(a, b)
            else:
                self._add_raw(a, b)
        self.log = []

    def fill(self, rng):
        """Greedily add edges between deficient vertices on opposite sides."""
        d = self.d
        defA = [a for a in range(self.NA) if len(self.adjA[a]) < d]
        defB = [b for b in range(self.NB) if len(self.adjB[b]) < d]
        rng.shuffle(defA)
        for a in defA:
            if len(self.adjA[a]) >= d:
                continue
            rng.shuffle(defB)
            for b in defB:
                if len(self.adjB[b]) < d and b not in self.adjA[a]:
                    self.add(a, b)
                    if len(self.adjA[a]) >= d:
                        break

    def cost(self):
        n = self.NA + self.NB
        adj = [[self.NA + b for b in s] for s in self.adjA]
        adj += [list(s) for s in self.adjB]
        return _bad(n, adj, self.D)

    def grow(self, rng):
        """Add one vertex per side; splice each new vertex into d existing edges."""
        a_new, b_new = self.NA, self.NB
        self.NA += 1
        self.NB += 1
        self.adjA.append(set())
        self.adjB.append(set())
        self.log = []
        made = 0
        tries = 0
        while made < self.d and self.E and tries < 50 * self.d:
            tries += 1
            a, b = self.E[rng.randrange(len(self.E))]
            if (a_new, b) in self.pos or (a, b_new) in self.pos:
                continue
            self._rem_raw(a, b)
            self._add_raw(a, b_new)
            self._add_raw(a_new, b)
            made += 1
        self.fill(rng)
        self.log = []


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.8 * time_limit - 2.0)
    rng = random.Random(seed)

    if d <= 0 or D <= 0:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    kn, ke = lib.haar_graph(d, range(d))
    if not lib.is_valid(kn, ke, d, D):
        return 1, []
    best_n, best_e = kn, ke

    # Starting structure: the projective-plane incidence graph (d-regular,
    # diameter 3) when d-1 is a prime power and D >= 3; otherwise K_{d,d}.
    NA = NB = d
    init = [(a, b) for a in range(d) for b in range(d)]
    if D >= 3 and lib.is_prime_power(d - 1):
        pn, pe = lib.projective_plane_incidence(d - 1)
        m = pn // 2
        if lib.is_valid(pn, pe, d, D) and pn > best_n:
            best_n, best_e = pn, pe
        NA = NB = m
        init = [(u, v - m) for u, v in pe]

    st = _State(d, D, NA, NB, init)

    while time.monotonic() < deadline:
        cur = st.cost()
        now = time.monotonic()
        stage_end = min(deadline, now + max(0.5, min(3.0, (deadline - now) / 10.0)))
        while cur > 0 and time.monotonic() < stage_end:
            st.log = []
            E = st.E
            r = rng.random()
            if r < 0.6 and len(E) >= 2:
                i = rng.randrange(len(E))
                j = rng.randrange(len(E))
                a1, b1 = E[i]
                a2, b2 = E[j]
                if a1 == a2 or b1 == b2 or (a1, b2) in st.pos or (a2, b1) in st.pos:
                    continue
                st.rem(a1, b1)
                st.rem(a2, b2)
                st.add(a1, b2)
                st.add(a2, b1)
            elif r < 0.85 and E:
                a, b = E[rng.randrange(len(E))]
                st.rem(a, b)
            elif len(E) >= 2:
                i = rng.randrange(len(E))
                a, b = E[i]
                st.rem(a, b)
                j = rng.randrange(len(E))
                a, b = E[j]
                st.rem(a, b)
            else:
                continue
            st.fill(rng)
            new = st.cost()
            delta = new - cur
            if delta <= 0 or rng.random() < math.exp(-delta / 0.4):
                cur = new
            else:
                st.undo()
        if cur > 0:
            break
        n = st.NA + st.NB
        if n > best_n:
            e = [(a, st.NA + b) for a, b in st.E]
            if lib.is_valid(n, e, d, D):
                best_n, best_e = n, e
        if time.monotonic() >= deadline:
            break
        st.grow(rng)

    if not lib.is_valid(best_n, best_e, d, D):
        return kn, ke
    return best_n, best_e
