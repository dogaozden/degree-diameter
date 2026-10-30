r"""Checks for Section 5 of SYNTHETIC.tex (diameter 5: level structures of generalized quadrangles,
freed sets and hubs), against the coordinate versions of research/theorems/D5_QUADRANGLE.md.

W(q) is built from the symplectic form w(x,y) = x0y2 + x1y3 - x2y0 - x3y1 of D5_QUADRANGLE.md \S1.2
(q prime), Q(4,q) is its dual (points = lines of W(q)), and from then on only incidence is used, except
where the explicit sets of D5_QUADRANGLE.md are evaluated (the spread of Lemma 1.1, the partial ovoid
of Lemma 1.3, the duality of Lemma 1.4 for q = 2).

  1. W(q), Q(4,q) are GQs of order (q,q) (q = 2, 3, 5, 7).
  2. Theorem A (level structures): random tournaments, typings and bijections, q = 2, 3, r = 1, 2:
     (q+1+r)-regular, (2r+1) 2N elements, diameter 5.
  3. Theorem E: the two conditions (E2), (E3) against a brute-force two-copy distance check, on random
     friendly and non-friendly transitions with freed sets of several kinds, perturbed two-point local
     dualities, and transitions built to keep one condition and (usually) break the other (q = 2, 3).
  4. Theorem B: friendly transition with M = identity (q = 3, both quadrangles) and a transition given
     by a duality (q = 2): repaired iff the freed set is pairwise non-collinear.
  5. Theorem C / Proposition 6.4: two-point local dualities built by the recipe are repaired, and
     M(R) is non-concurrent (q = 3, 5); triads of points of Q(4,q) have 0 or 2 centres, of W(q) 1 or
     q+1 (q = 3 all triads, q = 5 a sample); a 3-point freed set of pairwise non-collinear points
     of Q(4,3) never satisfies (H3) (as Corollary 6.2 says).
  6. Proposition 7.1 (relaxed freed sets): on a friendly identity transition from a copy of the dual
     of Q(4,q) to a copy of Q(4,q), the pairs at distance > 5 are exactly the 4q per partner pair;
     with the hubs of Proposition 7.2 they are all within 4 (q = 3, 5).
  7. Lemma 9.1: the hub graphs (Y1) (PG(2,s) with pendants), (Y2) (W(s) with pendants), s = 2, 3.
  8. Propositions 8.1-8.3 (slot vectors) and the six family values of Corollaries 10.1-10.4
     (4,044, 6,090, 8,430, 11,552, 14,812, 20,598) from the slot bounds and Lemma 9.1.
  9. Assembly, Lemma 7.3: seven copies HHHDHHD over Q(4,5): the ovoid of Lemma 1.1 on the five
     H->D arcs, the 14-point set of Lemma 1.3 plus one partner meeting it at an ovoid point on the
     D->H arcs, two-point local dualities on the eleven other arcs, 2 + 2 hubs placed by Lemma 7.3:
     max degree 9, 2188 elements, diameter 5.
 10. Corollary 10.2 at full size: five copies HHDHD over Q(4,7), 22 + 22 hubs on a (Y1) hub graph:
     4,044 elements, max degree 10, diameter 5.

Run: python3 check_d5.py      (a few seconds)
"""
import itertools
import random
import sys

FAIL = []


def check(cond, msg):
    if not cond:
        FAIL.append(msg)
        print('FAIL:', msg)


# ------------------------------------------------------------------ geometry

def proj_points(q, n):
    pts = []
    for v in itertools.product(range(q), repeat=n):
        if any(v):
            i = next(i for i in range(n) if v[i])
            if v[i] == 1:
                pts.append(v)
    return pts


def normp(v, q):
    i = next(i for i in range(len(v)) if v[i] % q)
    c = pow(v[i], q - 2, q)
    return tuple((x * c) % q for x in v)


def wform(x, y, q):
    return (x[0] * y[2] + x[1] * y[3] - x[2] * y[0] - x[3] * y[1]) % q


class GQ:
    """points 0..np-1, lines 0..nl-1, lines_on[p], pts_on[L] (lists of ints)."""

    def __init__(self, npts, nlines, flags):
        self.np, self.nl = npts, nlines
        self.lines_on = [[] for _ in range(npts)]
        self.pts_on = [[] for _ in range(nlines)]
        for p, L in flags:
            self.lines_on[p].append(L)
            self.pts_on[L].append(p)
        self.lset = [set(x) for x in self.lines_on]
        self.pset = [set(x) for x in self.pts_on]

    def dual(self):
        return GQ(self.nl, self.np, [(L, p) for p in range(self.np) for L in self.lines_on[p]])

    def collinear(self, a, b):           # distinct points on a common line
        return a != b and bool(self.lset[a] & self.lset[b])

    def concurrent(self, A, B):
        return A != B and bool(self.pset[A] & self.pset[B])

    def coll_set(self, p):               # Gamma_2(p): points collinear with p
        s = set()
        for L in self.lines_on[p]:
            s |= self.pset[L]
        s.discard(p)
        return s

    def conc_set(self, L):
        s = set()
        for p in self.pts_on[L]:
            s |= self.lset[p]
        s.discard(L)
        return s


def W(q):
    pts = proj_points(q, 4)
    idx = {p: i for i, p in enumerate(pts)}
    lines = set()
    for u, v in itertools.combinations(pts, 2):
        if wform(u, v, q) == 0:
            L = frozenset({idx[u], idx[v]} | {idx[normp(tuple((a * x + y) % q for x, y in zip(u, v)), q)]
                                              for a in range(q)})
            lines.add(L)
    lines = sorted(lines, key=sorted)
    G = GQ(len(pts), len(lines), [(p, i) for i, L in enumerate(lines) for p in L])
    G.coords, G.idx, G.lines = pts, idx, lines
    G.lidx = {L: i for i, L in enumerate(lines)}
    return G


def is_gq(G, s, t):
    if any(len(G.pts_on[L]) != s + 1 for L in range(G.nl)) or any(len(G.lines_on[p]) != t + 1 for p in range(G.np)):
        return False
    for p in range(G.np):
        coll = G.coll_set(p) | {p}
        for L in range(G.nl):
            if L not in G.lset[p] and len(G.pset[L] & coll) != 1:
                return False
    return True


def line_through(G, a, b):
    """the line of W(q) through two points given by coordinates (indices)."""
    return G.lidx[next(L for L in G.lines if a in L and b in L)]


# ------------------------------------------------------------------ graphs and distances

class Graph:
    def __init__(self, n):
        self.n = n
        self.adj = [set() for _ in range(n)]

    def add(self, u, v):
        assert u != v
        self.adj[u].add(v)
        self.adj[v].add(u)

    def remove(self, u, v):
        self.adj[u].discard(v)
        self.adj[v].discard(u)

    def new_vertex(self):
        self.adj.append(set())
        self.n += 1
        return self.n - 1

    def maxdeg(self):
        return max(len(a) for a in self.adj)

    def bipartite(self):
        col = [-1] * self.n
        for s in range(self.n):
            if col[s] >= 0:
                continue
            col[s] = 0
            st = [s]
            while st:
                u = st.pop()
                for w in self.adj[u]:
                    if col[w] < 0:
                        col[w] = 1 - col[u]
                        st.append(w)
                    elif col[w] == col[u]:
                        return False
        return True

    def ecc_all(self, sources=None, targets=None, limit=12):
        """R[v] = bitset of sources within distance k of v; returns the least k with R[v] full for every
        target v (None if not reached within limit)."""
        sources = list(range(self.n)) if sources is None else list(sources)
        targets = range(self.n) if targets is None else targets
        bit = {s: 1 << i for i, s in enumerate(sources)}
        full = (1 << len(sources)) - 1
        R = [bit.get(v, 0) for v in range(self.n)]
        for k in range(limit + 1):
            if all(R[v] == full for v in targets):
                return k
            R = [R[v] | self._or(R, v) for v in range(self.n)]
        return None

    def _or(self, R, v):
        x = 0
        for w in self.adj[v]:
            x |= R[w]
        return x

    def dist_from(self, s):
        d = {s: 0}
        fr = [s]
        while fr:
            nx = []
            for u in fr:
                for w in self.adj[u]:
                    if w not in d:
                        d[w] = d[u] + 1
                        nx.append(w)
            fr = nx
        return d


# ------------------------------------------------------------------ level structures

class Levels:
    """Copies 0..n-1, copy j a copy of S[j] (a GQ, or its dual).  Vertex of point p of copy j:
    j*2N + p; of line L: j*2N + N + L.  Arcs: dict (j, j') -> bijection M (list: point p of copy j ->
    line M[p] of copy j')."""

    def __init__(self, S, arcs):
        self.S, self.arcs = S, arcs
        self.N = S[0].np
        N = self.N
        self.g = Graph(len(S) * 2 * N)
        for j, G in enumerate(S):
            for p in range(N):
                for L in G.lines_on[p]:
                    self.g.add(self.P(j, p), self.L(j, L))
        for (j, jj), M in arcs.items():
            for p in range(N):
                self.g.add(self.P(j, p), self.L(jj, M[p]))

    def P(self, j, p):
        return j * 2 * self.N + p

    def L(self, j, L):
        return j * 2 * self.N + self.N + L


def two_copy_bad(GA, GB, M, R):
    """GA = copy j, GB = copy j' (GQs on the same N), M: points of j -> lines of j', R freed.
    Pairs (u in j, v in j') at distance > 5 in the two-copy graph without the freed incidences."""
    N = GA.np
    g = Graph(4 * N)
    for p in range(N):
        for L in GA.lines_on[p]:
            g.add(p, N + L)
        for L in GB.lines_on[p]:
            g.add(2 * N + p, 3 * N + L)
    for p in range(N):
        if p not in R:
            g.add(p, 3 * N + M[p])
    bad = []
    for u in range(2 * N):
        d = g.dist_from(u)
        for v in range(2 * N, 4 * N):
            if d.get(v, 99) > 5:
                bad.append((u, v))
    return bad


def conditions_E(GA, GB, M, R):
    """(E2), (E3) of Theorem E, evaluated as stated."""
    N = GA.np
    Minv = [0] * N
    for p in range(N):
        Minv[M[p]] = p
    e2 = e3 = True
    for x in R:
        coveredE2 = set()
        for a in GA.coll_set(x) - set(R):
            coveredE2 |= GB.pset[M[a]]
        if len(coveredE2) != N:
            e2 = False
        conc = GB.conc_set(M[x])
        good = {Minv[Y] for Y in conc} - set(R)          # points a notin R with M(a) concurrent with M(x)
        if any(not (GA.pset[L] & good) for L in range(N)):
            e3 = False
    return e2, e3


def random_bij(N, rng):
    M = list(range(N))
    rng.shuffle(M)
    return M


def local_duality_two(GA, GB, x, y, l, m, rng):
    """Proposition 6.4: M(x)=l, M(y)=m, {x,y}^perp -> {l,m}^perp, the rest of Gamma_2(x) -> the rest of
    Gamma_2(l), the same for y, m; the rest arbitrary."""
    N = GA.np
    px, py = GA.coll_set(x), GA.coll_set(y)
    cl, cm = GB.conc_set(l), GB.conc_set(m)
    pieces = [([x], [l]), ([y], [m]), (sorted(px & py), sorted(cl & cm)),
              (sorted(px - py), sorted(cl - cm)), (sorted(py - px), sorted(cm - cl))]
    M = [None] * N
    usedA, usedB = set(), set()
    for A, B in pieces:
        assert len(A) == len(B)
        B = list(B)
        rng.shuffle(B)
        for a, b in zip(A, B):
            M[a] = b
        usedA |= set(A)
        usedB |= set(B)
    restA = [p for p in range(N) if p not in usedA]
    restB = [L for L in range(N) if L not in usedB]
    rng.shuffle(restB)
    for a, b in zip(restA, restB):
        M[a] = b
    return M


# ------------------------------------------------------------------ the explicit sets of D5_QUADRANGLE.md

def spread_lemma11(G, q):
    """Lemma 1.1: l_inf = <e2,e3>, l_{a,b} = <(1,0,a,b), (0,1,b, alpha a + beta b)>."""
    al, be = next((a, b) for a in range(q) for b in range(q)
                  if all((x * x - b * x - a) % q for x in range(q)))
    idx = G.idx
    sp = [line_through(G, idx[(0, 0, 1, 0)], idx[(0, 0, 0, 1)])]
    for a in range(q):
        for b in range(q):
            u, v = (1, 0, a, b), (0, 1, b, (al * a + be * b) % q)
            sp.append(line_through(G, idx[normp(u, q)], idx[normp(v, q)]))
    return sp


def partial_ovoid_lemma13(G, q, tau=2, z=(1, 3)):
    """Lemma 1.3 (q odd, q >= 5): points (u, v), u, v in F_q^2."""
    perp = lambda v: ((-v[1]) % q, v[0] % q)
    a = [(1, 0), (0, 1), (1, 1)]
    b = [perp(a[(i - 1) % 3]) for i in range(3)]
    S = [(a[i][0], a[i][1], (c * b[i][0]) % q, (c * b[i][1]) % q) for i in range(3) for c in range(1, q)]
    S.append((1, tau % q, 0, 0))
    zp = perp(z)
    S.append((0, 0, zp[0], zp[1]))
    return [G.idx[normp(s, q)] for s in S]


# ------------------------------------------------------------------ 1. the quadrangles

def part1():
    out = {}
    for q in (2, 3, 5, 7):
        Wq = W(q)
        Qq = Wq.dual()
        N = (q + 1) * (q * q + 1)
        check(Wq.np == Wq.nl == N, f'W({q}) counts')
        if q <= 5:
            check(is_gq(Wq, q, q) and is_gq(Qq, q, q), f'W({q}), Q(4,{q}) are GQs of order (q,q)')
        out[q] = (Wq, Qq)
    print('1. W(q), Q(4,q) = W(q)^D are GQs of order (q,q): checked for q = 2, 3, 5')
    return out


# ------------------------------------------------------------------ 2. Theorem A

def part2(geo, rng):
    for q in (2, 3):
        Wq, Qq = geo[q]
        N = Wq.np
        for r in (1, 2):
            for trial in range(2):
                n = 2 * r + 1
                types = [rng.choice('HD') for _ in range(n)]
                S = [Qq if t == 'H' else Wq for t in types]   # a copy of D is a copy of the dual of Q(4,q)
                # a random regular tournament: rotational, then relabel the levels
                perm = list(range(n))
                rng.shuffle(perm)
                arcs = {(perm[j], perm[(j + k) % n]): random_bij(N, rng) for j in range(n) for k in range(1, r + 1)}
                X = Levels(S, arcs)
                degs = {len(a) for a in X.g.adj}
                check(degs == {q + 1 + r}, f'Theorem A: ({q}+1+{r})-regular')
                check(X.g.n == n * 2 * N, 'Theorem A: count')
                check(X.g.ecc_all() == 5, f'Theorem A: diameter 5 (q={q}, r={r}, types {"".join(types)})')
    print('2. Theorem A: random tournaments, typings, bijections, q = 2, 3, r = 1, 2: regular, diameter 5')


# ------------------------------------------------------------------ 3. Theorem E

def random_freed(G, kind, rng, size):
    N = G.np
    if kind == 'random':
        return set(rng.sample(range(N), size))
    if kind == 'noncollinear':
        R = []
        cand = list(range(N))
        rng.shuffle(cand)
        for p in cand:
            if all(not G.collinear(p, x) for x in R):
                R.append(p)
            if len(R) == size:
                break
        return set(R)
    if kind == 'line':
        L = rng.randrange(G.nl)
        return set(G.pts_on[L][:size])
    if kind == 'pencil':
        p = rng.randrange(N)
        R = {p}
        for L in G.lines_on[p]:
            R.add(rng.choice([x for x in G.pts_on[L] if x != p]))
        return R


def part3(geo, rng):
    stats = {'agree': 0, 'only_e2': 0, 'only_e3': 0, 'both_fail': 0, 'repaired': 0}
    for q in (2, 3):
        Wq, Qq = geo[q]
        N = Wq.np
        for GA, GB, friendly in ((Qq, Wq, True), (Wq, Qq, True), (Qq, Qq, False), (Wq, Wq, False)):
            for trial in range(12):
                kind = ['random', 'noncollinear', 'line', 'pencil'][trial % 4]
                R = random_freed(GA, kind, rng, rng.randint(1, 3))
                if friendly and trial % 3 == 0:
                    M = list(range(N))
                elif not friendly and trial % 3 == 0 and kind == 'noncollinear' and len(R) == 2:
                    x, y = sorted(R)
                    l = rng.randrange(N)
                    m = rng.choice([L for L in range(N) if L != l and not GB.concurrent(l, L)])
                    M = local_duality_two(GA, GB, x, y, l, m, rng)
                else:
                    M = random_bij(N, rng)
                e2, e3 = conditions_E(GA, GB, M, R)
                bad = two_copy_bad(GA, GB, M, R)
                check((e2 and e3) == (not bad), f'Theorem E: conditions and brute force agree (q={q})')
                stats['agree'] += 1
                stats['repaired'] += (not bad)
                stats['only_e2'] += (not e2 and e3)
                stats['only_e3'] += (e2 and not e3)
                stats['both_fail'] += (not e2 and not e3)
    # perturbed two-point local dualities: a few images exchanged
    for q in (2, 3):
        Wq, Qq = geo[q]
        N = Wq.np
        for GA, GB in ((Qq, Qq), (Wq, Wq), (Qq, Wq)):
            for trial in range(40):
                x = rng.randrange(N)
                y = rng.choice([p for p in range(N) if p != x and not GA.collinear(x, p)])
                l = rng.randrange(N)
                m = rng.choice([L for L in range(N) if L != l and not GB.concurrent(l, L)])
                M = local_duality_two(GA, GB, x, y, l, m, rng)
                near = sorted(GA.coll_set(x) | GA.coll_set(y))
                for _ in range(rng.randint(1, 3)):
                    a = rng.choice(near)
                    b = rng.randrange(N)
                    if b not in (x, y) and a not in (x, y):
                        M[a], M[b] = M[b], M[a]
                R = {x, y}
                e2, e3 = conditions_E(GA, GB, M, R)
                bad = two_copy_bad(GA, GB, M, R)
                check((e2 and e3) == (not bad), f'Theorem E (perturbed local dualities, q={q})')
                stats['agree'] += 1
                stats['repaired'] += (not bad)
                stats['only_e2'] += (not e2 and e3)
                stats['only_e3'] += (e2 and not e3)
                stats['both_fail'] += (not e2 and not e3)
    # targeted: M maps the points collinear with x onto the lines concurrent with another line L1 ((E2) holds,
    # (E3) usually fails), or maps the points collinear with another point x2 onto the lines concurrent with
    # M(x) ((E3) holds, (E2) usually fails)
    for q in (2, 3):
        Wq, Qq = geo[q]
        N = Wq.np
        for kind in ('E2 kept', 'E3 kept'):
            for trial in range(20):
                GA, GB = [(Qq, Qq), (Wq, Wq), (Qq, Wq), (Wq, Qq)][trial % 4]
                x = rng.randrange(N)
                l0 = rng.randrange(N)
                M = [None] * N
                M[x] = l0
                if kind == 'E2 kept':
                    L1 = rng.choice([L for L in range(N) if L != l0 and not GB.concurrent(l0, L)])
                    A, B = sorted(GA.coll_set(x)), sorted(GB.conc_set(L1))
                else:
                    x2 = rng.choice([p for p in range(N) if p != x and not GA.collinear(x, p)])
                    A, B = sorted(GA.coll_set(x2)), sorted(GB.conc_set(l0))
                rng.shuffle(B)
                for a, b in zip(A, B):
                    M[a] = b
                restA = [p for p in range(N) if M[p] is None]
                used = set(M) - {None}
                restB = [L for L in range(N) if L not in used]
                rng.shuffle(restB)
                for a, b in zip(restA, restB):
                    M[a] = b
                R = {x}
                e2, e3 = conditions_E(GA, GB, M, R)
                check(e2 if kind == 'E2 kept' else e3, 'targeted Theorem E test keeps the intended condition')
                bad = two_copy_bad(GA, GB, M, R)
                check((e2 and e3) == (not bad), f'Theorem E (targeted, q={q})')
                stats['agree'] += 1
                stats['repaired'] += (not bad)
                stats['only_e2'] += (not e2 and e3)
                stats['only_e3'] += (e2 and not e3)
                stats['both_fail'] += (not e2 and not e3)
    print(f'3. Theorem E agrees with the brute force on {stats["agree"]} transitions '
          f'({stats["repaired"]} repaired; failing only (E2): {stats["only_e2"]}, only (E3): {stats["only_e3"]}, '
          f'both: {stats["both_fail"]})')


# ------------------------------------------------------------------ 4. Theorem B

def duality_W2():
    """Lemma 1.4 of D5_QUADRANGLE.md for q = 2: psi(<x,y>) = (p01, p03, p23, p12)."""
    q = 2
    Wq = W(q)
    pl = lambda x, y, i, j: (x[i] * y[j] - x[j] * y[i]) % q
    psi = []
    for L in Wq.lines:
        x, y = [Wq.coords[i] for i in sorted(L)[:2]]
        psi.append(Wq.idx[normp((pl(x, y, 0, 1), pl(x, y, 0, 3), pl(x, y, 2, 3), pl(x, y, 1, 2)), q)])
    check(sorted(psi) == list(range(Wq.np)), 'Lemma 1.4: psi is a bijection lines -> points (q=2)')
    phi = []
    for p in range(Wq.np):
        img = frozenset(psi[L] for L in Wq.lines_on[p])
        phi.append(Wq.lidx.get(img))
    check(None not in phi and sorted(phi) == list(range(Wq.nl)), 'Lemma 1.4: phi(x) is a line, phi a bijection')
    check(all((psi[L] in Wq.pset[phi[p]]) == (p in Wq.pset[L]) for p in range(Wq.np) for L in range(Wq.nl)),
          'Lemma 1.4: (phi, psi) is a duality of W(2)')
    return Wq, phi


def part4(geo, rng):
    q = 3
    Wq, Qq = geo[q]
    N = Wq.np
    n_ok = n_no = 0
    for GA, GB in ((Qq, Wq), (Wq, Qq)):
        for trial in range(20):
            if trial % 2:
                R = random_freed(GA, 'noncollinear', rng, rng.randint(2, 8))
            else:
                R = random_freed(GA, 'noncollinear', rng, rng.randint(1, 6))
                x = next(iter(R))
                R.add(rng.choice(sorted(GA.coll_set(x))))
            noncoll = all(not GA.collinear(a, b) for a, b in itertools.combinations(R, 2))
            bad = two_copy_bad(GA, GB, list(range(N)), R)
            check(noncoll == (not bad), 'Theorem B (identity): repaired iff non-collinear')
            n_ok += noncoll
            n_no += not noncoll
    # a duality: W(2) -> W(2), M = phi restricted to points
    W2, phi = duality_W2()
    for trial in range(20):
        R = random_freed(W2, 'noncollinear', rng, rng.randint(1, 5))
        if trial % 2:
            x = next(iter(R))
            R.add(rng.choice(sorted(W2.coll_set(x))))
        noncoll = all(not W2.collinear(a, b) for a, b in itertools.combinations(R, 2))
        bad = two_copy_bad(W2, W2, phi, R)
        check(noncoll == (not bad), 'Theorem B (duality, q=2): repaired iff non-collinear')
    # a collinear pair: the witness of the proof (x, and a line through y other than xy)
    GA, GB = Qq, Wq
    x = 0
    y = sorted(GA.coll_set(x))[0]
    bad = two_copy_bad(GA, GB, list(range(N)), {x, y})
    xy = (GA.lset[x] & GA.lset[y]).pop()
    witnesses = {(GA.np * 0 + x, 2 * N + L) for L in GA.lines_on[y] if L != xy}
    check(witnesses <= set(bad), 'Theorem B: x and each line through y other than xy (a point of the dual copy) are far')
    print(f'4. Theorem B: identity transitions on Q(4,3) and W(3) ({n_ok} non-collinear sets repaired, '
          f'{n_no} sets with a collinear pair not), and the duality of W(2): checked')


# ------------------------------------------------------------------ 5. Theorem C, Proposition 6.4, triads

def centres(G, a, b, c):
    return len(G.coll_set(a) & G.coll_set(b) & G.coll_set(c))


def part5(geo, rng):
    for q in (3, 5):
        Wq, Qq = geo[q]
        N = Wq.np
        for GA, GB in ((Qq, Qq), (Wq, Wq), (Qq, Wq)):
            for trial in range(3 if q == 3 else 2):
                x = rng.randrange(N)
                y = rng.choice([p for p in range(N) if p != x and not GA.collinear(x, p)])
                l = rng.randrange(N)
                m = rng.choice([L for L in range(N) if L != l and not GB.concurrent(l, L)])
                M = local_duality_two(GA, GB, x, y, l, m, rng)
                check(sorted(M) == list(range(N)), 'Prop 6.4: M is a bijection')
                for z in (x, y):
                    check({M[a] for a in GA.coll_set(z)} == GB.conc_set(M[z]), 'Prop 6.4: (H3)')
                e2, e3 = conditions_E(GA, GB, M, {x, y})
                check(e2 and e3 and not two_copy_bad(GA, GB, M, {x, y}), f'Theorem C: two-point local duality repaired (q={q})')
                check(not GB.concurrent(M[x], M[y]), 'remark after Theorem C: M(R) non-concurrent')
    # triads
    for q in (3, 5):
        Wq, Qq = geo[q]
        N = Wq.np
        for G, name, allowed in ((Qq, 'Q(4,%d)' % q, {0, 2}), (Wq, 'W(%d)' % q, {1, q + 1})):
            seen = set()
            if q == 3:
                for a, b, c in itertools.combinations(range(N), 3):
                    if not (G.collinear(a, b) or G.collinear(a, c) or G.collinear(b, c)):
                        seen.add(centres(G, a, b, c))
            else:
                for _ in range(4000):
                    a, b, c = rng.sample(range(N), 3)
                    if not (G.collinear(a, b) or G.collinear(a, c) or G.collinear(b, c)):
                        seen.add(centres(G, a, b, c))
            check(seen == allowed, f'triads of points of {name}: centres {sorted(seen)}')
    # Corollary 6.2 directly on Q(4,3): no bijection with (H3) at three pairwise non-collinear points.
    # (H3) at x, y, z forces M({x,y,z}^perp) = the lines concurrent with M(x), M(y), M(z); the counts differ.
    q = 3
    Wq, Qq = geo[q]
    ok = True
    for a, b, c in itertools.combinations(range(Qq.np), 3):
        if not (Qq.collinear(a, b) or Qq.collinear(a, c) or Qq.collinear(b, c)):
            ca = centres(Qq, a, b, c)
            ok &= ca in (0, 2)
    lines_triads = {len(Qq.conc_set(A) & Qq.conc_set(B) & Qq.conc_set(C))
                    for A, B, C in itertools.combinations(range(Qq.nl), 3)
                    if not (Qq.concurrent(A, B) or Qq.concurrent(A, C) or Qq.concurrent(B, C))}
    check(ok and lines_triads == {1, q + 1}, 'Corollary 6.2 for Q(4,3): point triads 0/2 centres, line triads 1/(q+1)')
    print('5. Proposition 6.4 and Theorem C (q = 3, 5), triad centres (Q(4,q): 0, 2; W(q): 1, q+1), Corollary 6.2: checked')


# ------------------------------------------------------------------ 6. relaxed sets

def relaxed_set(Wq, rng, pairs_wanted, singles_wanted):
    """a set of points of W(q) (= lines of Q(4,q)) in which every point is collinear with at most one
    other; greedy."""
    N = Wq.np
    T, partner = [], {}
    cand = list(range(N))
    rng.shuffle(cand)
    for p in cand:
        if len(partner) // 2 < pairs_wanted:
            # try to add a pair p, p'
            if any(Wq.collinear(p, x) for x in T):
                continue
            opts = [y for y in Wq.coll_set(p) if y not in T and not any(Wq.collinear(y, x) for x in T)]
            if opts:
                y = rng.choice(opts)
                T += [p, y]
                partner[p], partner[y] = y, p
        elif len(T) - len(partner) < singles_wanted:
            if not any(Wq.collinear(p, x) for x in T):
                T.append(p)
    return T, partner


def part6(geo, rng):
    for q in (3, 5):
        Wq, Qq = geo[q]
        N = Wq.np
        GA, GB = Wq, Qq          # copy j: dual of Q(4,q) (= W(q)), points = lines of Q(4,q); copy j': Q(4,q)
        for trial in range(3):
            T, partner = relaxed_set(Wq, rng, 2 if q == 3 else 3, 2)
            bad = set(two_copy_bad(GA, GB, list(range(N)), set(T)))
            expected = set()
            for l, m in partner.items():
                z = (Qq.pset[l] & Qq.pset[m]).pop()      # l, m lines of Q(4,q); z their common point
                for p in Qq.pts_on[m]:
                    if p != z:
                        # ((l, j), (p, j')): point l of copy j, point p of copy j'
                        expected.add((l, 2 * N + p))
                        # ((p, j), (l, j')): line p of copy j, line l of copy j'
                        expected.add((N + p, 3 * N + l))
            check(bad == expected, f'Prop 7.1: the bad pairs are exactly the stated ones (q={q})')
            check(len(bad) == 4 * q * (len(partner) // 2), 'Prop 7.1: 4q pairs per partner pair')
            # Proposition 7.2: hub g_l on the line (l, j') and on a line (o, j) of copy j, o a point of m
            g = Graph(4 * N)
            for p in range(N):
                for L in GA.lines_on[p]:
                    g.add(p, N + L)
                for L in GB.lines_on[p]:
                    g.add(2 * N + p, 3 * N + L)
                if p not in T:
                    g.add(p, 3 * N + p)
            for l, m in partner.items():
                h = g.new_vertex()
                g.add(h, 3 * N + l)
                o = rng.choice(Qq.pts_on[m])               # any point of the partner (here a line of copy j)
                g.add(h, N + o)
            check(all(g.dist_from(u).get(v, 99) <= 4 for u, v in bad), f'Prop 7.2: the hub rule repairs them (q={q})')
    print('6. Propositions 7.1 and 7.2 (relaxed freed sets, the hub rule): checked for q = 3, 5')


# ------------------------------------------------------------------ 7. hub graphs (Lemma 9.1)

def pg2(s):
    pts = proj_points(s, 3)
    idx = {p: i for i, p in enumerate(pts)}
    lines = [[idx[p] for p in pts if (p[0] * a[0] + p[1] * a[1] + p[2] * a[2]) % s == 0] for a in pts]
    return GQ(len(pts), len(lines), [(p, i) for i, L in enumerate(lines) for p in L])


def hub_graph(core, extra, which_lines, which_points):
    """core incidence structure (points = B-hubs, lines = A-hubs), with 'extra' pendant B-vertices on
    each line in which_lines and pendant A-vertices on each point in which_points."""
    nB, nA = core.np, core.nl
    g = Graph(nB + nA)
    B = list(range(nB))
    A = list(range(nB, nB + nA))
    for p in range(nB):
        for L in core.lines_on[p]:
            g.add(p, nB + L)
    for L in which_lines:
        for _ in range(extra):
            v = g.new_vertex()
            g.add(v, nB + L)
            B.append(v)
    for p in which_points:
        for _ in range(extra):
            v = g.new_vertex()
            g.add(v, p)
            A.append(v)
    return g, B, A


def same_colour_ok(g, B, A):
    for side in (B, A):
        for u in side:
            d = g.dist_from(u)
            if any(d.get(v, 99) > 4 for v in side):
                return False
    return True


def part7(geo):
    for s in (2, 3):
        delta = s + 2
        core = pg2(s)
        g, B, A = hub_graph(core, delta - s - 1, range(core.nl), range(core.np))
        check(g.maxdeg() <= delta and len(B) == len(A) == (s * s + s + 1) * (delta - s), 'Lemma 9.1 (Y1): sizes, degrees')
        check(same_colour_ok(g, B, A), f'Lemma 9.1 (Y1): same-colour distance <= 4 (s={s})')
        Ws = geo[s][0]
        z0, m0 = 0, Ws.lines_on[0][0]
        g, B, A = hub_graph(Ws, delta - s - 1, Ws.lines_on[z0], Ws.pts_on[m0])
        check(g.maxdeg() <= delta and len(B) == len(A) == (s + 1) * (s * s + 1) + (s + 1) * (delta - s - 1),
              'Lemma 9.1 (Y2): sizes, degrees')
        check(same_colour_ok(g, B, A), f'Lemma 9.1 (Y2): same-colour distance <= 4 (s={s})')
    print('7. Lemma 9.1, hub graphs (Y1) and (Y2) with pendants, s = 2, 3: checked')


# ------------------------------------------------------------------ 8. slot vectors and the family values

def slot_vectors(types, r, size):
    n = len(types)
    alpha, beta = [0] * n, [0] * n
    for j in range(n):
        for k in range(1, r + 1):
            jj = (j + k) % n
            kind = types[j] + types[jj]
            s = size['HD'] if kind == 'HD' else size['DH'] if kind == 'DH' else size['NF']
            alpha[j] += s
            beta[jj] += s
    return alpha, beta


def Nq(s):
    return (s + 1) * (s * s + 1)


def prime_powers(n):
    out = []
    for k in range(2, n + 1):
        f = [p for p in range(2, k + 1) if k % p == 0 and all(p % d for d in range(2, p))]
        if len(f) == 1:
            out.append(k)
    return out


def hub_boxes(delta):
    """Lemma 9.1: (Y0)-(Y2) give boxes lo <= K_B, K_A <= hi; (Y3) gives single sizes."""
    boxes = [(1, delta)]
    for s in prime_powers(40):
        if s + 1 <= delta:
            boxes.append((s * s + s + 1, (s * s + s + 1) * (delta - s)))
            boxes.append((Nq(s), Nq(s) + (s + 1) * (delta - s - 1)))
        for rr in range(1, delta):
            if s + 1 + rr <= delta:
                K = (2 * rr + 1) * Nq(s)
                boxes.append((K, K))
    return boxes


def best_hubs(maxB, maxA, delta):
    """the largest K_B + K_A with K_B <= maxB, K_A <= maxA for which Lemma 9.1 gives a hub graph."""
    best = 0
    for lo, hi in hub_boxes(delta):
        kb, ka = min(hi, maxB), min(hi, maxA)
        if kb >= lo and ka >= lo:
            best = max(best, kb + ka)
    return best


def part8_numeric():
    for (A_, B_, C_) in [(26, 15, 2), (82, 26, 2), (50, 30, 2), (10, 9, 1)]:
        size = {'HD': A_, 'DH': B_, 'NF': C_}
        al, be = slot_vectors('HHHDHHD', 3, size)
        check(al == [A_ + 2 * C_] * 3 + [2 * B_ + C_] + [A_ + 2 * C_] * 2 + [3 * B_]
              and be == [B_ + 2 * C_] * 3 + [3 * A_] + [B_ + 2 * C_] * 2 + [2 * A_ + C_], 'Prop 8.1 slot vectors')
        al, be = slot_vectors('HHDHD', 2, size)
        check(al == [A_ + C_, A_ + C_, B_ + C_, A_ + C_, 2 * B_] and be == [B_ + C_, B_ + C_, 2 * A_, B_ + C_, A_ + C_],
              'Prop 8.2 slot vectors')
        al, be = slot_vectors('HHHHDHHHD', 4, size)
        check(al == [A_ + 3 * C_] * 4 + [3 * B_ + C_] + [A_ + 3 * C_] * 3 + [4 * B_]
              and be == [B_ + 3 * C_] * 4 + [4 * A_] + [B_ + 3 * C_] * 3 + [3 * A_ + C_], 'Prop 8.3 slot vectors')
    # the family values: q odd: a = q^2+1, b = 3q-1, c = 2; q even: all H, a duality, an ovoid on every arc
    fam = {}
    for q in prime_powers(13):
        if q % 2 == 0:
            for r in range(1, q):
                Delta = q + 1 + r
                v = (2 * r + 1) * 2 * Nq(q) + best_hubs(r * (q * q + 1), r * (q * q + 1), q - r)
                fam[Delta] = max(fam.get(Delta, 0), v)
        elif q >= 5:
            size = {'HD': q * q + 1, 'DH': 3 * q - 1, 'NF': 2}
            for types, r in (('HHDHD', 2), ('HHHDHHD', 3), ('HHHHDHHHD', 4)):
                if q - r < 1:
                    continue
                al, be = slot_vectors(types, r, size)
                Delta = q + 1 + r
                v = (2 * r + 1) * 2 * Nq(q) + best_hubs(min(al), min(be), q - r)
                fam[Delta] = max(fam.get(Delta, 0), v)
    want = {10: 4044, 11: 6090, 12: 8430, 13: 11552, 14: 14812, 15: 20598}
    table = {10: 4000, 11: 5850, 12: 8200, 13: 11480, 14: 14760, 15: 20496}
    for D, v in want.items():
        check(fam.get(D) == v, f'family value at Delta = {D}: {fam.get(D)} (expected {v})')
        check(v > table[D], 'family value above the 2013 table')
    print('8. Propositions 8.1-8.3 (slot vectors) and the family values 4,044, 6,090, 8,430, 11,552, 14,812, '
          '20,598 (prime powers q <= 13): checked')


# ------------------------------------------------------------------ 9, 10. full structures with hubs

def build_typed(q, Wq, Qq, types, r, ovoid, T, partner, KB, KA, Yedges, rng, spread_of=None):
    """Definition 3.1 of D5_QUADRANGLE.md with the rotational tournament: H copies of Q(4,q), D copies of
    its dual W(q).  H->D and D->H arcs: identity, freed O (points of Q(4,q)) resp. T (lines of Q(4,q));
    other arcs: two-point local dualities.  A-hubs for partnered lines placed as in Lemma 7.3."""
    n = len(types)
    N = Wq.np
    S = [Qq if t == 'H' else Wq for t in types]
    arcs, freed = {}, {}
    for j in range(n):
        for k in range(1, r + 1):
            jj = (j + k) % n
            if types[j] != types[jj]:
                arcs[(j, jj)] = list(range(N))
                freed[(j, jj)] = set(ovoid) if types[j] == 'H' else set(T)
            else:
                GA, GB = S[j], S[jj]
                x = rng.randrange(N)
                y = rng.choice([p for p in range(N) if p != x and not GA.collinear(x, p)])
                l = rng.randrange(N)
                m = rng.choice([L for L in range(N) if L != l and not GB.concurrent(l, L)])
                arcs[(j, jj)] = local_duality_two(GA, GB, x, y, l, m, rng)
                freed[(j, jj)] = {x, y}
    X = Levels(S, arcs)
    g = X.g
    Aslots = {j: [] for j in range(n)}      # free A-slots (point of copy j) per level: (vertex, arc)
    Bslots = {j: [] for j in range(n)}      # free B-slots (line of copy jj)
    for (j, jj), R in freed.items():
        M = arcs[(j, jj)]
        for p in R:
            g.remove(X.P(j, p), X.L(jj, M[p]))
            Aslots[j].append((X.P(j, p), (j, jj)))
            Bslots[jj].append((X.L(jj, M[p]), (j, jj)))
    alpha = [len(Aslots[j]) for j in range(n)]
    beta = [len(Bslots[j]) for j in range(n)]
    # A-hubs (new points) take one free B-slot in every level
    Ahubs = [g.new_vertex() for _ in range(KA)]
    Bhubs = [g.new_vertex() for _ in range(KB)]
    taken = set()
    plines = [l for l in T if l in partner]
    assert len(plines) <= KA
    # in an H level, a D->H arc ends there; in a D level, the requested slot is at the ovoid point of the partner
    for i, l in enumerate(plines):
        h = Ahubs[i]
        m = partner[l]
        om = next(o for o in ovoid if o in Qq.pset[m])          # the point where the ovoid meets m
        for j in range(n):
            if types[j] == 'H':
                cand = [s for s in Bslots[j] if s not in taken and s[0] == X.L(j, l) and types[s[1][0]] == 'D']
            else:
                cand = [s for s in Bslots[j] if s not in taken and s[0] == X.L(j, om)]
            assert cand, 'Lemma 7.3: a requested slot is available'
            taken.add(cand[0])
            g.add(h, cand[0][0])
    for h in Ahubs[len(plines):]:
        for j in range(n):
            s = next(s for s in Bslots[j] if s not in taken)
            taken.add(s)
            g.add(h, s[0])
    takenA = set()
    for h in Bhubs:
        for j in range(n):
            s = rng.choice([s for s in Aslots[j] if s not in takenA])
            takenA.add(s)
            g.add(h, s[0])
    for b, a in Yedges:
        g.add(Bhubs[b], Ahubs[a])
    return g, alpha, beta, X


def part9(geo, rng):
    q = 5
    Wq, Qq = geo[q]
    N = Wq.np
    sp = spread_lemma11(Wq, q)            # a spread of W(5) = an ovoid of Q(4,5) (points of Q(4,5) = lines of W)
    check(len(sp) == q * q + 1 and len(set().union(*[Wq.pset[L] for L in sp])) == N, 'Lemma 1.1: a spread of W(5)')
    ovoid = sp
    check(all(len(set(Qq.pts_on[L]) & set(ovoid)) == 1 for L in range(Qq.nl)), 'the ovoid meets every line of Q(4,5) once')
    S13 = partial_ovoid_lemma13(Wq, q)
    check(len(set(S13)) == 3 * q - 1 and all(not Wq.collinear(a, b) for a, b in itertools.combinations(S13, 2)),
          'Lemma 1.3: 3q-1 pairwise non-collinear points of W(5)')
    # one partner, on the spread line of some point s of S13, collinear with no other point of S13
    found = None
    for s in S13:
        Ls = next(L for L in sp if s in Wq.pset[L])
        for z2 in Wq.pts_on[Ls]:
            if z2 != s and all(not Wq.collinear(z2, x) for x in S13 if x != s):
                found = (s, z2, Ls)
                break
        if found:
            break
    check(found is not None, 'a partner meeting the set at an ovoid point exists')
    s, z2, Ls = found
    T = S13 + [z2]
    partner = {s: z2, z2: s}
    check(Ls in (Qq.pset[s] & Qq.pset[z2]), 'the partners meet at a point of the ovoid')
    types, r = 'HHHDHHD', 3
    Y = [(b, a) for b in range(2) for a in range(2)]          # (Y0): K_{2,2}, delta = q - r = 2
    g, alpha, beta, X = build_typed(q, Wq, Qq, types, r, ovoid, T, partner, 2, 2, Y, rng)
    a_, b_, c_ = q * q + 1, len(T), 2
    check(alpha == [a_ + 2 * c_] * 3 + [2 * b_ + c_] + [a_ + 2 * c_] * 2 + [3 * b_], f'alpha = {alpha}')
    check(beta == [b_ + 2 * c_] * 3 + [3 * a_] + [b_ + 2 * c_] * 2 + [2 * a_ + c_], f'beta = {beta}')
    check(g.n == 7 * 2 * N + 4 and g.maxdeg() == q + 1 + r and g.bipartite(), 'assembly: count, degree, bipartite')
    d = g.ecc_all()
    check(d == 5, f'assembly with a partner pair meeting at an ovoid point: diameter {d}')
    print(f'9. seven copies HHHDHHD over Q(4,5), 15 freed lines with one partner pair meeting at an ovoid point, '
          f'2 + 2 hubs placed by Lemma 7.3: {g.n} elements, max degree {g.maxdeg()}, diameter {d}')


def part10(geo, rng):
    q = 7
    Wq, Qq = geo[q]
    N = Wq.np
    sp = spread_lemma11(Wq, q)
    S13 = partial_ovoid_lemma13(Wq, q)
    check(len(set(S13)) == 3 * q - 1 and all(not Wq.collinear(a, b) for a, b in itertools.combinations(S13, 2)),
          'Lemma 1.3 for q = 7')
    types, r = 'HHDHD', 2
    # hub graph (Y1) with s = 3, delta = q - r = 5: PG(2,3) (13 + 13) and 9 pendants on each side
    core = pg2(3)
    Y = []
    nB = nA = 13
    for p in range(13):
        for L in core.lines_on[p]:
            Y.append((p, L))
    for i in range(9):
        Y.append((13 + i, i))          # pendant B-hub on the line i
        Y.append((i, 13 + i))          # pendant A-hub on the point i
    nB = nA = 22
    g, alpha, beta, X = build_typed(q, Wq, Qq, types, r, sp, S13, {}, nB, nA, Y, rng)
    check(min(alpha) == min(beta) == 3 * q + 1, 'Prop 8.2: min alpha = min beta = b + c')
    check(g.n == 4044 and g.maxdeg() == q + 1 + r and g.bipartite(), 'Corollary 10.2 at q = 7: 4,044 elements, degree 10')
    d = g.ecc_all()
    check(d == 5, f'Corollary 10.2 at q = 7: diameter {d}')
    print(f'10. Corollary 10.2 at q = 7 (five copies HHDHD over Q(4,7), 22 + 22 hubs): {g.n} elements, '
          f'max degree {g.maxdeg()}, diameter {d}')


def main():
    rng = random.Random(20261030)
    geo = part1()
    part2(geo, rng)
    part3(geo, rng)
    part4(geo, rng)
    part5(geo, rng)
    part6(geo, rng)
    part7(geo)
    part8_numeric()
    part9(geo, rng)
    part10(geo, rng)
    print('ALL CHECKS PASSED' if not FAIL else f'{len(FAIL)} FAILURES')


if __name__ == '__main__':
    main()
