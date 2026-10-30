r"""Checks for Section 6 of SYNTHETIC.tex (diameter 8: Gomez's construction on generalized hexagons, and
relabelling the copies), against research/theorems/OMEGA_NOTE.md (branch claude/omega-d8-note-xrbqux).

H(2), H(3) are built from coordinates as in check_d6.py; after that only incidence and distances are used.

  1. Distances in a generalized hexagon (Lemmas 1.4, 1.6 of OMEGA_NOTE.md): |S_i(u)| = (q+1)q^(i-1)
     for 1 <= i <= 5, q^5 opposite elements; |B(z,4) cap opp(t)| = 0, q^4, q^4, q^4 and
     |B(z,2) cap opp(t)| = 0, 0, q^2, q^2 for d(t,z) = 0, 2, 4, 6 (q = 2, 3).
  2. Gomez's wiring (Definition 2.1): every copy is met by two classes of each bar, every element of a
     copy gets two new neighbours, every new element meets 2 alpha of the 5 alpha copies, the structure
     is bipartite with degrees q+3 and 2 alpha and 5(alpha+1) 2N elements (q = 2, 3, all patterns,
     both readings, random pairings).
  3. Theorem 1 (projection): with the thesis labelling in reading 2, the elements at distance 9 from a
     new element are exactly the copies of the elements opposite its label in the 3 alpha copies it
     misses (q = 2, 3).  Exact diameters: 9 with both block types (q = 2: ab, both readings; q = 3:
     aba, both readings), 10 with one block type (q = 2, 3).
  4. Theorem 2: the constants A, B and the table of far vertices for q = 7, 8, 9, 11, 13.
  5. Lemma 5.6 and the route words of Lemma 5.4 (Computer-checked C4), from the wiring alone, for
     alpha = 5, 6, 7, 8 and all block patterns: every pair has r4 >= alpha; the starved pairs of Lemma
     5.6 exist; the largest m2 of a starved pair is 140, 201, 272, 353; in every pattern some starved
     pair has m2 <= 134, 197, 262, 347; m2 <= 8 alpha^2 - 1; the numbers of Theorem 3.
  6. Lemma 5.2: relabelling every copy by a collineation of H(q) (the maps (v,a,w) -> (Av,a,A^-T w),
     A in SL(3,q)) gives an isomorphic structure; checked by the distance profile from every new element
     class at q = 2.
  7. The repair at q = 3 (Computer-checked C7): the labelling q3_aba_LLL_G13.lab of the table audit
     (branch claude/table-audit-2-p7x6hn, research/projects/table-audit/omega/labs/), on the base hexagon
     of its moore_build.c (omega_q3_base.txt, re-checked here to be a generalized hexagon of order
     (3,3)), rebuilt here from Definition 2.1: 14,560 elements, 6-regular, bipartite, diameter 8.

Run: python3 check_d8.py      (about a minute)
"""
import itertools
import random
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from check_d6 import hexagon  # noqa: E402

FAIL = []


def check(cond, msg):
    if not cond:
        FAIL.append(msg)
        print('FAIL:', msg)


# ------------------------------------------------------------------ graphs

class Graph:
    def __init__(self, n):
        self.n = n
        self.adj = [[] for _ in range(n)]

    def add(self, u, v):
        self.adj[u].append(v)
        self.adj[v].append(u)

    def dist_from(self, s):
        d = [-1] * self.n
        d[s] = 0
        fr = [s]
        while fr:
            nx = []
            for u in fr:
                for w in self.adj[u]:
                    if d[w] < 0:
                        d[w] = d[u] + 1
                        nx.append(w)
            fr = nx
        return d

    def diameter(self, limit=14):
        """all sources at once: R[v] = bitset of sources within distance k of v."""
        n = self.n
        full = (1 << n) - 1
        R = [1 << v for v in range(n)]
        adj = self.adj
        for k in range(limit + 1):
            if all(x == full for x in R):
                return k
            new = []
            for v in range(n):
                x = R[v]
                for w in adj[v]:
                    x |= R[w]
                new.append(x)
            R = new
        return None

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


def base_hexagon(q):
    """incidence graph of H(q): points 0..N-1, lines N..2N-1; also the coordinates."""
    H, names, lines = hexagon(q)
    N = len(H.points)
    pidx = {p: i for i, p in enumerate(H.points)}
    edges = [(pidx[p], N + i) for i, L in enumerate(lines) for p in L]
    return N, edges, H.points, lines


def graph_from_edges(n, edges):
    g = Graph(n)
    for u, v in edges:
        g.add(u, v)
    return g


# ------------------------------------------------------------------ 1. distances in a hexagon

def part1():
    for q in (2, 3):
        N, edges, pts, lines = base_hexagon(q)
        I = graph_from_edges(2 * N, edges)
        rng = random.Random(q)
        sample = rng.sample(range(2 * N), 6)
        for u in sample:
            d = I.dist_from(u)
            sizes = [d.count(i) for i in range(7)]
            check(sizes == [1] + [(q + 1) * q ** (i - 1) for i in range(1, 6)] + [q ** 5],
                  f'H({q}): sphere sizes from an element: {sizes}')
        for t in rng.sample(range(N), 2) + rng.sample(range(N, 2 * N), 2):
            dt = I.dist_from(t)
            opp = {u for u in range(2 * N) if dt[u] == 6}
            same = range(0, N) if t < N else range(N, 2 * N)
            seen = {}
            for z in same:
                dz = I.dist_from(z)
                b4 = sum(1 for u in opp if dz[u] <= 4)
                b2 = sum(1 for u in opp if dz[u] <= 2)
                seen.setdefault(dt[z], set()).add((b4, b2))
            want = {0: {(0, 0)}, 2: {(q ** 4, 0)}, 4: {(q ** 4, q * q)}, 6: {(q ** 4, q * q)}}
            check(seen == want, f'H({q}): Lemma 1.6 ball counts {seen}')
    print('1. H(2), H(3): sphere sizes (q+1)q^(i-1), q^5 opposite elements; Lemma 1.6 (opposite elements in '
          'balls of radius 4 and 2): checked')


# ------------------------------------------------------------------ 2, 3. Gomez's wiring

def classes_meeting(types, c):
    """the hub classes (bar, k) that meet copy c = 5B + i (Definition 2.1)."""
    B, i = divmod(c, 5)
    if types[B] == 'a':
        return {(0, (i - 1) % 5), (0, (i + 1) % 5), (1, (i + 2) % 5), (1, (i + 3) % 5)}
    return {(0, (i + 1) % 5), (0, (i + 2) % 5), (1, (i - 1) % 5), (1, (i + 1) % 5)}


def copies_met(types, X):
    bar, k = X
    out = set()
    for B, ty in enumerate(types):
        if (ty == 'a') == (bar == 0):
            out |= {5 * B + (k - 1) % 5, 5 * B + (k + 1) % 5}
        elif ty == 'a':
            out |= {5 * B + (k + 2) % 5, 5 * B + (k + 3) % 5}
        else:
            out |= {5 * B + (k + 3) % 5, 5 * B + (k + 4) % 5}
    return out


def omega(N, edges, types, inner, P, L):
    """Definition 2.1.  inner[c] in 'PL'; P[c][t], L[c][t] (labellings, base indices 0..N-1).
    Copy c, base vertex v (points 0..N-1, lines N..2N-1): c*2N + v.  Hub (t, bar, k): 5 alpha 2N + 10t + 5bar + k."""
    A = len(types)
    C = 5 * A
    H0 = C * 2 * N
    g = Graph(H0 + 10 * N)
    for c in range(C):
        for u, v in edges:
            g.add(c * 2 * N + u, c * 2 * N + v)
    for c in range(C):
        B = c // 5
        for bar, k in classes_meeting(types, c):
            # a-block: unbarred on the inner class, barred on the outer; b-block: the other way round
            on_inner = (bar == 0) == (types[B] == 'a')
            on_points = (inner[c] == 'P') == on_inner
            for t in range(N):
                x = P[c][t] if on_points else N + L[c][t]
                g.add(H0 + 10 * t + 5 * bar + k, c * 2 * N + x)
    return g, H0


def readings(types):
    r1 = ''.join('L' * 5 for _ in types)
    r2 = ''.join(('P' if ty == 'a' else 'L') * 5 for ty in types)
    return {'reading 1': r1, 'reading 2': r2}


def part2_3():
    for q in (2, 3):
        N, edges, pts, lines = base_hexagon(q)
        alpha = (q + 3) // 2
        rng = random.Random(10 + q)
        pats = [''.join(p) for p in itertools.product('ab', repeat=alpha)]
        for types in pats:
            C = 5 * alpha
            for c in range(C):
                m = classes_meeting(types, c)
                check(sum(1 for b, k in m if b == 0) == 2 and sum(1 for b, k in m if b == 1) == 2,
                      'every copy is met by two classes of each bar')
            for X in itertools.product((0, 1), range(5)):
                cm = copies_met(types, X)
                check(len(cm) == 2 * alpha and all(X in classes_meeting(types, c) for c in cm)
                      and all(X not in classes_meeting(types, c) for c in range(C) if c not in cm),
                      'a class meets 2 alpha copies, two in each block')
        for types in (pats[1], pats[-2]) if alpha == 2 else (pats[2], pats[5]):
            for name, inner in readings(types).items():
                sigma = list(range(N))
                rng.shuffle(sigma)
                P = [list(range(N))] * (5 * alpha)
                Lb = [sigma] * (5 * alpha)
                g, H0 = omega(N, edges, types, inner, P, Lb)
                degs = [len(a) for a in g.adj]
                check(set(degs[:H0]) == {q + 3} and set(degs[H0:]) == {2 * alpha}, 'Lemma 2.2: degrees q+3 and 2 alpha')
                check(g.n == 5 * (alpha + 1) * 2 * N and g.bipartite(), 'Lemma 2.2: count and bipartite')
        # Theorem 1, reading 2, thesis labelling: distance-9 sets
        I = graph_from_edges(2 * N, edges)
        for types in ('ab', 'ba') if q == 2 else ('aba', 'abb'):
            inner = readings(types)['reading 2']
            sigma = list(range(N))
            rng.shuffle(sigma)
            P = [list(range(N))] * (5 * alpha)
            Lb = [sigma] * (5 * alpha)
            g, H0 = omega(N, edges, types, inner, P, Lb)
            for t in rng.sample(range(N), 2):
                for bar in (0, 1):
                    k = rng.randrange(5)
                    h = H0 + 10 * t + 5 * bar + k
                    d = g.dist_from(h)
                    label = t if bar == 0 else N + sigma[t]      # reading 2: unbarred on points, barred on lines
                    dl = I.dist_from(label)
                    missed = [c for c in range(5 * alpha) if c not in copies_met(types, (bar, k))]
                    want = {c * 2 * N + y for c in missed for y in range(2 * N) if dl[y] == 6}
                    far = {v for v in range(g.n) if d[v] >= 9}
                    check(far == want and max(d) == 9, f'Theorem 1 (q={q}, {types}): the far set is the opposite set')
        print(f'2-3. q = {q}: wiring, degrees, counts, bipartite (all patterns); Theorem 1 far sets (reading 2): checked')
        # exact diameters
        for types in (('ab',) if q == 2 else ('aba',)):
            for name, inner in readings(types).items():
                sigma = list(range(N))
                rng.shuffle(sigma)
                g, H0 = omega(N, edges, types, inner, [list(range(N))] * (5 * alpha), [sigma] * (5 * alpha))
                dm = g.diameter()
                check(dm == 9, f'diameter of the thesis structure, q={q}, {types}, {name}: {dm}')
                print(f'     q = {q}, pattern {types}, {name}, thesis labelling: {g.n} elements, diameter {dm}')
        types = 'a' * alpha
        g, H0 = omega(N, edges, types, readings(types)['reading 2'], [list(range(N))] * (5 * alpha),
                      [list(range(N))] * (5 * alpha))
        dm = g.diameter()
        check(dm == 10, f'one block type, q={q}: diameter {dm}')
        print(f'     q = {q}, pattern {types} (one block type): diameter {dm}')


# ------------------------------------------------------------------ 4. Theorem 2

def part4():
    s = lambda q, i: 1 if i == 0 else (q + 1) * q ** (i - 1)
    rows = {7: (15073, 385, 1348), 8: (24994, 487, 7286), 9: (39161, 601, 19286), 11: (84625, 865, 75560),
            13: (161449, 1177, 208666)}
    for q, (Aw, Bw, far) in rows.items():
        A = sum(s(q, e1) * s(q, e2) for e1 in range(5) for e2 in range(5) if e1 + e2 in (0, 2, 4))
        B = sum(s(q, e1) * s(q, e2) * s(q, e3) for e1 in range(3) for e2 in range(3) for e3 in range(3)
                if e1 + e2 + e3 <= 2)
        check(A == 5 * q ** 4 + 8 * q ** 3 + 6 * q ** 2 + 4 * q + 2 == Aw, f'Theorem 2: A at q={q}')
        check(B == 6 * q ** 2 + 12 * q + 7 == Bw, f'Theorem 2: B at q={q}')
        check(q ** 5 - (A + B + 1) == far > 0, f'Theorem 2: far vertices at q={q}')
    check(all(q ** 5 - (5 * q ** 4 + 8 * q ** 3 + 12 * q ** 2 + 16 * q + 10) > 0 for q in range(7, 200)), 'Theorem 2: q >= 7')
    check(all(q ** 5 - (5 * q ** 4 + 8 * q ** 3 + 12 * q ** 2 + 16 * q + 10) <= 0 for q in range(2, 7)), 'Theorem 2: fails q <= 6')
    print('4. Theorem 2: A, B and the far counts 1,348, 7,286, 19,286, 75,560, 208,666 (q = 7, 8, 9, 11, 13): checked')


# ------------------------------------------------------------------ 5. starved pairs and route words

def route_numbers(types, X):
    """for a class X (its bar = the 'point bar' P of Lemma 5.4, the other bar = L) and every copy c' it
    misses: r4 = |N(X,c')| and m2 (the pairs of W2 not of the form (c', c1), c1 in N(X,c'))."""
    C = 5 * len(types)
    meet = [classes_meeting(types, c) for c in range(C)]
    bar = X[0]
    sharesP = lambda c, d: any(Y[0] == bar for Y in meet[c] & meet[d])
    sharesL = lambda c, d: any(Y[0] != bar for Y in meet[c] & meet[d])
    CX = copies_met(types, X)
    out = {}
    for cp in range(C):
        if cp in CX:
            continue
        Nset = {c1 for c1 in CX if sharesL(c1, cp)}
        W2 = set()
        for c1 in CX:
            for c2 in range(C):
                if c2 in (c1, cp):
                    continue
                if sharesP(c1, c2) and sharesL(c2, cp):
                    W2.add((cp, c2))                      # P then L
                if sharesL(c1, c2) and sharesL(c2, cp):
                    W2.add((cp, c1))                      # L then L
                if sharesL(c1, c2) and sharesP(c2, cp):
                    W2.add((c2, c1))                      # L then P
        m2 = len({w for w in W2 if w[0] != w[1] and not (w[0] == cp and w[1] in Nset)})
        out[cp] = (len(Nset), m2)
    return out


def part5():
    want_max = {5: 140, 6: 201, 7: 272, 8: 353}
    want_best = {5: 134, 6: 197, 7: 262, 8: 347}
    for alpha in (5, 6, 7, 8):
        worst_starved, best_per_pattern = 0, 0
        for types in (''.join(p) for p in itertools.product('ab', repeat=alpha)):
            best_here = None
            starved_bars = set()
            for X in itertools.product((0, 1), range(5)):
                nums = route_numbers(types, X)
                check(all(r4 >= alpha for r4, m2 in nums.values()), 'C4: r4 >= alpha for every pair')
                for cp, (r4, m2) in nums.items():
                    if r4 == alpha:
                        starved_bars.add(X[0])
                        worst_starved = max(worst_starved, m2)
                        best_here = m2 if best_here is None else min(best_here, m2)
                        check(m2 <= 8 * alpha * alpha - 1, 'Corollary 5.5: m2 <= 8 alpha^2 - 1')
                # Lemma 5.6: the listed starved copies
                bar, k = X
                if bar == 0:
                    cps = [5 * B + (k + 3) % 5 for B, ty in enumerate(types) if ty == 'a'] or \
                          [5 * B + k for B in range(alpha)]
                else:
                    cps = [5 * B + (k + 3) % 5 for B, ty in enumerate(types) if ty == 'b'] or \
                          [5 * B + (k + 1) % 5 for B in range(alpha)]
                check(all(cp in nums and nums[cp][0] == alpha for cp in cps), f'Lemma 5.6 ({types}, {X})')
            check(starved_bars == {0, 1}, 'Lemma 5.6: starved pairs of both bars')
            best_per_pattern = max(best_per_pattern, best_here)
        check(worst_starved == want_max[alpha], f'C4: largest m2 of a starved pair, alpha={alpha}: {worst_starved}')
        check(best_per_pattern == want_best[alpha], f'C4: best starved pair, worst pattern, alpha={alpha}: {best_per_pattern}')
    # Theorem 3 and its table
    th = {8: (5, 140, 3328, 134, 3712), 9: (6, 201, 3402, 197, 3726)}
    for q, (al, m2, lo, m2b, best) in th.items():
        check(q ** 5 - al * q ** 4 - m2 * q * q == lo and q ** 5 - al * q ** 4 - m2b * q * q == best, f'Theorem 3 numbers q={q}')
    for q, al, lo, best in ((11, 7, 11253, 26862), (13, 8, 56446, 84162)):
        check(q ** 5 - al * q ** 4 - (8 * al * al - 1) * q * q == lo, f'Theorem 3 by hand q={q}')
        check(q ** 5 - al * q ** 4 - want_best[al] * q * q == best, f'Theorem 3 best pair q={q}')
    check(all(q * q * (q - (q + 3) // 2) > 8 * ((q + 3) // 2) ** 2 - 1 for q in range(10, 300)), 'Theorem 3: q >= 10 by hand')
    print('5. Lemma 5.6 and the route words (alpha = 5..8, all patterns): r4 >= alpha, starved pairs of both bars, '
          'largest m2 140, 201, 272, 353, best 134, 197, 262, 347; Theorem 3 numbers: checked')


# ------------------------------------------------------------------ 6. Lemma 5.2

def collineation(q, pts, lines, A):
    """x = (v, a, w), v = x0..x2, a = x3, w = x4..x6 -> (Av, a, A^-T w), A in SL(3,q)."""
    def det3(M):
        return (M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1]) - M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0])
                + M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0])) % q
    assert det3(A) == 1
    # inverse transpose: adjugate^T / det = cofactor matrix
    cof = [[((-1) ** (i + j)) * (A[(i + 1) % 3][(j + 1) % 3] * A[(i + 2) % 3][(j + 2) % 3]
                                  - A[(i + 1) % 3][(j + 2) % 3] * A[(i + 2) % 3][(j + 1) % 3]) % q for j in range(3)]
           for i in range(3)]
    # for 3x3 the cyclic cofactor formula already carries the sign; recompute plainly
    cof = [[0] * 3 for _ in range(3)]
    for i in range(3):
        for j in range(3):
            r = [x for x in range(3) if x != i]
            c = [x for x in range(3) if x != j]
            cof[i][j] = ((-1) ** (i + j) * (A[r[0]][c[0]] * A[r[1]][c[1]] - A[r[0]][c[1]] * A[r[1]][c[0]])) % q
    AinvT = cof                                        # det = 1
    pidx = {p: i for i, p in enumerate(pts)}

    def norm(v):
        i = next(i for i in range(7) if v[i] % q)
        cc = pow(v[i], q - 2, q)
        return tuple((x * cc) % q for x in v)

    def img(x):
        v, a, w = x[0:3], x[3], x[4:7]
        Av = [sum(A[i][j] * v[j] for j in range(3)) % q for i in range(3)]
        Bw = [sum(AinvT[i][j] * w[j] for j in range(3)) % q for i in range(3)]
        return norm(tuple(Av) + (a,) + tuple(Bw))
    pmap = [pidx[img(p)] for p in pts]
    lidx = {frozenset(pidx[p] for p in L): i for i, L in enumerate(lines)}
    lmap = [lidx.get(frozenset(pmap[pidx[p]] for p in L)) for L in lines]
    return pmap, lmap


def part6():
    q = 2
    N, edges, pts, lines = base_hexagon(q)
    rng = random.Random(6)
    # random elements of SL(3,2)
    mats = []
    while len(mats) < 10:
        A = [[rng.randrange(q) for _ in range(3)] for _ in range(3)]
        d = (A[0][0] * (A[1][1] * A[2][2] - A[1][2] * A[2][1]) - A[0][1] * (A[1][0] * A[2][2] - A[1][2] * A[2][0])
             + A[0][2] * (A[1][0] * A[2][1] - A[1][1] * A[2][0])) % q
        if d == 1:
            mats.append(A)
    maps = []
    for A in mats:
        pmap, lmap = collineation(q, pts, lines, A)
        check(None not in lmap and sorted(lmap) == list(range(N)), 'Fact 1.2: (Av, a, A^-T w) is a collineation of H(2)')
        maps.append((pmap, lmap))
    alpha, types = 2, 'ab'
    inner = readings(types)['reading 2']
    base_P, base_L = list(range(N)), list(range(N))
    g0, H0 = omega(N, edges, types, inner, [base_P] * 10, [base_L] * 10)
    P = [maps[c][0] for c in range(10)]
    L = [maps[c][1] for c in range(10)]
    g1, _ = omega(N, edges, types, inner, P, L)
    for bar in (0, 1):
        for k in range(5):
            h = H0 + 5 * bar + k
            p0 = sorted(g0.dist_from(h))
            p1 = sorted(g1.dist_from(h))
            check(p0 == p1, 'Lemma 5.2: same distance profile after relabelling every copy by a collineation')
    check(g1.diameter() == g0.diameter() == 9, 'Lemma 5.2: diameter unchanged (9)')
    print('6. Lemma 5.2 at q = 2: relabelling every copy by a collineation (Av, a, A^-T w) changes nothing; '
          'diameter 9: checked')


# ------------------------------------------------------------------ 7. the repair at q = 3

def part7():
    with open(HERE / 'omega_q3_base.txt') as f:
        nb = int(f.readline())
        edges = [tuple(map(int, l.split())) for l in f if l.strip()]
    N = nb // 2
    q = 3
    I = graph_from_edges(nb, edges)
    check(all(len(a) == q + 1 for a in I.adj) and I.bipartite(), 'audit base: 4-regular bipartite')
    for u in range(nb):
        d = I.dist_from(u)
        if [d.count(i) for i in range(7)] != [1] + [(q + 1) * q ** (i - 1) for i in range(1, 6)] + [q ** 5]:
            check(False, 'audit base: sphere sizes')
            break
    check(all((u < N) != (v < N) for u, v in edges), 'audit base: points 0..N-1, lines N..2N-1')
    types, inner = 'aba', 'L' * 15
    vals = list(map(int, open(HERE / 'omega_q3_aba_LLL_G13.lab').read().split()))
    C = 15
    check(len(vals) == 2 * C * N, 'labelling file size')
    P = [vals[c * N:(c + 1) * N] for c in range(C)]
    L = [vals[C * N + c * N:C * N + (c + 1) * N] for c in range(C)]
    check(all(sorted(P[c]) == list(range(N)) and sorted(L[c]) == list(range(N)) for c in range(C)), 'labelling: bijections')
    g, H0 = omega(N, edges, types, inner, P, L)
    degs = {len(a) for a in g.adj}
    check(g.n == 14560 and degs == {6} and g.bipartite(), 'the q = 3 relabelled structure: 14,560 elements, 6-regular')
    dm = g.diameter()
    check(dm == 8, f'the q = 3 relabelled structure: diameter {dm}')
    # how far the labelling is from the thesis labelling: transfers are not collineations
    same = sum(1 for c in range(C) for t in range(N) if P[c][t] == P[0][t])
    print(f'7. q = 3, pattern aba, reading 1, the audit labelling rebuilt here: {g.n} elements, degrees {sorted(degs)}, '
          f'diameter {dm} (point labels agreeing with copy 0: {same} of {C * N})')


def main():
    part1()
    part2_3()
    part4()
    part5()
    part6()
    part7()
    print('ALL CHECKS PASSED' if not FAIL else f'{len(FAIL)} FAILURES')


if __name__ == '__main__':
    main()
