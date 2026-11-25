r"""Checks for Section 7 of SYNTHETIC.tex (diameters 9 to 14: Haar structures).

Everything is written here from the definitions, without the lab's search or checking code.

  1. Haar structures (Definition 7.1): right multiplication is an automorphism group acting regularly on the
     points and on the lines; all degrees are Delta.
  2. Lemma 7.3 (two searches): on random S in small groups (SL(2,3), SL(2,5) x Z_3, PSL(2,7), S_4, D_12,
     metacyclic Z_31 x|_5 Z_3, Z_7 x|_2 Z_9), the exact diameter (all pairs) equals the larger of the
     eccentricities of the point e and the line e; diameter <= D iff the word conditions hold (one condition
     for even D, two for odd D); an example where the two odd-D conditions differ (Z13 x|_3 Z3, D = 7).
  3. Isomorphisms: S -> S s0^-1 and S -> phi(S) (phi an automorphism) give isomorphic structures.
  4. Singer: the Haar structure of Z_(q^2+q+1) with a perfect difference set is a projective plane (q = 2..5).
  5. Counting: the number of reduced alternating words of length l is Delta (Delta-1)^(l-1) (enumerated), and
     W(Delta, D) = M_b(Delta, D)/2 for Delta = 3..20, D = 3..14.
  6. Orbit symmetry (Section 7.4): S invariant under an automorphism alpha of order 3 of SL(2,p) x Z_n; alpha is
     an automorphism of the structure fixing the point e and the line e; the far elements form a union of alpha-orbits.
     Odd-D lemma: (S^-1 S)^h is inverse-closed, and a central element lies in (S^-1 S)^h iff in (S S^-1)^h.
  7. Values rebuilt from their solution files (two searches, Lemma 7.3), and (3,11) from its group; the edge lists of
     the Delta = 3 values by an all-pairs search (no symmetry used), the (3,11) edge list against its group, and the
     quotients of the (3,13), (3,14) lifts; alpha found from S for every symmetric S containing e in SL(2,p) or
     PSL(2,p) times a cyclic group (p prime), with f and k checked against the values list, and the field
     automorphism of (11,10) checked.
  8. The values table and Appendix B: every value agrees with its file, the orbit shapes add up to Delta, every prime
     factor of n is 1 mod k, the tables in SYNTHETIC.tex are generated from the list here (python3 check_haar.py --tables
     prints them), and the size-law numbers of Section 7.3 (W, lambda = W/N, mu = N e^-lambda, 2N/M_b).

Run: python3 check_haar.py      (a few minutes)
"""
import gzip
import itertools
import math
import os
import random
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
SOLS = os.path.join(REPO, 'research', 'frontier', 'sols')
OWN = os.path.join(HERE, 'haar')
GRAPHS = os.path.join(REPO, 'research', 'frontier', 'beyond', 'graphs')
LIFTS = os.path.join(REPO, 'research', 'lifts', 'sols')
rng = random.Random(20261101)


def ok(cond, msg):
    if not cond:
        print('FAILED:', msg)
        sys.exit(1)


# ------------------------------------------------------------------ small groups as multiplication tables
class Group:
    """A finite group given by a list of elements and a product; elements are indexed 0..N-1, e = index 0."""

    def __init__(self, name, elems, mul, e):
        self.name = name
        self.el = list(elems)
        self.idx = {g: i for i, g in enumerate(self.el)}
        ok(e in self.idx, name + ': identity missing')
        i0 = self.idx[e]
        self.el[0], self.el[i0] = self.el[i0], self.el[0]
        self.idx = {g: i for i, g in enumerate(self.el)}
        n = len(self.el)
        self.n = n
        self.M = np.zeros((n, n), dtype=np.int32)
        for i, a in enumerate(self.el):
            for j, b in enumerate(self.el):
                self.M[i, j] = self.idx[mul(a, b)]
        self.inv = np.array([int(np.where(self.M[i] == 0)[0][0]) for i in range(n)], dtype=np.int32)
        # sanity: associativity on a sample
        for _ in range(200):
            a, b, c = (rng.randrange(n) for _ in range(3))
            ok(self.M[self.M[a, b], c] == self.M[a, self.M[b, c]], name + ': not associative')

    def mul(self, a, b):
        return int(self.M[a, b])

    def center(self):
        return [z for z in range(self.n) if all(self.M[z, g] == self.M[g, z] for g in range(self.n))]


def mat_group(p, proj=False, cyc=1):
    def norm(m):
        m = tuple(x % p for x in m)
        if proj:
            mm = tuple((-x) % p for x in m)
            return min(m, mm)
        return m
    els = set()
    for a, b, c, d in itertools.product(range(p), repeat=4):
        if (a * d - b * c) % p == 1:
            for z in range(cyc):
                els.add((norm((a, b, c, d)), z))

    def mul(x, y):
        (a, b, c, d), z = x
        (e, f, g, h), w = y
        return (norm((a * e + b * g, a * f + b * h, c * e + d * g, c * f + d * h)), (z + w) % cyc)
    name = ('PSL' if proj else 'SL') + f'(2,{p})' + (f' x Z{cyc}' if cyc > 1 else '')
    return Group(name, els, mul, (norm((1, 0, 0, 1)), 0))


def perm_group_S4():
    els = list(itertools.permutations(range(4)))
    return Group('S4', els, lambda a, b: tuple(a[b[i]] for i in range(4)), (0, 1, 2, 3))


def dihedral(n):
    els = [(r, f) for r in range(n) for f in range(2)]
    return Group(f'D{2 * n}', els, lambda a, b: ((a[0] + (b[0] if a[1] == 0 else -b[0])) % n, (a[1] + b[1]) % 2),
                 (0, 0))


def metacyclic(m, k, r):
    ok(pow(r, k, m) == 1, 'r^k != 1 mod m')
    els = [(a, j) for a in range(m) for j in range(k)]
    return Group(f'Z{m} x|_{r} Z{k}', els, lambda x, y: ((x[0] + pow(r, x[1], m) * y[0]) % m, (x[1] + y[1]) % k),
                 (0, 0))


# ------------------------------------------------------------------ Haar structures on small groups
def haar_flags(G, S):
    """Points ('p', g), lines ('L', h); p_g I L_h iff h g^-1 in S, i.e. h = s g."""
    return {(('p', g), ('L', G.mul(s, g))) for g in range(G.n) for s in S}


def bfs(adj, src):
    dist = {src: 0}
    fr = [src]
    while fr:
        nx = []
        for u in fr:
            for v in adj[u]:
                if v not in dist:
                    dist[v] = dist[u] + 1
                    nx.append(v)
        fr = nx
    return dist


def adjacency(flags):
    adj = {}
    for p, L in flags:
        adj.setdefault(p, []).append(L)
        adj.setdefault(L, []).append(p)
    return adj


def ecc(adj, src, nverts):
    d = bfs(adj, src)
    return max(d.values()) if len(d) == nverts else math.inf


def products(G, A, B):
    return {G.mul(a, b) for a in A for b in B}


def word_sets(G, S, kmax):
    """X_A[k] = (S^-1 S)^k, X_B[k] = (S S^-1)^k, Y[k] = S (S^-1 S)^k (e in S, so nested)."""
    Sinv = [int(G.inv[s]) for s in S]
    SiS = products(G, Sinv, S)
    SSi = products(G, S, Sinv)
    XA, XB, Y = [{0}], [{0}], [set(S)]
    for _ in range(kmax):
        XA.append(products(G, SiS, XA[-1]))
        XB.append(products(G, SSi, XB[-1]))
        Y.append(products(G, S, products(G, Sinv, Y[-1])))
    return XA, XB, Y


def check_haar_lemmas():
    groups = [mat_group(3), mat_group(5, cyc=3), mat_group(7, proj=True), perm_group_S4(), dihedral(6),
              metacyclic(31, 3, 5), metacyclic(7, 9, 2)]
    ntests = 0
    for G in groups:
        for Delta in (2, 3, 4):
            if Delta >= G.n:
                continue
            for _ in range(6):
                S = [0] + rng.sample(range(1, G.n), Delta - 1)
                flags = haar_flags(G, S)
                # 1. right multiplication by every x preserves the flags; regular on points and on lines
                for x in range(G.n):
                    img = {(('p', G.mul(g, x)), ('L', G.mul(h, x))) for (_, g), (_, h) in flags}
                    ok(img == flags, f'{G.name}: right multiplication is not an automorphism')
                lines_e = sorted(h for (_, g), (_, h) in flags if g == 0)
                ok(lines_e == sorted(S), 'the lines through the point e are the lines s, s in S')
                ok(len(flags) == Delta * G.n, 'degrees')
                adj = adjacency(flags)
                nv = 2 * G.n
                eA, eB = ecc(adj, ('p', 0), nv), ecc(adj, ('L', 0), nv)
                diam = max(ecc(adj, v, nv) for v in adj)
                ok(diam == max(eA, eB), f'{G.name}: diameter {diam} != max ecc {eA}, {eB}')
                XA, XB, Y = word_sets(G, S, 12)
                full = set(range(G.n))
                for D in range(2, 15):
                    if D % 2 == 0:
                        cond = Y[D // 2 - 1] == full
                        # even D: one search from the point e: every line within D-1
                        d = bfs(adj, ('p', 0))
                        one = all(d.get(('L', h), math.inf) <= D - 1 for h in range(G.n))
                        ok(cond == one, 'even D: word condition vs one search')
                    else:
                        h = (D - 1) // 2
                        cond = XA[h] == full and XB[h] == full
                    ok(cond == (diam <= D), f'{G.name} D={D}: word condition {cond} but diameter {diam}')
                ntests += 1
    print(f'1-2. right multiplication regular on points and lines; exact diameter = max(ecc(point e), ecc(line e)); '
          f'word conditions (one for even D, two for odd D) agree with the diameter for D = 2..14: {ntests} '
          'random (G, S): checked')
    # the two odd-D conditions can differ (found by an exhaustive search over small groups and |S| <= 3)
    G = metacyclic(13, 3, 3)
    S = [G.idx[(0, 0)], G.idx[(0, 1)], G.idx[(1, 0)]]
    XA, XB, _ = word_sets(G, S, 3)
    adj = adjacency(haar_flags(G, S))
    eA, eB = ecc(adj, ('p', 0), 2 * G.n), ecc(adj, ('L', 0), 2 * G.n)
    ok(len(XA[3]) == 37 and len(XB[3]) == 39 and (eA, eB) == (8, 7), 'odd-D example')
    print(f'   the two odd-D conditions differ: Z13 x|_3 Z3, S = {{(0,0), (0,1), (1,0)}}, D = 7: '
          f'|(S^-1 S)^3| = 37 < 39 = |(S S^-1)^3|; eccentricity {eA} from the point e, {eB} from the line e')


def check_isomorphisms():
    G = mat_group(5, cyc=3)
    for _ in range(10):
        S = [0] + rng.sample(range(1, G.n), 3)
        s0 = rng.choice(S)
        T = [G.mul(s, int(G.inv[s0])) for s in S]
        F1 = haar_flags(G, S)
        F2 = haar_flags(G, T)
        # (g, A) -> (s0 g, A), (h, B) -> (h, B) maps H(G,S) onto H(G, S s0^-1)
        img = {(('p', G.mul(s0, g)), ('L', h)) for (_, g), (_, h) in F1}
        ok(img == F2, 'S -> S s0^-1 is not an isomorphism')
        # phi = conjugation by a random element: H(G,S) -> H(G, phi(S)) by g -> phi(g) on both sides
        c = rng.randrange(G.n)
        phi = lambda g: G.mul(G.mul(c, g), int(G.inv[c]))
        F3 = haar_flags(G, [phi(s) for s in S])
        ok({(('p', phi(g)), ('L', phi(h))) for (_, g), (_, h) in F1} == F3, 'phi is not an isomorphism')
    print('3. H(G,S) = H(G, S s0^-1) and H(G,S) = H(G, phi(S)) (phi conjugation) as incidence structures: checked')


def check_singer():
    for q in (2, 3, 4, 5):
        v = q * q + q + 1
        found = None
        for S in itertools.combinations(range(1, v), q):
            S = (0,) + S
            diffs = sorted((a - b) % v for a in S for b in S if a != b)
            if diffs == list(range(1, v)):
                found = S
                break
        ok(found is not None, f'no difference set for q = {q}')
        G = Group(f'Z{v}', range(v), lambda a, b: (a + b) % v, 0)
        flags = haar_flags(G, list(found))
        adj = adjacency(flags)
        # projective plane: two points on exactly one line, two lines meet in exactly one point
        lines_on = {g: {h for (_, x), (_, h) in flags if x == g} for g in range(v)}
        pts_on = {h: {x for (_, x), (_, y) in flags if y == h} for h in range(v)}
        ok(all(len(lines_on[a] & lines_on[b]) == 1 for a in range(v) for b in range(a + 1, v)), 'two points')
        ok(all(len(pts_on[a] & pts_on[b]) == 1 for a in range(v) for b in range(a + 1, v)), 'two lines')
        ok(v == W(q + 1, 3), 'Singer: N = W')
    print('4. Singer difference sets in Z7, Z13, Z21, Z31: the Haar structures are projective planes of order '
          '2, 3, 4, 5 with N = W(q+1, 3): checked')


# ------------------------------------------------------------------ counting
def W(d, D):
    if D % 2:
        k = (D - 1) // 2
        return 1 + sum(d * (d - 1) ** (2 * i - 1) for i in range(1, k + 1))
    k = D // 2
    return d * sum((d - 1) ** (2 * i) for i in range(k))


def moore(d, D):
    return 2 * sum((d - 1) ** i for i in range(D))


def check_counting():
    # reduced alternating words: s1, s2^-1 s1, ... with s_{i+1} != s_i, counted by enumeration
    for d in (3, 4, 5):
        for l in range(1, 7):
            cnt = sum(1 for w in itertools.product(range(d), repeat=l) if all(w[i] != w[i + 1] for i in range(l - 1)))
            ok(cnt == d * (d - 1) ** (l - 1), 'word count')
    for d in range(3, 21):
        for D in range(3, 15):
            ok(2 * W(d, D) == moore(d, D), f'W != M_b/2 at {d},{D}')
    print('5. reduced words of length l: Delta (Delta-1)^(l-1) (enumerated, Delta = 3..5, l <= 6); '
          'W(Delta, D) = M_b(Delta, D)/2 for Delta = 3..20, D = 3..14: checked')


# ------------------------------------------------------------------ orbit symmetry
def check_orbits():
    p, n, r = 7, 7, 2          # SL(2,7) x Z7, alpha = conjugation by an element of order 3, z -> 2z
    G = mat_group(p, cyc=n)
    t = next(i for i, (m, z) in enumerate(G.el)
             if z == 0 and i != 0 and G.mul(i, G.mul(i, i)) == 0)
    tinv = int(G.inv[t])

    def alpha(g):
        x = G.mul(G.mul(t, g), tinv)
        m, z = G.el[x]
        return G.idx[(m, (r * z) % n)]
    ok(all(alpha(alpha(alpha(g))) == g for g in range(G.n)), 'alpha has order 3')
    ok(all(alpha(G.mul(a, b)) == G.mul(alpha(a), alpha(b)) for a in rng.sample(range(G.n), 60)
           for b in rng.sample(range(G.n), 60)), 'alpha is a homomorphism')
    fixed = [g for g in range(G.n) if alpha(g) == g]
    free = [g for g in range(G.n) if alpha(g) != g]
    nholes_seen = 0
    for Delta, m in ((4, 1), (7, 2)):
        for _ in range(4):
            S = [0] + [g for x in rng.sample(free, m) for g in (x, alpha(x), alpha(alpha(x)))]
            if len(set(S)) != Delta:
                continue
            ok(sorted(alpha(s) for s in S) == sorted(S), 'S not alpha-invariant')
            flags = haar_flags(G, S)
            ok({(('p', alpha(g)), ('L', alpha(h))) for (_, g), (_, h) in flags} == flags, 'alpha not an automorphism')
            adj = adjacency(flags)
            dA, dB = bfs(adj, ('p', 0)), bfs(adj, ('L', 0))
            for rho in range(0, 10):   # balls about the point e and the line e are alpha-invariant
                for dist in (dA, dB):
                    for kind in ('p', 'L'):
                        far = {g for g in range(G.n) if dist.get((kind, g), 99) > rho}
                        ok({alpha(g) for g in far} == far, 'far set not alpha-invariant')
                        nholes_seen += len(far)
            XA, XB, _ = word_sets(G, S, 6)
            Z = G.center()
            for h in range(1, 6):
                ok({int(G.inv[x]) for x in XA[h]} == XA[h], '(S^-1 S)^h not inverse-closed')
                ok(all((c in XA[h]) == (c in XB[h]) for c in Z), 'central element on one side only')
    print(f'6. SL(2,7) x Z7 with alpha = (conjugation by an element of order 3) x (z -> 2z): |Fix(alpha)| = '
          f'{len(fixed)}; random alpha-invariant S (Delta = 4, 7): alpha is an automorphism fixing the point e and the '
          f'line e, the elements at distance more than rho from the point e or the line e form a union of alpha-orbits '
          f'(rho = 0..9; {nholes_seen} far elements seen), (S^-1 S)^h is '
          'inverse-closed, central elements are far on both sides or on neither: checked')


# ------------------------------------------------------------------ records rebuilt from solution files
def read_sol(path):
    with open(path) as f:
        head = f.readline().split()
        gens = [ln.split(None, 1)[1].strip() for ln in f if ln.strip()]
    return head, gens


class Field:
    """GF(q), q = p^k, as GF(p)[x]/(f); element code = sum c_i p^i (the lab's file convention).  add, mul, neg as
    numpy tables."""

    def __init__(self, q, poly=None):
        p = next(t for t in range(2, q + 1) if q % t == 0)
        k = round(math.log(q, p))
        ok(p ** k == q, 'q not a prime power')
        self.q, self.p = q, p
        if k == 1:
            x = np.arange(q)
            self.add = (x[:, None] + x[None, :]) % q
            self.mul = (x[:, None] * x[None, :]) % q
        else:
            f = {0: 0}
            for term in poly.split('+'):          # e.g. x^2+2, x^5+2x+1
                c, _, e = term.partition('x')
                coef = int(c) if c else 1
                expo = (int(e[1:]) if e.startswith('^') else 1) if 'x' in term else 0
                if 'x' not in term:
                    coef = int(term)
                f[expo] = (f.get(expo, 0) + coef) % p
            fv = [f.get(i, 0) for i in range(k + 1)]
            ok(fv[k] == 1, 'monic')
            dig = [[(c // p ** i) % p for i in range(k)] for c in range(q)]
            enc = lambda v: sum(x * p ** i for i, x in enumerate(v))
            self.add = np.array([[enc([(x + y) % p for x, y in zip(dig[u], dig[v])]) for v in range(q)] for u in range(q)])
            mul = np.zeros((q, q), dtype=np.int64)
            for u in range(q):
                for v in range(q):
                    r = [0] * (2 * k - 1)
                    for i in range(k):
                        for j in range(k):
                            r[i + j] = (r[i + j] + dig[u][i] * dig[v][j]) % p
                    for i in range(2 * k - 2, k - 1, -1):
                        t = r[i]
                        if t:
                            for j in range(k + 1):
                                r[i - k + j] = (r[i - k + j] - t * fv[j]) % p
                    mul[u, v] = enc(r[:k])
            self.mul = mul
            # a field: every nonzero element invertible
            ok(all((mul[u] == 1).any() for u in range(1, q)), 'not a field')
        self.neg = np.array([int(np.where(self.add[u] == 0)[0][0]) for u in range(q)])


class Factor:
    """One factor of G: 'meta m k r' (Z_m x|_r Z_k, (a,j)(b,l) = (a + r^j b, j + l)) or 'sl q' / 'psl q' [poly f]
    (2x2 matrices over GF(q) with determinant 1, modulo +-I for psl).  Elements are indexed 0..size-1;
    left(s) is the permutation x -> s x of the indices."""

    def __init__(self, toks):
        self.kind = toks[0]
        if self.kind == 'meta':
            m, k, r = int(toks[1]), int(toks[2]), int(toks[3])
            ok(pow(r, k, m) == 1, 'meta: r^k != 1 mod m')
            self.m, self.k = m, k
            self.size = m * k
            self.a = np.repeat(np.arange(m, dtype=np.int64), k)
            self.j = np.tile(np.arange(k, dtype=np.int64), m)
            self.rp = np.array([pow(r, t, m) for t in range(k)], dtype=np.int64)
            self.e = 0
            self.ntok = 4
        else:
            q = int(toks[1])
            poly = toks[3] if len(toks) > 3 and toks[2] == 'poly' else None
            self.ntok = 4 if poly else 2
            F = self.F = Field(q, poly)
            self.q, self.proj = q, self.kind == 'psl'
            A, B, C, Dd = (x.ravel() for x in np.meshgrid(*[np.arange(q, dtype=np.int64)] * 4, indexing='ij'))
            det = F.add[F.mul[A, Dd], F.neg[F.mul[B, C]]]
            A, B, C, Dd = A[det == 1], B[det == 1], C[det == 1], Dd[det == 1]
            codes = np.unique(self.code(A, B, C, Dd))
            ok(len(codes) == q * (q * q - 1) // (2 if self.proj and q % 2 else 1), 'group order')
            self.codes, self.size = codes, len(codes)
            self.aa, self.bb, self.cc, self.dd = codes // q ** 3, codes // q ** 2 % q, codes // q % q, codes % q
            self.e = int(np.searchsorted(codes, self.code(np.int64(1), 0, 0, 1)))

    def code(self, a, b, c, d):
        q = self.q
        c1 = ((a * q + b) * q + c) * q + d
        if self.proj and q % 2:
            n = self.F.neg
            c2 = ((n[a] * q + n[b]) * q + n[c]) * q + n[d]
            return np.minimum(c1, c2)
        return c1

    def parse(self, desc):
        if self.kind == 'meta':
            return int(desc.split('a=')[1].split(',')[0]), int(desc.split('j=')[1].split(')')[0])
        return tuple(int(x) for x in desc.split('(')[1].split(')')[0].split(','))

    def left(self, s):
        if self.kind == 'meta':
            sa, sj = s
            return ((sa + self.rp[sj] * self.a) % self.m) * self.k + (sj + self.j) % self.k
        F = self.F
        sa, sb, sc, sd = s
        na, nb = F.add[F.mul[sa, self.aa], F.mul[sb, self.cc]], F.add[F.mul[sa, self.bb], F.mul[sb, self.dd]]
        nc, nd = F.add[F.mul[sc, self.aa], F.mul[sd, self.cc]], F.add[F.mul[sc, self.bb], F.mul[sd, self.dd]]
        return np.searchsorted(self.codes, self.code(na, nb, nc, nd))

    def inv(self, s):
        if self.kind == 'meta':
            sa, sj = s
            ij = (-sj) % self.k
            return ((-int(self.rp[ij]) * sa) % self.m, ij)
        n = self.F.neg
        sa, sb, sc, sd = s
        return (sd, int(n[sb]), int(n[sc]), sa)


class BigGroup:
    """G = F_1 x ... x F_r x Z_n from a solution-file header ('meta ...', 'sl q [poly f]', 'psl q ...', 'prod X Y'),
    elements indexed ((i_1 |F_2| + i_2) ...) n + z.  left(s) is the permutation g -> s g; e is the identity."""

    def __init__(self, head):
        self.d, self.D = int(head[0]), int(head[1])
        toks = head[2:head.index('n')]
        if toks[0] == 'prod':
            toks = toks[1:]
        self.factors = []
        while toks:
            f = Factor(toks)
            self.factors.append(f)
            toks = toks[f.ntok:]
        self.n = int(head[head.index('n') + 1])
        sizes = [f.size for f in self.factors]
        self.N = int(np.prod(sizes)) * self.n
        ok(self.N == int(head[head.index('N') + 1]), 'N in the header')
        # index arrays of each coordinate
        shape = sizes + [self.n]
        grids = np.indices(shape, dtype=np.int64).reshape(len(shape), -1) if self.N <= 2 * 10 ** 7 else None
        ok(grids is not None, 'group too large for this check')
        self.coord = grids
        self.shape = shape
        self.e = int(np.ravel_multi_index([f.e for f in self.factors] + [0], shape))
        self.fam = 'meta' if all(f.kind == 'meta' for f in self.factors) else 'mat'

    def parse(self, desc):
        z = int(desc.split('z=')[1])
        if desc.startswith('prod['):
            parts = desc[5:desc.index(']')].split(';')
        else:
            parts = [desc.split(' z=')[0]]
        ok(len(parts) == len(self.factors), 'generator format')
        return tuple(f.parse(x) for f, x in zip(self.factors, parts)) + (z,)

    def left(self, s):
        cols = [f.left(x)[self.coord[i]] for i, (f, x) in enumerate(zip(self.factors, s[:-1]))]
        cols.append((self.coord[-1] + s[-1]) % self.n)
        return np.ravel_multi_index(cols, self.shape)

    def inv(self, s):
        return tuple(f.inv(x) for f, x in zip(self.factors, s[:-1])) + ((-s[-1]) % self.n,)


def eccentricity(fwd, bwd, N, e, start):
    """BFS in H(G,S) from the point e (start 'p') or the line e (start 'L'); fwd[k]: g -> s_k g (point g to line
    s_k g), bwd[k]: h -> s_k^-1 h (line h to point s_k^-1 h).  Returns the eccentricity, or None if some
    vertex is not reached."""
    pts, lns = np.zeros(N, dtype=bool), np.zeros(N, dtype=bool)
    kind = start
    (pts if kind == 'p' else lns)[e] = True
    fr = np.array([e], dtype=np.int64)
    level = 0
    while True:
        maps, seen = (fwd, lns) if kind == 'p' else (bwd, pts)
        nxt = np.unique(np.concatenate([mp[fr] for mp in maps]))
        nxt = nxt[~seen[nxt]]
        if len(nxt) == 0:
            break
        seen[nxt] = True
        fr, kind, level = nxt, ('L' if kind == 'p' else 'p'), level + 1
    return level if pts.all() and lns.all() else None


def check_record(path, head=None, gens=None):
    if head is None:
        head, gens = read_sol(path)
    G = BigGroup(head)
    S = [G.parse(g) for g in gens]
    ok(len(S) == G.d, 'number of generators')
    fwd = [G.left(s) for s in S]
    bwd = [G.left(G.inv(s)) for s in S]
    for k in range(G.d):
        ok(np.array_equal(bwd[k][fwd[k]], np.arange(G.N)), 's^-1 s != e')
    ok(len({int(f[G.e]) for f in fwd}) == G.d, 'generators not distinct')
    eA = eccentricity(fwd, bwd, G.N, G.e, 'p')
    eB = eccentricity(fwd, bwd, G.N, G.e, 'L')
    ok(eA is not None and eB is not None and max(eA, eB) == G.D,
       f'{os.path.basename(path)}: eccentricities {eA}, {eB}, D = {G.D}')
    return G, S, eA, eB


def nullspace_mod_p(rows, p):
    """Basis of the solutions x of rows . x = 0 over GF(p) (rows: list of length-4 lists)."""
    A = [list(r) for r in rows]
    ncol = 4
    piv = []
    rk = 0
    for c in range(ncol):
        pr = next((i for i in range(rk, len(A)) if A[i][c] % p), None)
        if pr is None:
            continue
        A[rk], A[pr] = A[pr], A[rk]
        iv = pow(A[rk][c], p - 2, p)
        A[rk] = [x * iv % p for x in A[rk]]
        for i in range(len(A)):
            if i != rk and A[i][c] % p:
                f = A[i][c]
                A[i] = [(x - f * y) % p for x, y in zip(A[i], A[rk])]
        piv.append(c)
        rk += 1
    free = [c for c in range(ncol) if c not in piv]
    basis = []
    for fc in free:
        v = [0] * ncol
        v[fc] = 1
        for i, c in enumerate(piv):
            v[c] = (-A[i][fc]) % p
        basis.append(v)
    return basis


def orbit_alpha(path, k=3):
    """For an SL/PSL(2,p) x Z_n orbit solution with e in S: find alpha = (conjugation by t in GL(2,p)) x (z -> r z)
    of order 3 with alpha(S) = S, by linear algebra (t x = +-y t for the pairs x -> y forced by the z-parts).
    Returns (t, r, number of alpha-fixed generators) or None.  No search over the group."""
    head, gens = read_sol(path)
    p, n = int(head[3]), int(head[head.index('n') + 1])
    proj = head[2] == 'psl'
    S = []
    for g in gens:
        m = tuple(int(x) % p for x in g.split('mat(')[1].split(')')[0].split(','))
        S.append((m, int(g.split('z=')[1])))

    def norm(m):
        m = tuple(x % p for x in m)
        return min(m, tuple((-x) % p for x in m)) if proj else m

    def mm(x, y):
        return ((x[0] * y[0] + x[1] * y[2]) % p, (x[0] * y[1] + x[1] * y[3]) % p,
                (x[2] * y[0] + x[3] * y[2]) % p, (x[2] * y[1] + x[3] * y[3]) % p)
    Sset = {(norm(m), z) for m, z in S}
    signs = (1, -1) if proj else (1,)

    def rows_for(x, y):
        # (t x)_{ij} - (y t)_{ij} = 0 for t = [[a, b], [c, d]], linear in (a, b, c, d)
        return [[x[0] - y[0], x[2], -y[1], 0], [x[1], x[3] - y[0], 0, -y[1]],
                [-y[2], 0, x[0] - y[3], x[2]], [0, -y[2], x[1], x[3] - y[3]]]

    def candidates_t(basis):
        if len(basis) == 1:
            yield tuple(basis[0])
        elif len(basis) == 2:
            for u in range(p):
                yield tuple((x + u * y) % p for x, y in zip(basis[0], basis[1]))
            yield tuple(basis[1])

    for r in ([r for r in range(2, n) if pow(r, k, n) == 1] if n > 1 else [0]):
        cands = [[m2 for m2, z2 in S if z2 == (r * z) % n] for m, z in S]
        if any(not c for c in cands):
            continue
        # depth-first over the image of each generator (and its sign in PSL), pruning on an empty solution space
        stack = [(0, [])]
        while stack:
            i, rows = stack.pop()
            basis = nullspace_mod_p(rows, p) if rows else [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]]
            if not basis:
                continue
            if i == len(S) or len(basis) <= 2 and i >= 3:
                for t in candidates_t(basis) if len(basis) <= 2 else []:
                    det = (t[0] * t[3] - t[1] * t[2]) % p
                    if det == 0 or (t[1] == t[2] == 0 and t[0] == t[3]):
                        continue
                    tk = t
                    for _ in range(k - 1):
                        tk = mm(tk, t)
                    if not (tk[1] == tk[2] == 0 and tk[0] == tk[3]):   # t^k scalar: conjugation of order k
                        continue
                    di = pow(det, p - 2, p)
                    ti = (t[3] * di % p, (-t[1]) * di % p, (-t[2]) * di % p, t[0] * di % p)
                    img = {(norm(mm(mm(t, m), ti)), (r * z) % n) for m, z in S}
                    if img == Sset:
                        fixed = sum(1 for m, z in S if (norm(mm(mm(t, m), ti)), (r * z) % n) == (norm(m), z))
                        return t, r, fixed
                if i == len(S):
                    continue
            x = S[i][0]
            for y in cands[i]:
                for sg in signs:
                    stack.append((i + 1, rows + rows_for(x, tuple(sg * v for v in y))))
    return None


def isomorphic(E1, E2, n):
    """Backtracking isomorphism test for two small graphs on 0..n-1 given as sets of 2-sets."""
    A1 = [set() for _ in range(n)]
    A2 = [set() for _ in range(n)]
    for e in E1:
        u, v = tuple(e)
        A1[u].add(v)
        A1[v].add(u)
    for e in E2:
        u, v = tuple(e)
        A2[u].add(v)
        A2[v].add(u)
    if len(E1) != len(E2) or sorted(map(len, A1)) != sorted(map(len, A2)):
        return False
    order = []
    seen = set()
    for s in range(n):                     # BFS order so that each new vertex has a mapped neighbour
        if s in seen:
            continue
        q = [s]
        seen.add(s)
        while q:
            u = q.pop(0)
            order.append(u)
            for v in sorted(A1[u]):
                if v not in seen:
                    seen.add(v)
                    q.append(v)
    f = {}

    def ext(i):
        if i == n:
            return True
        u = order[i]
        used = set(f.values())
        for w in range(n):
            if w in used or len(A2[w]) != len(A1[u]):
                continue
            if all((f[x] in A2[w]) == (x in A1[u]) for x in f):
                f[u] = w
                if ext(i + 1):
                    return True
                del f[u]
        return False
    return ext(0)


def apsp_cubic(path, D):
    """All-pairs check of an edge list (first line n, then 'u v'): bipartite, degrees, every distance <= D,
    exact diameter.  Distances by boolean reachability matrices, no symmetry used."""
    with gzip.open(path, 'rt') if path.endswith('.gz') else open(path) as f:
        n = int(f.readline())
        E = np.array([list(map(int, ln.split())) for ln in f if ln.strip()], dtype=np.int64)
    nb = [[] for _ in range(n)]
    for u, v in E:
        nb[u].append(v)
        nb[v].append(u)
    degs = {len(x) for x in nb}
    ok(len({(min(u, v), max(u, v)) for u, v in E}) == len(E), 'repeated edge')
    # bipartite colouring
    col = [-1] * n
    col[0] = 0
    st = [0]
    while st:
        u = st.pop()
        for v in nb[u]:
            if col[v] < 0:
                col[v] = 1 - col[u]
                st.append(v)
            ok(col[v] != col[u], 'not bipartite')
    ok(min(col) >= 0, 'not connected')
    dmax = max(degs)
    NB = np.array([x + [x[0]] * (dmax - len(x)) for x in nb], dtype=np.int64)
    R = np.eye(n, dtype=bool)
    diam = 0
    while not R.all():
        R2 = R.copy()
        for c in range(dmax):
            R2 |= R[:, NB[:, c]]
        diam += 1
        ok(diam <= 3 * D, 'no convergence')
        R = R2
    return n, sorted(degs), diam


def check_records():
    files = [(SOLS, 'd5D9_meta_346_43_29_s613_n29756.txt'), (SOLS, 'd6D9_sl_17_13_orb3f0_s2.txt'),
             (SOLS, 'd7D9_psl_29_19_orb3_s1.txt'), (SOLS, 'd8D9_sl_25_43_orb3_s1.txt'),
             (SOLS, 'd6D10_prod_sl_5_psl_7_13_orb3f0_s1.txt'), (SOLS, 'd4D11_meta_523_29_9_b2h01.txt'),
             (SOLS, 'd5D11_meta_5023_31_2886_b5k05.txt'), (SOLS, 'd6D11_meta_20809_51_12972_b5k07.txt'),
             (SOLS, 'd4D12_meta_731_48_7_b5k02.txt'), (OWN, 'd4D12_meta_1277_29_964_h08.txt'),
             (SOLS, 'd5D12_meta_8969_59_205_b6l03.txt'), (OWN, 'd4D13_meta_2237_43_1984_h03.txt'),
             (OWN, 'd4D14_meta_2731_91_i04.txt'), (OWN, 'd5D13_prodmeta_11_5_2971_11_i06.txt'),
             (OWN, 'd5D14_meta_148781_43_i07.txt'),
             (LIFTS, 'd4D10_n12416_haar_meta97_64_19.txt'), (LIFTS, 'd5D10_n95472_haar_meta1989_24_461.txt')]
    for d, f in files:
        head = gens = None
        if d == LIFTS:     # research/lifts format: 'lift D .. Delta ..', 'group meta m k r', edges 'e 0 1 = a,j'
            lines = open(os.path.join(d, f)).read().split('\n')
            hd = next(ln for ln in lines if ln.startswith('lift')).split()
            gr = next(ln for ln in lines if ln.startswith('group')).split()[1:]
            gl = [ln.split('=')[1].strip().split(',') for ln in lines if ln.startswith('e 0 1')]
            gens = [f'meta(a={a},j={j}) z=0' for a, j in gl]
            m, k = int(gr[1]), int(gr[2])
            head = [hd[4], hd[2]] + gr + ['n', '1', 'N', str(m * k)]
        G, S, eA, eB = check_record(os.path.join(d, f), head, gens)
        extra = ''
        # orbit solutions with e in S (f >= 1): S itself is alpha-invariant.  For f = 0 the file stores S s0^-1
        # (Section 7.1), which is not, so those are only checked for the diameter.
        if f == 'd7D9_psl_29_19_orb3_s1.txt':
            a = orbit_alpha(os.path.join(d, f))
            ok(a is not None, f + ': no order-3 automorphism of the expected form maps S onto S')
            t, r, fx = a
            extra = f'; S is mapped onto itself by (conjugation by {t}) x (z -> {r} z), fixing {fx} of the generators'
        print(f'7. {f}: {G.d}-regular, {2 * G.N:,} vertices, eccentricity {eA} from the point e and {eB} from '
              f'the line e, diameter {max(eA, eB)}{extra}: checked')
    lifts = [(os.path.join(REPO, 'research/squads/own-small/records/d3D10_n810_c3xheis27.edges'), 10),
             (os.path.join(OWN, 'd3D11_n1474_meta67_11_9.edges.gz'), 11),
             (os.path.join(REPO, 'research/squads/own-small/records/d3D12_n2368_meta37_8.edges'), 12),
             (os.path.join(GRAPHS, 'd3D13_n3400_lift_gp10_Z170.edges.gz'), 13),
             (os.path.join(GRAPHS, 'd3D14_n5706_lift_pappus_Z317.edges.gz'), 14)]
    for path, D in lifts:
        n, degs, diam = apsp_cubic(path, D)
        ok(degs == [3] and diam == D, f'{path}: degrees {degs}, diameter {diam}')
        print(f'7. {os.path.basename(path)}: {n:,} vertices, cubic, bipartite, diameter {diam} (all pairs): checked')
    # the two cyclic lifts: vertex b*m + i is (base vertex b, i in Z_m); i -> i+1 is an automorphism and the
    # quotient is the Desargues graph GP(10,3) or the Pappus graph
    desargues = {frozenset(e) for i in range(10) for e in ((i, (i + 1) % 10), (i, 10 + i), (10 + i, 10 + (i + 3) % 10))}
    lcf = [5, 7, -7, 7, -7, -5] * 3
    pappus = {frozenset((i, (i + 1) % 18)) for i in range(18)} | {frozenset((i, (i + lcf[i]) % 18)) for i in range(18)}
    for path, nb, m, base, name in ((os.path.join(GRAPHS, 'd3D13_n3400_lift_gp10_Z170.edges.gz'), 20, 170, desargues,
                                     'the Desargues graph GP(10,3)'),
                                    (os.path.join(GRAPHS, 'd3D14_n5706_lift_pappus_Z317.edges.gz'), 18, 317, pappus,
                                     'the Pappus graph')):
        with gzip.open(path, 'rt') as fh:
            n = int(fh.readline())
            E = {frozenset(map(int, ln.split())) for ln in fh if ln.strip()}
        ok(n == nb * m, 'lift size')
        shift = lambda v: (v // m) * m + (v % m + 1) % m
        ok({frozenset(shift(v) for v in e) for e in E} == E, 'i -> i+1 is not an automorphism')
        quot = {frozenset(v // m for v in e) for e in E}
        ok(len(quot) == 3 * nb // 2 and all(len(e) == 2 for e in quot), 'quotient not simple cubic')
        ok(isomorphic(quot, base, nb), f'quotient is not {name}')
        # the base itself: cubic, bipartite, girth 6 (a configuration of points and lines)
        print(f'7. {os.path.basename(path)}: Z{m} acts by i -> i+1 and the quotient is {name}: checked')
    # (3,11): the Haar structure of Z67 x|_9 Z11 with S = {(0,0), (0,1), (1,5)} (the BEYOND_TABLE row gives S as indices
    # {0, 67, 336} with index j*67 + a): two searches, and the edge list is exactly this structure
    head = ['3', '11', 'meta', '67', '11', '9', 'n', '1', 'N', '737']
    gens = ['meta(a=0,j=0) z=0', 'meta(a=0,j=1) z=0', 'meta(a=1,j=5) z=0']
    G, S, eA, eB = check_record('(3,11)', head, gens)
    F = G.factors[0]
    idx = lambda i: int(F.a[i] + 67 * F.j[i])            # our index a*k + j -> the file's j*67 + a
    ours = {(idx(g), 737 + idx(int(G.left(s)[g]))) for s in S for g in range(G.N)}
    with gzip.open(os.path.join(OWN, 'd3D11_n1474_meta67_11_9.edges.gz'), 'rt') as fh:
        n = int(fh.readline())
        E = {tuple(sorted(map(int, ln.split()))) for ln in fh if ln.strip()}
    ok(n == 1474 and E == ours, '(3,11): the edge list is not H(Z67 x|_9 Z11, S)')
    print(f'7. (3,11): H(Z67 x|_9 Z11, {{(0,0), (0,1), (1,5)}}) has eccentricities {eA}, {eB}, and the edge list '
          f'd3D11_n1474_meta67_11_9.edges.gz is exactly this structure: checked')
    # alpha for every symmetric S containing e in SL(2,p) / PSL(2,p) x Z_n, p prime: f and k as in VALUES
    nal = 0
    for d, D, v, kind, path, grp, Sh, chk, table in VALUES:
        if kind != 'H' or '.' not in Sh or Sh.startswith('0+'):
            continue
        head, gens = read_sol(os.path.join(REPO, path))
        if head[2] not in ('sl', 'psl') or 'poly' in head:
            continue
        f, mk = Sh.split('+')
        m, k = mk.split('.')
        a = orbit_alpha(os.path.join(REPO, path), k=int(k))
        ok(a is not None and a[2] == int(f), f'({d},{D}): no alpha of order {k} fixing {f} generators')
        nal += 1
    print(f'7. alpha found from S alone, with f and k as in the values list, for all {nal} symmetric sets containing e '
          'in SL(2,p) or PSL(2,p) times a cyclic group: checked')
    # (11,10): PSL(2,243) x Z11, alpha = (x -> x^3 on the matrix entries, GF(243) = GF(3)[x]/(x^5+2x+1)) x (z -> 3z)
    f = 'd11D10_psl_243_11_orb10_frob1d_ar3_s201.txt'
    head, gens = read_sol(os.path.join(SOLS, f))
    ok(head[3] == '243' and head[5] == 'x^5+2x+1' and head[7] == '11', f + ': header')
    fp, fk, fpoly = 3, 5, [1, 2, 0, 0, 0, 1]

    def fdec(c):
        return [(c // fp ** i) % fp for i in range(fk)]

    def fenc(v):
        return sum(x * fp ** i for i, x in enumerate(v))

    def fmul(a, b):
        A, B = fdec(a), fdec(b)
        r = [0] * (2 * fk - 1)
        for i in range(fk):
            for j in range(fk):
                r[i + j] = (r[i + j] + A[i] * B[j]) % fp
        for i in range(2 * fk - 2, fk - 1, -1):
            if r[i]:
                t = r[i]
                for j in range(fk + 1):
                    r[i - fk + j] = (r[i - fk + j] - t * fpoly[j]) % fp
        return fenc(r[:fk])

    def fnorm(m):
        return min(m, tuple(fenc([(-x) % fp for x in fdec(a)]) for a in m))
    S = [(tuple(int(x) for x in g.split('mat(')[1].split(')')[0].split(',')), int(g.split('z=')[1])) for g in gens]
    Sset = {(fnorm(m), z) for m, z in S}
    img = {(fnorm(tuple(fmul(fmul(a, a), a) for a in m)), (3 * z) % 11) for m, z in S}
    nfix = sum(1 for m, z in S if (fnorm(tuple(fmul(fmul(a, a), a) for a in m)), (3 * z) % 11) == (fnorm(m), z))
    ok(img == Sset and nfix == 1, f + ': S is not invariant under the Frobenius automorphism')
    print(f'7. {f}: S (11 elements) is mapped onto itself by (x -> x^3 on the entries) x (z -> 3 z), an automorphism '
          f'of order 5 fixing only e: checked')



# ------------------------------------------------------------------ the values table and Appendix B
# Delta, D, value, kind, file (relative to the repository root), group (LaTeX), S, checks, 2013 table value
#   kind: H = Haar structure, S symmetric (orbit search); M = Haar structure of a metacyclic group (or a product of
#         two), S without symmetry; L = lift of a small cubic incidence structure (not a Haar structure)
#   S: 'f+m.k' = f elements fixed by alpha (e among them when f >= 1) and m orbits of size k
#   checks: B build_haar2.py, I check_haar_indep.py, S haarcheck_sl.c, P haarcheck_psl.c, G haarcheck_gen.c,
#           T haarcheck2.c, X bigcheck_indep.c, A all-pairs search (apsp.c), M metacheck.py, L Lean, H check_haar.py;
#           a trailing ' marks a check run for this note (log in checks/haar/), a trailing ^ a log only on a branch
F = 'research/frontier/sols/'
O = 'research/synthetic/checks/haar/'
GR = 'research/frontier/beyond/graphs/'
OS = 'research/squads/own-small/records/'
VALUES = [
    (5, 9, 29756, 'M', F + 'd5D9_meta_346_43_29_s613_n29756.txt', r'\mathbb{Z}_{346}\rtimes_{29}\mathbb{Z}_{43}', 'random', 'B L H', 27936),
    (6, 9, 127296, 'H', F + 'd6D9_sl_17_13_orb3f0_s2.txt', r'\mathrm{SL}(2,17)\times\mathbb{Z}_{13}', '0+2.3', 'B L H', 117360),
    (7, 9, 462840, 'H', F + 'd7D9_psl_29_19_orb3_s1.txt', r'\mathrm{PSL}(2,29)\times\mathbb{Z}_{19}', '1+2.3', 'B L H', 400160),
    (8, 9, 1341600, 'H', F + 'd8D9_sl_25_43_orb3_s1.txt', r'\mathrm{SL}(2,25)\times\mathbb{Z}_{43}', '2+2.3', 'B H', 1091232),
    (9, 9, 3499776, 'H', F + 'd9D9_prod_psl_7_sl_7_31_orb3f0_s1.txt', r'\mathrm{PSL}(2,7)\times\mathrm{SL}(2,7)\times\mathbb{Z}_{31}', '0+3.3', 'B X', 2961536),
    (10, 9, 8418120, 'H', F + 'd10D9_psl_59_41_orb5f0_ORBW5RESTART1_s12.txt', r'\mathrm{PSL}(2,59)\times\mathbb{Z}_{41}', '0+2.5', 'P I', 7057400),
    (11, 9, 17323152, 'H', F + 'd11D9_sl_43_109_orbw3_s3.txt', r'\mathrm{SL}(2,43)\times\mathbb{Z}_{109}', '2+3.3', 'S T', 15200448),
    (12, 9, 35445648, 'H', F + 'd12D9_sl_83_31_orb3f0_orbw3_s3.txt', r'\mathrm{SL}(2,83)\times\mathbb{Z}_{31}', '0+4.3', 'S T', 30001152),
    (13, 9, 67742688, 'H', F + 'd13D9_sl_103_31_orb3_s1.txt', r'\mathrm{SL}(2,103)\times\mathbb{Z}_{31}', '1+4.3', 'S X', 50990610),
    (14, 9, 120043728, 'H', F + 'd14D9_sl_107_49_orb3_s1.txt', r'\mathrm{SL}(2,107)\times\mathbb{Z}_{49}', '2+4.3', 'S T', 95087738),
    (15, 9, 208483200, 'H', F + 'd15D9_prod_sl_5_sl_19_127_orb3f0_s52.txt', r'\mathrm{SL}(2,5)\times\mathrm{SL}(2,19)\times\mathbb{Z}_{127}', '0+5.3', 'G I', 168016334),
    (16, 9, 348207600, 'H', F + 'd16D9_sl_101_169_orb3_s1.txt', r'\mathrm{SL}(2,101)\times\mathbb{Z}_{169}', '1+5.3', 'S T', 288939118),
    (17, 9, 501707400, 'H', F + 'd17D9_psl_101_487_orb3_s2.txt', r'\mathrm{PSL}(2,101)\times\mathbb{Z}_{487}', '2+5.3', 'P I', None),
    (18, 9, 790626816, 'H', F + 'd18D9_sl_127_193_orb3_s2.txt', r'\mathrm{SL}(2,127)\times\mathbb{Z}_{193}', '3+5.3', 'S T', None),
    (19, 9, 1218394320, 'H', F + 'd19D9_sl_131_271_orb3_s2.txt', r'\mathrm{SL}(2,131)\times\mathbb{Z}_{271}', '1+6.3', 'S T', None),
    (20, 9, 1823175864, 'H', F + 'd20D9_psl_163_421_orb3_s2.txt', r'\mathrm{PSL}(2,163)\times\mathbb{Z}_{421}', '2+6.3', 'P G', None),
    (3, 10, 810, 'L', OS + 'd3D10_n810_c3xheis27.edges', r'5+5 \text{ base}, \mathbb{Z}_3\times\mathrm{He}_3', 'lift', 'A L H', 800),
    (4, 10, 12416, 'M', 'research/lifts/sols/d4D10_n12416_haar_meta97_64_19.txt', r'\mathbb{Z}_{97}\rtimes_{19}\mathbb{Z}_{64}', 'random', 'A L H', 11748),
    (5, 10, 95472, 'M', 'research/lifts/sols/d5D10_n95472_haar_meta1989_24_461.txt', r'\mathbb{Z}_{1989}\rtimes_{461}\mathbb{Z}_{24}', 'random', 'A L H', 90068),
    (6, 10, 524160, 'H', F + 'd6D10_prod_sl_5_psl_7_13_orb3f0_s1.txt', r'\mathrm{SL}(2,5)\times\mathrm{PSL}(2,7)\times\mathbb{Z}_{13}', '0+2.3', 'B L H', 452032),
    (7, 10, 2298240, 'H', F + 'd7D10_prod_sl_7_psl_19_1_orb3_s2.txt', r'\mathrm{SL}(2,7)\times\mathrm{PSL}(2,19)', '1+2.3', 'B I', 1987380),
    (8, 10, 8043840, 'H', F + 'd8D10_prod_psl_7_psl_19_7_orb3_s1.txt', r'\mathrm{PSL}(2,7)\times\mathrm{PSL}(2,19)\times\mathbb{Z}_{7}', '2+2.3', 'B I', 6927210),
    (9, 10, 24099600, 'H', F + 'd9D10_psl_151_7_orb3f0_s1.txt', r'\mathrm{PSL}(2,151)\times\mathbb{Z}_{7}', '0+3.3', 'P I', 20017260),
    (10, 10, 64294560, 'H', F + 'd10D10_psl_81_121_orb5f0_s3.txt', r'\mathrm{PSL}(2,81)\times\mathbb{Z}_{121}', '0+2.5', 'B I', 50331156),
    (11, 10, 157835304, 'H', F + 'd11D10_psl_243_11_orb10_frob1d_ar3_s201.txt', r'\mathrm{PSL}(2,243)\times\mathbb{Z}_{11}', '1+2.5', 'G I', 130592354),
    (12, 10, 332797296, 'H', F + 'd12D10_sl_157_43_orb3f0_s4.txt', r'\mathrm{SL}(2,157)\times\mathbb{Z}_{43}', '0+4.3', 'S T', 300383050),
    (13, 10, 683943456, 'H', F + 'd13D10_sl_137_133_orb3_ORBW3_s2.txt', r'\mathrm{SL}(2,137)\times\mathbb{Z}_{133}', '1+4.3', 'S T', 617330936),
    (14, 10, 1350537864, 'H', F + 'd14D10_psl_157_349_orb3_s2_n1350537864.txt', r'\mathrm{PSL}(2,157)\times\mathbb{Z}_{349}', '2+4.3', 'P G', 1213477190),
    (15, 10, 2566531440, 'H', F + 'd15D10_sl_109_991_orb5f0_s1_FIXPRE100_EARLYB1.txt', r'\mathrm{SL}(2,109)\times\mathbb{Z}_{991}', '0+3.5', 'S T G', 2300326510),
    (16, 10, 4708566360, 'H', F + 'd16D10_psl_179_821_orb5g_s41.txt', r'\mathrm{PSL}(2,179)\times\mathbb{Z}_{821}', '1+3.5', 'P G', 4119507330),
    (17, 10, 7022052336, 'H', F + 'd17D10_psl_313_229_orb3_s1.txt', r'\mathrm{PSL}(2,313)\times\mathbb{Z}_{229}', '2+5.3', 'P G', None),
    (18, 10, 11787972672, 'H', F + 'd18D10_psl_223_1063_orb3_s1.txt', r'\mathrm{PSL}(2,223)\times\mathbb{Z}_{1063}', '3+5.3', 'G P', None),
    (19, 10, 19233722496, 'H', F + 'd19D10_sl_607_43_orb3_s1.txt', r'\mathrm{SL}(2,607)\times\mathbb{Z}_{43}', '1+6.3', 'G S', None),
    (20, 10, 30518778360, 'H', F + 'd20D10_psl_421_409_orb3_s1.txt', r'\mathrm{PSL}(2,421)\times\mathbb{Z}_{409}', '2+6.3', 'G P', None),
    (3, 11, 1474, 'M', O + 'd3D11_n1474_meta67_11_9.edges.gz', r'\mathbb{Z}_{67}\rtimes_{9}\mathbb{Z}_{11}', 'exhaustive', 'A^ H', None),
    (4, 11, 30334, 'M', F + 'd4D11_meta_523_29_9_b2h01.txt', r'\mathbb{Z}_{523}\rtimes_{9}\mathbb{Z}_{29}', 'random', 'B A^ H', None),
    (5, 11, 311426, 'M', F + 'd5D11_meta_5023_31_2886_b5k05.txt', r'\mathbb{Z}_{5023}\rtimes_{2886}\mathbb{Z}_{31}', 'random', 'B A^ H', None),
    (6, 11, 2122518, 'M', F + 'd6D11_meta_20809_51_12972_b5k07.txt', r'\mathbb{Z}_{20809}\rtimes_{12972}\mathbb{Z}_{51}', 'random', 'B H', None),
    (7, 11, 11012976, 'H', F + 'd7D11_sl_53_37_orb3-2-1_d09.txt', r'\mathrm{SL}(2,53)\times\mathbb{Z}_{37}', '1+2.3', 'G S', None),
    (8, 11, 45329808, 'H', F + 'd8D11_sl_283_1_orb3-2-2_e04.txt', r'\mathrm{SL}(2,283)', '2+2.3', 'G S', None),
    (9, 11, 155250816, 'H', F + 'd9D11_sl_223_7_orb3-3-0_d08.txt', r'\mathrm{SL}(2,223)\times\mathbb{Z}_{7}', '0+3.3', 'G S', None),
    (10, 11, 460691568, 'H', F + 'd10D11_sl_613_1_orb3-3-1_d13.txt', r'\mathrm{SL}(2,613)', '1+3.3', 'G S', None),
    (11, 11, 1241299248, 'H', F + 'd11D11_sl_853_1_orb3-3-2_s1.txt', r'\mathrm{SL}(2,853)', '2+3.3', 'G S', None),
    (12, 11, 2976066240, 'H', F + 'd12D11_sl_239_109_orb3-4-0_c04.txt', r'\mathrm{SL}(2,239)\times\mathbb{Z}_{109}', '0+4.3', 'G S', None),
    (13, 11, 6781213392, 'H', F + 'd13D11_sl_563_19_orb3-4-1_s1.txt', r'\mathrm{SL}(2,563)\times\mathbb{Z}_{19}', '1+4.3', 'G S', None),
    (14, 11, 14381398080, 'H', F + 'd14D11_sl_1009_7_orb3-4-2_s1.txt', r'\mathrm{SL}(2,1009)\times\mathbb{Z}_{7}', '2+4.3', 'G S', None),
    (15, 11, 28655908512, 'H', F + 'd15D11_sl_617_61_orb3-5-0_s1.txt', r'\mathrm{SL}(2,617)\times\mathbb{Z}_{61}', '0+5.3', 'G S', None),
    (16, 11, 29961590400, 'H', O + 'd16D11_psl_449_331_orb3-5-1_s1.txt', r'\mathrm{PSL}(2,449)\times\mathbb{Z}_{331}', '1+5.3', 'G^ P^', None),
    (3, 12, 2368, 'L', OS + 'd3D12_n2368_meta37_8.edges', r'4+4 \text{ base}, \mathbb{Z}_{37}\rtimes_{6}\mathbb{Z}_{8}', 'lift', 'A A L H', None),
    (4, 12, 74066, 'M', O + 'd4D12_meta_1277_29_964_h08.txt', r'\mathbb{Z}_{1277}\rtimes_{964}\mathbb{Z}_{29}', 'random', 'A M^ H', None),
    (5, 12, 1058342, 'M', F + 'd5D12_meta_8969_59_205_b6l03.txt', r'\mathbb{Z}_{8969}\rtimes_{205}\mathbb{Z}_{59}', 'random', 'B H', None),
    (6, 12, 9366240, 'H', F + 'd6D12_psl_79_19_orb3-2-0_e08.txt', r'\mathrm{PSL}(2,79)\times\mathbb{Z}_{19}', '0+2.3', 'G P', None),
    (7, 12, 59838504, 'H', F + 'd7D12_psl_67_199_orb3-2-1_e09.txt', r'\mathrm{PSL}(2,67)\times\mathbb{Z}_{199}', '1+2.3', 'G P', None),
    (8, 12, 284095056, 'H', F + 'd8D12_psl_167_61_orb3-2-2_f10.txt', r'\mathrm{PSL}(2,167)\times\mathbb{Z}_{61}', '2+2.3', 'G P', None),
    (9, 12, 1105785120, 'H', F + 'd9D12_psl_241_79_orb3-3-0_e11.txt', r'\mathrm{PSL}(2,241)\times\mathbb{Z}_{79}', '0+3.3', 'G P', None),
    (10, 12, 3712424352, 'H', F + 'd10D12_psl_337_97_orb3-3-1_f12.txt', r'\mathrm{PSL}(2,337)\times\mathbb{Z}_{97}', '1+3.3', 'G P', None),
    (11, 12, 11189148096, 'H', F + 'd11D12_psl_223_1009_orb3-3-2_s2.txt', r'\mathrm{PSL}(2,223)\times\mathbb{Z}_{1009}', '2+3.3', 'G P', None),
    (12, 12, 29996171040, 'H', F + 'd12D12_psl_241_2143_orb3-4-0_s1.txt', r'\mathrm{PSL}(2,241)\times\mathbb{Z}_{2143}', '0+4.3', 'G P', None),
    (13, 12, 29997644040, 'H', F + 'd13D12_psl_181_5059_orb3-4-1_s1.txt', r'\mathrm{PSL}(2,181)\times\mathbb{Z}_{5059}', '1+4.3', 'G P', None),
    (14, 12, 29996171040, 'H', F + 'd14D12_psl_241_2143_orb3-4-2_s1.txt', r'\mathrm{PSL}(2,241)\times\mathbb{Z}_{2143}', '2+4.3', 'G P', None),
    (3, 13, 3400, 'L', GR + 'd3D13_n3400_lift_gp10_Z170.edges.gz', r'\text{Desargues}, \mathbb{Z}_{170}', 'lift', 'A^ A H', None),
    (4, 13, 192382, 'M', O + 'd4D13_meta_2237_43_1984_h03.txt', r'\mathbb{Z}_{2237}\rtimes_{1984}\mathbb{Z}_{43}', 'random', 'A M^ H', None),
    (5, 13, 3594910, 'M', O + 'd5D13_prodmeta_11_5_2971_11_i06.txt', r'(\mathbb{Z}_{11}\rtimes_4\mathbb{Z}_5)\times(\mathbb{Z}_{2971}\rtimes_{1764}\mathbb{Z}_{11})', 'random', "M^ H", None),
    (6, 13, 41734392, 'H', O + 'd6D13_psl_83_73_orb3-2-0_f11.txt', r'\mathrm{PSL}(2,83)\times\mathbb{Z}_{73}', '0+2.3', "G^ P'", None),
    (7, 13, 312227760, 'H', O + 'd7D13_sl_229_13_orb3-2-1_e10.txt', r'\mathrm{SL}(2,229)\times\mathbb{Z}_{13}', '1+2.3', "G^ S'", None),
    (8, 13, 1739514000, 'H', O + 'd8D13_sl_499_7_orb3-2-2_s2.txt', r'\mathrm{SL}(2,499)\times\mathbb{Z}_{7}', '2+2.3', "G^ S'", None),
    (9, 13, 7924036032, 'H', O + 'd9D13_sl_593_19_orb3-3-0_s6.txt', r'\mathrm{SL}(2,593)\times\mathbb{Z}_{19}', '0+3.3', "G^ S'", None),
    (10, 13, 19980294768, 'H', O + 'd10D13_psl_503_157_orb3-3-1_s1.txt', r'\mathrm{PSL}(2,503)\times\mathbb{Z}_{157}', '1+3.3', 'G^', None),
    (3, 14, 5706, 'L', GR + 'd3D14_n5706_lift_pappus_Z317.edges.gz', r'\text{Pappus}, \mathbb{Z}_{317}', 'lift', 'A^ A H', None),
    (4, 14, 497042, 'M', O + 'd4D14_meta_2731_91_i04.txt', r'\mathbb{Z}_{2731}\rtimes_{2400}\mathbb{Z}_{91}', 'random', 'A M^ H', None),
    (5, 14, 12795166, 'M', O + 'd5D14_meta_148781_43_i07.txt', r'\mathbb{Z}_{148781}\rtimes_{85175}\mathbb{Z}_{43}', 'random', 'M^ H', None),
    (6, 14, 187990656, 'H', O + 'd6D14_sl_97_103_orb3-2-0_g07.txt', r'\mathrm{SL}(2,97)\times\mathbb{Z}_{103}', '0+2.3', "G^ S'", None),
    (7, 14, 1674490944, 'H', O + 'd7D14_psl_223_151_orb3-2-1_h14.txt', r'\mathrm{PSL}(2,223)\times\mathbb{Z}_{151}', '1+2.3', "G^ P'", None),
    (8, 14, 11325238056, 'H', O + 'd8D14_psl_397_181_orb3-2-2_s4.txt', r'\mathrm{PSL}(2,397)\times\mathbb{Z}_{181}', '2+2.3', "G^ P'", None),
]
# beyond the master ledger (research/RESULTS.md) at the time of writing
NOT_IN_LEDGER = {(16, 11), (3, 11), (4, 12)} | {(d, 13) for d in range(3, 11)} | {(d, 14) for d in range(3, 9)}
CAPPED = {(16, 11), (13, 12), (14, 12), (10, 13)}       # first S solved at a size cap of the job (mu about 0)


def fmt(v):
    return '{:,}'.format(v).replace(',', '{,}')


def shape_tex(s):
    if '.' in s:
        f, mk = s.split('+')
        m, k = mk.split('.')
        return f'${f}+{m}\\cdot{k}$'
    return s


def checks_tex(c):
    out = []
    for t in c.split():
        base, mark = t[0], t[1:]
        out.append(base + ('$^\\prime$' if mark == "'" else '$^\\ast$' if mark == '^' else ''))
    return ', '.join(out)


def grid_rows():
    best = {(d, D): v for d, D, v, *_ in VALUES}
    rows = []
    for d in range(3, 21):
        cells = []
        for D in range(9, 15):
            if (d, D) not in best:
                cells.append('--')
                continue
            row = next(r for r in VALUES if r[0] == d and r[1] == D)
            v = best[(d, D)]
            marks = ''
            if (d, D) == (14, 12):
                v = best[(13, 12)]        # a structure of degree 13 also has degree at most 14
                marks += r'\S'
            marks += {'L': r'\dagger', 'M': r'\ddagger', 'H': ''}[row[3]]
            if (d, D) in CAPPED:
                marks += r'\circ'
            if (d, D) in NOT_IN_LEDGER:
                marks += r'\sharp'
            cells.append(f'${fmt(v)}' + (f'^{{{marks}}}$' if marks else '$'))
        rows.append(f'{d} & ' + ' & '.join(cells) + r'\\')
    return '\n'.join(rows)


def appendix_rows(Ds):
    rows = []
    for d, D, v, kind, path, grp, S, chk, table in sorted(VALUES, key=lambda r: (r[1], r[0])):
        if D not in Ds:
            continue
        if kind == 'L':
            mu = '--'
        elif (d, D) in CAPPED:
            mu = r'$\approx0$'
        else:
            m = (v / 2) * math.exp(-W(d, D) / (v / 2))
            mu = f'{m:.1f}' if m >= 10 else f'{m:.2f}'
        tab = fmt(table) if table else '--'
        rows.append(f'$({d},{D})$ & ${fmt(v)}$ & ${tab}$ & ${grp}$ & {shape_tex(S)} & {mu} & {checks_tex(chk)}'
                    .replace('$--$', '--') + r'\\')
    return '\n'.join(rows)


def check_values():
    nm = 0
    for d, D, v, kind, path, grp, S, chk, table in VALUES:
        full = os.path.join(REPO, path)
        ok(os.path.exists(full), f'missing {path}')
        if path.endswith('.edges') or path.endswith('.edges.gz'):
            with (gzip.open(full, 'rt') if path.endswith('.gz') else open(full)) as fh:
                n = int(fh.readline())
            ok(n == v, f'({d},{D}): {n} vertices in {path}, table says {v}')
        elif path.startswith('research/lifts/sols/'):
            lines = open(full).read().split('\n')
            gr = next(ln for ln in lines if ln.startswith('group')).split()
            hd = next(ln for ln in lines if ln.startswith('lift')).split()
            ok(int(hd[2]) == D and int(hd[4]) == d and 2 * int(gr[2]) * int(gr[3]) == v, f'({d},{D}) header')
        else:
            head, gens = read_sol(full)
            ok(int(head[0]) == d and int(head[1]) == D, f'({d},{D}): header {head[:2]}')
            ok(2 * int(head[head.index('N') + 1]) == v, f'({d},{D}): 2N != {v}')
            ok(len(gens) == d, f'({d},{D}): {len(gens)} generators')
        if '.' in S:
            f, mk = S.split('+')
            m, k = mk.split('.')
            ok(int(f) + int(m) * int(k) == d, f'({d},{D}): shape {S} does not add up to Delta')
            n = int(read_sol(full)[0][read_sol(full)[0].index('n') + 1])
            ok(all(n % q or q % int(k) == 1 for q in range(2, n + 1) if all(q % t for t in range(2, q))),
               f'({d},{D}): a prime factor of n = {n} is not 1 mod {k}')
        nm += 1
    # the tables in SYNTHETIC.tex are the ones generated here
    tex = open(os.path.join(HERE, '..', 'SYNTHETIC.tex')).read()
    ok(grid_rows() in tex, 'the values table in SYNTHETIC.tex differs from the data here (check_haar.py --tables)')
    for Ds in ((9, 10), (11, 12), (13, 14)):
        ok(appendix_rows(Ds) in tex, f'the Appendix B table for D = {Ds} differs from the data here')
    # size-law numbers quoted in Section 7.3
    lo_hi = {}
    for d, D, v, kind, *_ in VALUES:
        if kind == 'L' or (d, D) in CAPPED:
            continue
        N = v / 2
        mu = N * math.exp(-W(d, D) / N)
        frac = v / moore(d, D)
        lo_hi.setdefault(D, []).append((d, mu, frac, math.log(N)))
    mus = [m for D in lo_hi for _, m, _, _ in lo_hi[D]]
    lns = [ln for D in lo_hi for _, _, _, ln in lo_hi[D]]
    print(f'8. Values table and Appendix B: {nm} values agree with their files (2N from the headers, n from the edge lists), '
          'the orbit shapes add up to Delta, and the tables in SYNTHETIC.tex are the ones generated from this data: '
          'checked')
    print(f'   size law (Haar values, capped cells excluded): mu from {min(mus):.2f} to {max(mus):.1f}, '
          f'ln N from {min(lns):.1f} to {max(lns):.1f}; 2N/M_b by D:',
          ', '.join(f'D={D}: {max(f for _, _, f, _ in r):.3f}..{min(f for _, _, f, _ in r):.3f}'
                    for D, r in sorted(lo_hi.items())))
    for D in sorted(lo_hi):
        print(f'   D={D}: ' + ', '.join(f'({d}) mu={m:.1f} {100 * f:.1f}%' for d, m, f, _ in sorted(lo_hi[D])))


def main():
    check_haar_lemmas()
    check_isomorphisms()
    check_singer()
    check_counting()
    check_orbits()
    check_records()
    check_values()
    print('ALL CHECKS PASSED')


if __name__ == '__main__':
    if sys.argv[1:] == ['--tables']:
        print('% values table rows\n' + grid_rows())
        for Ds in ((9, 10), (11, 12), (13, 14)):
            print(f'% Appendix B rows, D = {Ds}\n' + appendix_rows(Ds))
    else:
        main()
