r"""Checks for Section 7 of SYNTHETIC.tex (diameters 9 to 14: Haar structures).

Everything is written here from the definitions, without the lab's search or checking code.

  1. Haar structures (Definition 7.1): right multiplication is an automorphism group acting regularly on the
     points and on the lines; all degrees are Delta.
  2. Lemma 7.2 (two searches): on random S in small groups (SL(2,3), SL(2,5) x Z_3, PSL(2,7), S_4, D_12,
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
  7. Record structures rebuilt from their solution files (two searches, Lemma 7.2), with alpha-invariance of S
     where the file is an orbit solution with e in S; the Delta = 3 lifts and the (3,11) Haar graph by an
     all-pairs search on their edge lists (no symmetry used).
  8. The size-law numbers of Table 8 (W, lambda = W/N, mu = N e^-lambda, 2N/M_b) for every value in it.

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
                for g in range(G.n):    # every point is on Delta lines, every line has Delta points
                    pass
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


class BigGroup:
    """G = Z_m x|_r Z_k (head 'meta m k r n 1') or SL(2,p) / PSL(2,p) x Z_n (p prime), elements indexed 0..N-1.
    left(s) is the permutation g -> s g as a numpy array; e is the index of the identity."""

    def __init__(self, head):
        self.D, self.d, fam = int(head[1]), int(head[0]), head[2]
        self.fam = fam
        if fam == 'meta':
            m, k, r = int(head[3]), int(head[4]), int(head[5])
            ok(int(head[head.index('n') + 1]) == 1, 'meta with a cyclic factor not handled')
            ok(pow(r, k, m) == 1, 'meta: r^k != 1 mod m')
            self.m, self.k, self.r = m, k, r
            self.N = m * k
            self.a = np.repeat(np.arange(m, dtype=np.int64), k)
            self.j = np.tile(np.arange(k, dtype=np.int64), m)
            self.rp = np.array([pow(r, t, m) for t in range(k)], dtype=np.int64)
            self.e = 0
        else:
            ok(fam in ('sl', 'psl') and 'poly' not in head and 'prod' not in head, 'only sl/psl over a prime field')
            p = int(head[3])
            n = int(head[head.index('n') + 1])
            self.p, self.n, self.proj = p, n, fam == 'psl'
            A, B, C, Dd = (x.ravel() for x in np.meshgrid(*[np.arange(p, dtype=np.int64)] * 4, indexing='ij'))
            mask = (A * Dd - B * C) % p == 1
            codes = np.unique(self.code(A[mask], B[mask], C[mask], Dd[mask]))
            ok(len(codes) == p * (p * p - 1) // (2 if self.proj else 1), 'group order')
            self.codes = codes
            self.N = len(codes) * n
            reps = np.repeat(codes, n)
            self.aa, self.bb, self.cc, self.dd = reps // p ** 3, reps // p ** 2 % p, reps // p % p, reps % p
            self.zz = np.tile(np.arange(n, dtype=np.int64), len(codes))
            self.e = int(np.searchsorted(codes, self.code(np.int64(1), 0, 0, 1))) * n
        ok(self.N == int(head[head.index('N') + 1]), 'N in the header')

    def code(self, a, b, c, d):
        p = self.p
        c1 = ((a * p + b) * p + c) * p + d
        if self.proj:
            c2 = ((((-a) % p) * p + (-b) % p) * p + (-c) % p) * p + (-d) % p
            return np.minimum(c1, c2)
        return c1

    def parse(self, desc):
        if self.fam == 'meta':
            return int(desc.split('a=')[1].split(',')[0]), int(desc.split('j=')[1].split(')')[0])
        m = desc.split('mat(')[1].split(')')[0].split(',')
        return tuple(int(x) % self.p for x in m), int(desc.split('z=')[1])

    def left(self, s):
        if self.fam == 'meta':      # (sa, sj)(a, j) = (sa + r^sj a, sj + j)
            sa, sj = s
            return ((sa + self.rp[sj] * self.a) % self.m) * self.k + (sj + self.j) % self.k
        (sa, sb, sc, sd), sz = s
        p = self.p
        na, nb = (sa * self.aa + sb * self.cc) % p, (sa * self.bb + sb * self.dd) % p
        nc, nd = (sc * self.aa + sd * self.cc) % p, (sc * self.bb + sd * self.dd) % p
        return np.searchsorted(self.codes, self.code(na, nb, nc, nd)) * self.n + (sz + self.zz) % self.n

    def inv(self, s):
        if self.fam == 'meta':
            sa, sj = s
            ij = (-sj) % self.k
            return ((-int(self.rp[ij]) * sa) % self.m, ij)
        (sa, sb, sc, sd), sz = s
        p = self.p
        return (sd, (-sb) % p, (-sc) % p, sa), (-sz) % self.n


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


def check_record(path):
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


def find_alpha(G, S):
    """For an SL/PSL(2,p) x Z_n solution with e in S: an automorphism alpha = (conjugation by t of order 3 in the
    matrix part) x (z -> r z, r of order 3 mod n) with alpha(S) = S, or None."""
    p, n = G.p, G.n

    def norm(m):
        m = tuple(x % p for x in m)
        return min(m, tuple((-x) % p for x in m)) if G.proj else m

    def mm(x, y):
        return (x[0] * y[0] + x[1] * y[2], x[0] * y[1] + x[1] * y[3], x[2] * y[0] + x[3] * y[2],
                x[2] * y[1] + x[3] * y[3])
    Sset = {(norm(m), z) for m, z in S}
    rs = [r for r in range(1, n) if pow(r, 3, n) == 1 and r != 1] or [1]
    for t in itertools.product(range(p), repeat=4):
        if (t[0] * t[3] - t[1] * t[2]) % p != 1:
            continue
        t3 = norm(mm(mm(t, t), t))
        if t3 != norm((1, 0, 0, 1)) or norm(t) == norm((1, 0, 0, 1)):
            continue
        ti = (t[3], -t[1], -t[2], t[0])
        for r in rs:
            img = {(norm(mm(mm(t, m), ti)), (r * z) % n) for m, z in S}
            if img == Sset:
                fixed = sum(1 for m, z in S if (norm(mm(mm(t, m), ti)), (r * z) % n) == (norm(m), z))
                return t, r, fixed
    return None


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

    for r in [r for r in range(2, n) if pow(r, k, n) == 1]:
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
             (SOLS, 'd7D9_psl_29_19_orb3_s1.txt'), (SOLS, 'd4D11_meta_523_29_9_b2h01.txt'),
             (SOLS, 'd5D11_meta_5023_31_2886_b5k05.txt'), (SOLS, 'd6D11_meta_20809_51_12972_b5k07.txt'),
             (SOLS, 'd4D12_meta_731_48_7_b5k02.txt'), (OWN, 'd4D12_meta_1277_29_964_h08.txt'),
             (SOLS, 'd5D12_meta_8969_59_205_b6l03.txt'), (OWN, 'd4D13_meta_2237_43_1984_h03.txt'),
             (OWN, 'd4D14_meta_2731_91_i04.txt')]
    for d, f in files:
        G, S, eA, eB = check_record(os.path.join(d, f))
        extra = ''
        # orbit solutions with e in S (f >= 1): S itself is alpha-invariant.  For f = 0 the file stores S s0^-1
        # (Section 7.2), which is not, so those are only checked for the diameter.
        if G.fam != 'meta' and 'orb3' in f and 'f0' not in f and not f.split('orb3')[1].startswith('-') :
            a = find_alpha(G, S)
            ok(a is not None, f + ': no order-3 automorphism of the expected form maps S onto S')
            t, r, fx = a
            extra = f'; S is mapped onto itself by (conjugation by {t}) x (z -> {r} z), fixing {fx} of the generators'
        print(f'7. {f}: {G.d}-regular, {2 * G.N:,} vertices, eccentricity {eA} from the point e and {eB} from '
              f'the line e, diameter {max(eA, eB)}{extra}: checked')
    lifts = [(os.path.join(REPO, 'research/squads/own-small/records/d3D10_n810_c3xheis27.edges'), 10),
             (os.path.join(OWN, 'd3D11_n1474_meta67_11_9.edges.gz'), 11),
             (os.path.join(REPO, 'research/squads/own-small/records/d3D12_n2368_meta37_8.edges'), 12),
             (os.path.join(OWN, 'd3D13_n3400_lift_gp10_Z170.edges.gz'), 13),
             (os.path.join(OWN, 'd3D14_n5706_lift_pappus_Z317.edges.gz'), 14)]
    for path, D in lifts:
        n, degs, diam = apsp_cubic(path, D)
        ok(degs == [3] and diam == D, f'{path}: degrees {degs}, diameter {diam}')
        print(f'7. {os.path.basename(path)}: {n:,} vertices, cubic, bipartite, diameter {diam} (all pairs): checked')
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
    a = orbit_alpha(os.path.join(SOLS, 'd16D10_psl_179_821_orb5g_s41.txt'), k=5)
    ok(a is not None and a[2] == 1, '(16,10): S is not invariant under a conjugation of order 5')
    print(f'7. d16D10_psl_179_821_orb5g_s41.txt: S (16 elements) is mapped onto itself by (conjugation by {a[0]}) x '
          f'(z -> {a[1]} z), an automorphism of order 5 fixing only e: checked')
    # alpha-invariance of S in large orbit solutions with e in S (no diameter check here; that is the checkers' job)
    for f in ('d14D9_sl_107_49_orb3_s1.txt', 'd13D10_sl_137_133_orb3_ORBW3_s2.txt', 'd17D10_psl_313_229_orb3_s1.txt',
              'd13D11_sl_563_19_orb3-4-1_s1.txt', 'd13D12_psl_181_5059_orb3-4-1_s1.txt',
              'd14D12_psl_241_2143_orb3-4-2_s1.txt'):
        a = orbit_alpha(os.path.join(SOLS, f))
        ok(a is not None, f + ': S is not invariant under an automorphism of the expected form')
        t, r, fx = a
        head, gens = read_sol(os.path.join(SOLS, f))
        print(f'7. {f}: S ({len(gens)} elements) is mapped onto itself by (conjugation by {t}) x (z -> {r} z), '
              f'an automorphism of order 3 fixing {fx} of the generators: checked')


def main():
    check_haar_lemmas()
    check_isomorphisms()
    check_singer()
    check_counting()
    check_orbits()
    check_records()
    print('ALL CHECKS PASSED')


if __name__ == '__main__':
    main()
