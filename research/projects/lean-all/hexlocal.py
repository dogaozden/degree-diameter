#!/usr/bin/env python3
"""Local certificates for the three-level hexagon constructions (research/d13D7/multi.c, sol format "multi"), q prime.

The graph of a multi sol is Theorem 1 of the hexagon-family project (lean/BipartiteDD/HexagonD7, `Hyp`, `exists_graph`)
for H(q) over ZMod q: R the freed points, sigma the sol's bijection, one hub of each side per point of R, the hub graph
of the sol. `Hyp.pl/p2/l2` hold in H(q) for every field (Mathlib side, no computation). What is left is local to R:
R non-collinear, sigma a local duality at every r in R, and the hub graph. This script writes those facts as data that
`LeanAll/HexLocal.lean` checks:

  * D: the points of R and of every Gamma_2(r), as base-q codes of normalised vectors, sorted (domain points);
  * Lam: the lines sigma(D), each by a basis (a, b) with normalised Pluecker coordinates, sorted by their code;
  * sg: domain index -> line index (sigma), sgi its inverse;
  * per r in R: the q+1 lines through r (r and an extra vector x_k), the q points of each line other than r (domain
    indices with coefficients), the q+1 points z_t of sigma(r) (codes, coefficients), and for each z_t the q lines of
    Lam through z_t other than sigma(r) (index, coefficients, and the position e of the point of Gamma_2(r) that sigma
    maps to it);
  * the hub graph (both directions).

Every check that Lean will run is run here first (`check`), with the same arithmetic.

usage: hexlocal.py SOL HEXBIN OUT.json
"""
import json, struct, sys, array

PAIRS = [(i, j) for i in range(7) for j in range(i + 1, 7)]
TITS = [(1, 2, 3, 4), (5, 4, 3, 2), (2, 0, 3, 5), (6, 5, 3, 0), (0, 1, 3, 6), (4, 6, 3, 1)]


def mulC8(a, b):
    """GF(8) product modulo x^3 + x + 1 (LeanAll/GF8.lean mulC)."""
    bit = lambda n, i: n >> i & 1
    c0 = bit(a, 0) * bit(b, 0)
    c1 = bit(a, 0) * bit(b, 1) + bit(a, 1) * bit(b, 0)
    c2 = bit(a, 0) * bit(b, 2) + bit(a, 1) * bit(b, 1) + bit(a, 2) * bit(b, 0)
    c3 = bit(a, 1) * bit(b, 2) + bit(a, 2) * bit(b, 1)
    c4 = bit(a, 2) * bit(b, 2)
    return (c0 + c3) % 2 + 2 * ((c1 + c3 + c4) % 2) + 4 * ((c2 + c4) % 2)


class Fld:
    """The field of the checks: ZMod p (Nat arithmetic of LeanAll/HexArith.lean) or GF(8) (LeanAll/HexGF8.lean)."""

    def __init__(self, q):
        self.q = q
        self.prime = all(q % d for d in range(2, q))
        assert self.prime or q == 8, 'q must be prime or 8'

    def add(self, a, b):
        return (a + b) % self.q if self.prime else a ^ b

    def mul(self, a, b):
        return (a * b) % self.q if self.prime else mulC8(a, b)

    def inv(self, a):
        return next(x for x in range(1, self.q) if self.mul(a, x) == 1)

    def cd(self, c, i):
        return c // self.q ** i % self.q

    def vec(self, c):
        return [self.cd(c, i) for i in range(7)]

    def code(self, v):
        return sum(x * self.q ** i for i, x in enumerate(v))

    def qN(self, c):
        p, v = self.q, self.vec(c)
        if self.prime:
            return (v[0] * v[4] + v[1] * v[5] + v[2] * v[6]) % p == (v[3] * v[3]) % p
        m = mulC8
        return m(v[0], v[4]) ^ m(v[1], v[5]) ^ m(v[2], v[6]) ^ m(v[3], v[3]) == 0

    def bN(self, a, b):
        p, x, y = self.q, self.vec(a), self.vec(b)
        if self.prime:
            return (x[0] * y[4] + x[4] * y[0] + x[1] * y[5] + x[5] * y[1] + x[2] * y[6] + x[6] * y[2]) % p == \
                (2 * (x[3] * y[3])) % p
        m = mulC8
        return m(x[0], y[4]) ^ m(x[4], y[0]) ^ m(x[1], y[5]) ^ m(x[5], y[1]) ^ m(x[2], y[6]) ^ m(x[6], y[2]) == 0

    def pl1(self, x, y, i, j):
        p = self.q
        if self.prime:
            return (x[i] * y[j] + p * p - x[j] * y[i]) % p
        return mulC8(x[i], y[j]) ^ mulC8(x[j], y[i])

    def tN(self, a, b):
        x, y = self.vec(a), self.vec(b)
        if self.prime:
            p = self.q
            return all((x[i] * y[j] + x[l] * y[k]) % p == (x[k] * y[l] + x[j] * y[i]) % p for (i, j, k, l) in TITS)
        return all(self.pl1(x, y, i, j) == self.pl1(x, y, k, l) for (i, j, k, l) in TITS)

    def plN(self, a, b):
        x, y = self.vec(a), self.vec(b)
        return [self.pl1(x, y, i, j) for (i, j) in PAIRS]

    def plCode(self, a, b):
        return sum(t * self.q ** k for k, t in enumerate(self.plN(a, b)))

    def linN(self, y, a, b, al, be):
        Y, A, B = self.vec(y), self.vec(a), self.vec(b)
        if not self.prime and not (al < 8 and be < 8):
            return False
        return all(Y[i] == self.add(self.mul(al, A[i]), self.mul(be, B[i])) for i in range(7))

    def ptOK(self, c):
        return c < self.q ** 7 and first_one(self.vec(c)) and self.qN(c)

    def lnOK(self, a, b):
        return self.qN(a) and self.qN(b) and self.bN(a, b) and self.tN(a, b) and first_one(self.plN(a, b))

    def coeffs(self, y, a, b):
        for al in range(self.q):
            for be in range(self.q):
                if all(y[i] == self.add(self.mul(al, a[i]), self.mul(be, b[i])) for i in range(7)):
                    return al, be
        raise ValueError('not in span')

    def line_basis(self, u, w):
        """a basis (u, c w) of the line through u, w with normalised Pluecker coordinates."""
        pl = self.plN(self.code(u), self.code(w))
        for t in pl:
            if t:
                c = self.inv(t)
                return u, [self.mul(c, x) for x in w]
        raise ValueError('dependent')


def first_one(xs):
    for x in xs:
        if x != 0:
            return x == 1
    return False


def build(solf, hexf):
    f = open(hexf, 'rb')
    q, N, L = struct.unpack('<3i', f.read(12))
    Q1 = q + 1
    lp = array.array('i')
    lp.frombytes(f.read(4 * L * Q1))
    coord = f.read(N * 7)
    p = q
    K = Fld(q)
    code = lambda p_, v: K.code(v)
    pts = [list(coord[7 * i: 7 * i + 7]) for i in range(N)]
    pcode = [code(p, v) for v in pts]
    assert pcode == sorted(pcode) and all(first_one(v) for v in pts)
    lines = [list(lp[l * Q1:(l + 1) * Q1]) for l in range(L)]
    pl = [[] for _ in range(N)]
    for l in range(L):
        for x in lines[l]:
            pl[x].append(l)
    tok = open(solf).read().split()
    assert tok[0] == 'multi'
    q2, N2, r, m, Hn, HP, n = map(int, tok[1:8])
    assert (q2, N2, r, Hn, HP) == (q, N, 1, m, m)
    pos = 8
    assert tok[pos] == 'freed'
    R = list(map(int, tok[pos + 1: pos + 1 + m])); pos += 1 + m
    assert tok[pos] == 'hubedges'
    k = int(tok[pos + 1])
    hg = list(map(int, tok[pos + 2: pos + 2 + 2 * k])); pos += 2 + 2 * k
    sig = list(map(int, tok[pos: pos + N]))
    assert sorted(sig) == list(range(N))
    assert n == 6 * N + 2 * m

    def g2p(x):
        return [y for l in pl[x] for y in lines[l] if y != x]

    D = sorted(set(R) | {y for x in R for y in g2p(x)})
    dix = {x: i for i, x in enumerate(D)}
    Lam = sorted({sig[x] for x in D})
    assert len(Lam) == len(D)
    # bases of the image lines
    lbasis = {}
    for l in Lam:
        u, w = pts[lines[l][0]], pts[lines[l][1]]
        a, b = K.line_basis(u, w)
        lbasis[l] = (code(p, a), code(p, b))
    Lam.sort(key=lambda l: K.plCode(*lbasis[l]))
    lix = {l: j for j, l in enumerate(Lam)}
    sg = [lix[sig[x]] for x in D]
    sgi = [0] * len(D)
    for i, j in enumerate(sg):
        sgi[j] = i
    # R in domain order; hub j of the sol is owned by R[j]
    Rord = sorted(range(m), key=lambda j: dix[R[j]])
    newhub = {j: v for v, j in enumerate(Rord)}
    rl = [dix[R[j]] for j in Rord]
    hubL = [[] for _ in range(m)]
    hubR = [[] for _ in range(m)]
    for t in range(k):
        a, b = newhub[hg[2 * t]], newhub[hg[2 * t + 1]]
        hubL[a].append(b)
        hubR[b].append(a)
    hubL = [sorted(x) for x in hubL]
    hubR = [sorted(x) for x in hubR]
    certs = []
    for j in Rord:
        x = R[j]
        rv = pts[x]
        aux = []
        for l in pl[x]:
            other = [y for y in lines[l] if y != x]
            _, xk = K.line_basis(rv, pts[other[0]])
            ents = []
            for y in other:
                al, be = K.coeffs(pts[y], rv, xk)
                ents.append((dix[y], al, be))
            ents.sort()
            aux.append((K.plCode(code(p, rv), code(p, xk)), code(p, xk), ents, l))
        aux.sort()
        xs = [a[1] for a in aux]
        es = [a[2] for a in aux]
        flat = [e for k_ in es for e in k_]
        # the point y of Gamma_2(r) with sigma(y) = line, by position
        epos = {sig[D[e[0]]]: t for t, e in enumerate(flat)}
        ell = sig[x]
        a, b = lbasis[ell]
        A, B = K.vec(a), K.vec(b)
        zs = []
        for z in sorted(lines[ell], key=lambda z: pcode[z]):
            al, be = K.coeffs(pts[z], A, B)
            fl = []
            for l2 in pl[z]:
                if l2 == ell:
                    continue
                ma, mb = lbasis[l2]
                ga, de = K.coeffs(pts[z], K.vec(ma), K.vec(mb))
                fl.append((lix[l2], ga, de, epos[l2]))
            fl.sort()
            zs.append(((pcode[z], al, be), fl))
        certs.append({'xs': xs, 'es': es, 'zs': [z[0] for z in zs], 'fs': [z[1] for z in zs]})
    return {'p': p, 'q': q, 'N': N, 'm': m, 'n': n, 'ptc': [pcode[x] for x in D],
            'lnA': [lbasis[l][0] for l in Lam], 'lnB': [lbasis[l][1] for l in Lam], 'sg': sg, 'sgi': sgi,
            'rl': rl, 'hubL': hubL, 'hubR': hubR, 'certs': certs}


def check(d):
    """The checks of LeanAll/HexLocal.lean, with the same arithmetic."""
    p, q, M, m = d['p'], d['q'], len(d['ptc']), d['m']
    K = Fld(q)
    ptOK, lnOK, linN = (lambda p_, c: K.ptOK(c)), (lambda p_, a, b: K.lnOK(a, b)), (lambda p_, *a: K.linN(*a))
    plCode = lambda p_, a, b: K.plCode(a, b)
    ptc, lnA, lnB, sg, sgi, rl = d['ptc'], d['lnA'], d['lnB'], d['sg'], d['sgi'], d['rl']
    assert all(ptOK(p, c) for c in ptc), 'G1 point'
    assert all(ptc[i] < ptc[i + 1] for i in range(M - 1)), 'G1 sorted'
    assert all(lnOK(p, lnA[j], lnB[j]) for j in range(M)), 'G2 line'
    plc = [plCode(p, lnA[j], lnB[j]) for j in range(M)]
    assert all(plc[j] < plc[j + 1] for j in range(M - 1)), 'G2 sorted'
    assert all(sg[i] < M and sgi[sg[i]] == i for i in range(M)), 'G3'
    assert all(rl[v] < M for v in range(m)) and all(rl[v] < rl[v + 1] for v in range(m - 1)), 'G4'
    rset = set(rl)
    for v in range(m):
        c = d['certs'][v]
        r = ptc[rl[v]]
        L0 = sg[rl[v]]
        a, b = lnA[L0], lnB[L0]
        xs, es, zs, fs = c['xs'], c['es'], c['zs'], c['fs']
        assert len(xs) == q + 1 and len(es) == q + 1 and len(zs) == q + 1 and len(fs) == q + 1
        for k in range(q + 1):
            assert xs[k] < p ** 7 and lnOK(p, r, xs[k]), 'aux line'
            if k:
                assert plCode(p, r, xs[k - 1]) < plCode(p, r, xs[k]), 'aux sorted'
            assert len(es[k]) == q
            for s, (i, al, be) in enumerate(es[k]):
                assert i < M and i != rl[v] and i not in rset and linN(p, ptc[i], r, xs[k], al, be), 'entry'
                if s:
                    assert es[k][s - 1][0] < i
        flat = [e for k_ in es for e in k_]
        mask = 0
        for t in range(q + 1):
            z, al, be = zs[t]
            assert ptOK(p, z) and linN(p, z, a, b, al, be), 'z'
            if t:
                assert zs[t - 1][0] < z
            assert len(fs[t]) == q
            for s, (mm, ga, de, e) in enumerate(fs[t]):
                assert mm < M and mm != L0 and linN(p, z, lnA[mm], lnB[mm], ga, de), 'f line'
                assert e < q * (q + 1) and sg[flat[e][0]] == mm, 'f pos'
                if s:
                    assert fs[t][s - 1][0] < mm
                mask |= 1 << e
        assert mask == (1 << (q * (q + 1))) - 1, 'mask'
    hubL, hubR = d['hubL'], d['hubR']
    assert all(len(x) <= q - 1 and all(u < m for u in x) for x in hubL)
    assert all(len(x) <= q - 1 and all(u < m for u in x) for x in hubR)
    assert all(v in hubR[u] for v in range(m) for u in hubL[v]) and all(v in hubL[u] for v in range(m) for u in hubR[v])
    # hub graph on 2m vertices (V = 0..m-1, U = m..2m-1): every pair within 7
    nb = [[m + u for u in hubL[v]] for v in range(m)] + [list(hubR[u]) for u in range(m)]
    full = (1 << (2 * m)) - 1
    mk = [1 << v for v in range(2 * m)]
    for _ in range(7):
        mk = [mk[v] | _or(mk, nb[v]) for v in range(2 * m)]
    assert all(x == full for x in mk), 'hub distances'
    return True


def _or(mk, l):
    x = 0
    for u in l:
        x |= mk[u]
    return x


if __name__ == '__main__':
    d = build(sys.argv[1], sys.argv[2])
    check(d)
    M = len(d['ptc'])
    print(f"q={d['q']} N={d['N']} |R|={d['m']} n={d['n']} domain points {M}; all checks pass", file=sys.stderr)
    json.dump(d, open(sys.argv[3], 'w'))
