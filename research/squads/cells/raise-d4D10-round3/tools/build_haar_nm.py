"""Independent rebuild + diameter check for haar_gen / haar_gen2 / haar_gen3 solution files (all group families).

Usage: python3 build_haar2.py SOLUTION.txt [OUT.edges.txt]
Prints ecc from (e,A) and (e,B), unreached counts, n, edges, max/min degree, duplicate edges, and the sha256 of the
edge list (written to OUT if given; the sha256 is computed either way).  Exit code 0 iff the graph has diameter <= D
from both sides, every vertex reached, max degree = d and no repeated edge.

The groups are constructed here from their mathematical definitions (numpy), independently of the C code:
  meta m k r          Z_m x|_r Z_k, (a,j)(b,l) = (a + r^j b, j + l)
  sl q / psl q / pgl q   2x2 matrices over GF(q) with det 1 / det 1 mod +-1 / det != 0 mod scalars; q = p^k with the
                      field GF(p)[x]/(f) given by "poly f" in the spec (k > 1); field elements written as sum c_i p^i
  agl1 q              maps x -> a x + b over GF(q), product = composition (s g)(x) = s(g(x))
  prod G1 G2          direct product
  cyc                 trivial group
and G = <group> x Z_n, except
  tpgl q              G = Z_n x| PGL(2,q): (m,z)(m',z') = (m m', z + chi(m) z'), chi(m) = +1 if det(m) is a square in
                      GF(q), else -1 (well defined on PGL since scalars change det by squares).
  csl q               G = (SL(2,q) x Z_n) / <(-I, n/2)> (central product, n even); element [X, z] with X the
                      lexicographically smaller of +-X, [-X, z] = [X, z + n/2].  Element order (for the edge list) = sorted canonical tuples, then z; for the old families this
is the same order as build_haar.py, so the edge list (and its sha256) is identical to build_haar.py's.
Haar graph: vertices (g,A) -> idx(g), (g,B) -> N + idx(g); edges (g,A) ~ (s g, B), s in S.  Right multiplication by G is
an automorphism group transitive on each side, so two BFS (from (e,A) and (e,B)) give the exact diameter.
"""
import hashlib
import re
import sys
from itertools import product as iproduct

import numpy as np


# ---------------------------------------------------------------- fields
def parse_poly(s, p):
    """'x^3+2x+1' -> coefficient list low..high"""
    coeffs = {}
    for term in s.split("+"):
        m = re.fullmatch(r"(\d*)(x(\^(\d+))?)?", term)
        if not m or term == "":
            raise ValueError("bad polynomial " + s)
        c = int(m.group(1)) if m.group(1) else 1
        e = (int(m.group(4)) if m.group(4) else 1) if m.group(2) else 0
        coeffs[e] = (coeffs.get(e, 0) + c) % p
    k = max(coeffs)
    return [coeffs.get(i, 0) for i in range(k + 1)]


def poly_mod(a, f, p):
    a = list(a)
    k = len(f) - 1
    inv_lead = pow(f[-1], p - 2, p)
    for i in range(len(a) - 1, k - 1, -1):
        t = a[i] * inv_lead % p
        if t:
            for j in range(k + 1):
                a[i - k + j] = (a[i - k + j] - t * f[j]) % p
    return a[:k] + [0] * max(0, k - len(a))


def is_irreducible(f, p):
    k = len(f) - 1
    for dg in range(1, k // 2 + 1):
        for low in iproduct(range(p), repeat=dg):
            g = list(low) + [1]
            if not any(poly_mod(f, g, p)[: dg]):
                return False
    return True


class Field:
    def __init__(self, q, poly=None):
        p = next(t for t in range(2, q + 1) if q % t == 0)
        k, x = 0, q
        while x % p == 0:
            x //= p
            k += 1
        assert x == 1, "q must be a prime power"
        self.q, self.p, self.k = q, p, k
        if k == 1:
            assert poly is None
            v = np.arange(q)
            self.add = (v[:, None] + v[None, :]) % q
            self.mul = (v[:, None] * v[None, :]) % q
        else:
            f = parse_poly(poly, p)
            assert len(f) == k + 1 and f[-1] == 1 and is_irreducible(f, p), "poly must be monic irreducible of degree k"
            digits = [[(e // p ** i) % p for i in range(k)] for e in range(q)]
            enc = lambda ds: sum(c * p ** i for i, c in enumerate(ds))
            self.add = np.array([[enc([(a + b) % p for a, b in zip(digits[x1], digits[y1])]) for y1 in range(q)]
                                 for x1 in range(q)])
            mul = np.zeros((q, q), dtype=np.int64)
            for x1 in range(q):
                for y1 in range(q):
                    pr = [0] * (2 * k - 1)
                    for i, a in enumerate(digits[x1]):
                        for j, b in enumerate(digits[y1]):
                            pr[i + j] = (pr[i + j] + a * b) % p
                    mul[x1, y1] = enc(poly_mod(pr, f, p))
            self.mul = mul
        self.add = self.add.astype(np.int64)
        self.mul = self.mul.astype(np.int64)
        self.neg = np.array([int(np.where(self.add[a] == 0)[0][0]) for a in range(q)])
        inv = np.zeros(q, dtype=np.int64)
        for a in range(1, q):
            inv[a] = int(np.where(self.mul[a] == 1)[0][0])
        self.inv = inv
        # field axioms (checked fully for small q, sampled otherwise)
        rng = np.random.default_rng(1)
        a, b, c = (rng.integers(0, q, 20000) for _ in range(3))
        A, M = self.add, self.mul
        assert (A[A[a, b], c] == A[a, A[b, c]]).all() and (M[M[a, b], c] == M[a, M[b, c]]).all()
        assert (M[a, A[b, c]] == A[M[a, b], M[a, c]]).all() and (M[a, b] == M[b, a]).all()
        assert all(M[x1, inv[x1]] == 1 for x1 in range(1, q))


# ---------------------------------------------------------------- groups
class Group:
    """elements 0..order-1 in sorted canonical order; lmul(s, idx_array) -> idx_array of s*g; parse(desc) -> index;
    chi(s) = sign by which s acts on the cyclic factor Z_n (+1 except for tpgl)"""

    def chi(self, s):
        return 1

    def lmul2(self, s, g):
        """(index of s*g, extra shift of the Z_n coordinate) -- the shift is 0 except for csl"""
        return self.lmul(s, g), 0

    def parse2(self, desc):
        return self.parse(desc), 0


class Meta(Group):
    def __init__(self, m, k, r):
        assert pow(r, k, m) == 1 % m
        self.m, self.k, self.r = m, k, r
        self.order = m * k
        self.ident = 0
        self.spec = f"meta {m} {k} {r}"

    def lmul(self, s, g):
        a, j = divmod(s, self.k)
        b, l = np.divmod(g, self.k)
        return ((a + pow(self.r, j, self.m) * b) % self.m) * self.k + (j + l) % self.k

    def parse(self, desc):
        a, j = map(int, re.fullmatch(r"meta\(a=(\d+),j=(\d+)\)", desc).groups())
        assert 0 <= a < self.m and 0 <= j < self.k
        return a * self.k + j


class NMeta(Group):
    """Non-split metacyclic Z_m . Z_k: b a b^-1 = a^r, b^k = a^s (needs r^k = 1, s(r-1) = 0 mod m).
    Normal form a^a b^j.  (a^a b^j)(a^b b^l) = a^(a + r^j b) b^(j+l), and if j+l >= k then b^(j+l) = b^t a^s with
    t = j+l-k, so the a-exponent gains s r^t.  Associativity and inverses are checked on construction."""
    def __init__(self, m, k, r, s):
        assert pow(r, k, m) == 1 % m and (s * (r - 1)) % m == 0
        self.m, self.k, self.r, self.s = m, k, r, s
        self.Rk = np.array([pow(r, t, m) for t in range(k)], dtype=np.int64)
        self.order = m * k
        self.ident = 0
        self.spec = f"nmeta {m} {k} {r} {s}"
        rng = np.random.default_rng(1)
        for _ in range(20000):
            x, y, z = (int(v) for v in rng.integers(0, self.order, 3))
            assert self.lmul(x, self.lmul(y, z)) == self.lmul(self.lmul(x, y), z), "nmeta: not associative"
        allg = np.arange(self.order)
        for x in range(self.order):   # every element has a right inverse
            assert (self.lmul(x, allg) == 0).any(), "nmeta: no inverse"

    def lmul(self, s_, g):
        a, j = divmod(int(s_), self.k)
        b, l = np.divmod(np.asarray(g, dtype=np.int64), self.k)
        t = j + l
        ov = t >= self.k
        tt = np.where(ov, t - self.k, t)
        c = (a + self.Rk[j] * b + np.where(ov, self.s * self.Rk[tt], 0)) % self.m
        return c * self.k + tt

    def parse(self, desc):
        a, j = map(int, re.fullmatch(r"nmeta\(a=(\d+),j=(\d+)\)", desc).groups())
        assert 0 <= a < self.m and 0 <= j < self.k
        return a * self.k + j


class Matrix(Group):
    def __init__(self, kind, q, poly=None):
        F = Field(q, poly)
        self.F, self.kind, self.q = F, kind, q
        A, M, neg = F.add, F.mul, F.neg
        keys = []
        v = np.arange(q)
        b, c, d = (x.ravel() for x in np.meshgrid(v, v, v, indexing="ij"))
        for a in range(q):                       # brute force over all (a,b,c,d), det = ad - bc
            det = A[M[a, d], neg[M[b, c]]]
            ok = det == 1 if kind in ("sl", "psl") else det != 0
            aa = np.full(int(ok.sum()), a)
            keys.append(self.canon_key(aa, b[ok], c[ok], d[ok]))
        self.keys = np.unique(np.concatenate(keys))
        self.order = len(self.keys)
        expect = q * (q * q - 1) // (2 if (kind == "psl" and q % 2) else 1)
        assert self.order == expect, (self.order, expect)
        self.ident = self.index(self.canon_key(np.array([1]), np.array([0]), np.array([0]), np.array([1])))[0]
        self.spec = f"{kind} {q}" + (f" poly {poly}" if poly else "")
        self.twist = False
        self.csl = False

    def chi(self, s):
        if not self.twist:
            return 1
        F = self.F
        a, b, c, d = (int(x[0]) for x in self.entries(np.array([s])))
        det = int(F.add[F.mul[a, d], F.neg[F.mul[b, c]]])
        squares = {int(F.mul[v, v]) for v in range(1, self.q)}
        return 1 if det in squares else -1

    def canon_key(self, a, b, c, d):
        q, F = self.q, self.F
        if self.kind == "psl" and q % 2:
            na, nb, nc, nd = F.neg[a], F.neg[b], F.neg[c], F.neg[d]
            k1 = ((a * q + b) * q + c) * q + d
            k2 = ((na * q + nb) * q + nc) * q + nd
            return np.minimum(k1, k2)
        if self.kind == "pgl":
            first = np.where(a != 0, a, b)
            iv = F.inv[first]
            a, b, c, d = F.mul[a, iv], F.mul[b, iv], F.mul[c, iv], F.mul[d, iv]
        return ((a * q + b) * q + c) * q + d

    def index(self, key):
        i = np.searchsorted(self.keys, key)
        assert (i < self.order).all() and (self.keys[np.minimum(i, self.order - 1)] == key).all()
        return i

    def entries(self, idx):
        k = self.keys[idx]
        q = self.q
        return k // q ** 3, (k // q ** 2) % q, (k // q) % q, k % q

    def lmul(self, s, g):
        A, M = self.F.add, self.F.mul
        sa, sb, sc, sd = (int(x[0]) for x in self.entries(np.array([s])))
        a, b, c, d = self.entries(g)
        na = A[M[sa, a], M[sb, c]]
        nb = A[M[sa, b], M[sb, d]]
        nc = A[M[sc, a], M[sd, c]]
        nd = A[M[sc, b], M[sd, d]]
        return self.index(self.canon_key(na, nb, nc, nd))

    def lmul2(self, s, g):
        if not self.csl:
            return self.lmul(s, g), 0
        q, F, A, M = self.q, self.F, self.F.add, self.F.mul
        sa, sb, sc, sd = (int(x[0]) for x in self.entries(np.array([s])))
        a, b, c, d = self.entries(g)
        na = A[M[sa, a], M[sb, c]]
        nb = A[M[sa, b], M[sb, d]]
        nc = A[M[sc, a], M[sd, c]]
        nd = A[M[sc, b], M[sd, d]]
        actual = ((na * q + nb) * q + nc) * q + nd
        canon = self.canon_key(na, nb, nc, nd)          # min over +-X
        return self.index(canon), np.where(actual != canon, self.n // 2, 0)

    def parse2(self, desc):
        idx = self.parse(desc)
        if not self.csl:
            return idx, 0
        vals = [int(t) for t in re.fullmatch(r"mat\(([^)]*)\)", desc).group(1).split(",")]
        q = self.q
        actual = ((vals[0] * q + vals[1]) * q + vals[2]) * q + vals[3]
        return idx, (self.n // 2 if actual != int(self.keys[idx]) else 0)

    def parse(self, desc):
        vals = [int(t) for t in re.fullmatch(r"mat\(([^)]*)\)", desc).group(1).split(",")]
        assert len(vals) == 4 and all(0 <= t < self.q for t in vals)
        a, b, c, d = (np.array([t]) for t in vals)
        F = self.F
        det = int(F.add[F.mul[vals[0], vals[3]], F.neg[F.mul[vals[1], vals[2]]]])
        assert (det == 1) if self.kind in ("sl", "psl") else (det != 0), "matrix not in the group"
        return int(self.index(self.canon_key(a, b, c, d))[0])


class AGL1(Group):
    def __init__(self, q, poly=None):
        self.F, self.q = Field(q, poly), q
        self.order = q * (q - 1)
        self.ident = 0          # (a=1, b=0): index (a-1)*q + b, sorted by (a, b)
        self.spec = f"agl1 {q}" + (f" poly {poly}" if poly else "")

    def lmul(self, s, g):
        q, A, M = self.q, self.F.add, self.F.mul
        a1, b1 = s // q + 1, s % q
        a2, b2 = g // q + 1, g % q
        return (M[a1, a2] - 1) * q + A[M[a1, b2], b1]

    def parse(self, desc):
        a, b = map(int, re.fullmatch(r"aff\((\d+),(\d+)\)", desc).groups())
        assert 1 <= a < self.q and 0 <= b < self.q
        return (a - 1) * self.q + b


class Triv(Group):
    order, ident, spec = 1, 0, "cyc"

    def lmul(self, s, g):
        return g

    def parse(self, desc):
        assert desc == ""
        return 0


class Prod(Group):
    def __init__(self, g1, g2):
        self.g1, self.g2 = g1, g2
        self.order = g1.order * g2.order
        self.ident = g1.ident * g2.order + g2.ident
        self.spec = f"prod {g1.spec} {g2.spec}"

    def lmul(self, s, g):
        o2 = self.g2.order
        return self.g1.lmul(s // o2, g // o2) * o2 + self.g2.lmul(s % o2, g % o2)

    def parse(self, desc):
        m = re.fullmatch(r"prod\[(.*)\]", desc)
        inner, depth = m.group(1), 0
        for i, ch in enumerate(inner):          # split at the top-level ';'
            depth += ch in "[(" and 1 or 0
            depth -= ch in "])" and 1 or 0
            if ch == ";" and depth == 0:
                return self.g1.parse(inner[:i]) * self.g2.order + self.g2.parse(inner[i + 1:])
        raise ValueError("bad prod description " + desc)


def parse_group(tok, i):
    t = tok[i]
    if t == "meta":
        return Meta(int(tok[i + 1]), int(tok[i + 2]), int(tok[i + 3])), i + 4
    if t == "nmeta":
        return NMeta(int(tok[i + 1]), int(tok[i + 2]), int(tok[i + 3]), int(tok[i + 4])), i + 5
    if t == "csl":
        assert i == 0, "csl only as the whole group"
        q = int(tok[i + 1])
        assert q % 2, "csl needs q odd"
        poly, j = None, i + 2
        if j < len(tok) and tok[j] == "poly":
            poly, j = tok[j + 1], j + 2
        g = Matrix("psl", q, poly)
        g.csl = True
        g.spec = "c" + g.spec[1:]
        return g, j
    if t == "tpgl":
        assert i == 0, "tpgl only as the whole group"
        q = int(tok[i + 1])
        assert q % 2, "tpgl needs q odd"
        poly, j = None, i + 2
        if j < len(tok) and tok[j] == "poly":
            poly, j = tok[j + 1], j + 2
        g = Matrix("pgl", q, poly)
        g.twist = True
        g.spec = "t" + g.spec
        return g, j
    if t in ("sl", "psl", "pgl", "agl1"):
        q = int(tok[i + 1])
        poly, j = None, i + 2
        if j < len(tok) and tok[j] == "poly":
            poly, j = tok[j + 1], j + 2
        return (AGL1(q, poly) if t == "agl1" else Matrix(t, q, poly)), j
    if t == "prod":
        g1, j = parse_group(tok, i + 1)
        g2, j = parse_group(tok, j)
        return Prod(g1, g2), j
    if t == "cyc":
        return Triv(), i + 1
    raise ValueError("unknown group " + t)


# ---------------------------------------------------------------- main
def main():
    sol = sys.argv[1]
    out = sys.argv[2] if len(sys.argv) > 2 else None
    lines = [ln for ln in open(sol).read().split("\n") if ln.strip()]
    head = lines[0].split()
    d, D = int(head[0]), int(head[1])
    ni = head.index("n")
    Q, j = parse_group(head[2:ni], 0)
    assert j == ni - 2, "trailing tokens in the group spec"
    n = int(head[ni + 1])
    N = Q.order * n
    if getattr(Q, "csl", False):
        assert n % 2 == 0, "csl needs n even"
        Q.n = n
    if "N" in head[ni:]:
        assert int(head[head.index("N", ni) + 1]) == N, "declared N does not match the group order"
    S = []
    for ln in lines[1:1 + d]:
        body = ln.split(None, 1)[1] if len(ln.split(None, 1)) > 1 else ""
        m = re.fullmatch(r"(.*?)\s*z=(\d+)", body.strip())
        desc, z = m.group(1), int(m.group(2))
        assert 0 <= z < n
        qidx, zs = Q.parse2(desc)
        S.append(qidx * n + (z + zs) % n)
    assert len(S) == d and len(set(S)) == d, "generators must be d distinct elements"
    # permutations g -> s g of G = Q x Z_n, element index qi * n + z
    qi = np.arange(Q.order)
    perms = []
    for s in S:
        sq, sz = divmod(s, n)
        qp, zshift = Q.lmul2(sq, qi)
        qp = np.asarray(qp, dtype=np.int64)
        zshift = np.broadcast_to(np.asarray(zshift, dtype=np.int64), qp.shape)
        assert len(np.unique(qp)) == Q.order, "left multiplication is not a permutation"
        perm = (qp[:, None] * n + (Q.chi(sq) * np.arange(n)[None, :] + sz + zshift[:, None]) % n).ravel()
        perms.append(perm)
    perms = np.array(perms, dtype=np.int32)                   # d x N (int32 keeps 10M-vertex checks in memory)
    inv = np.empty_like(perms)
    ar = np.arange(N, dtype=np.int32)
    for t in range(d):
        inv[t][perms[t]] = ar
    del ar
    e = Q.ident * n
    ok = True
    for src_side in (0, 1):
        distA = np.full(N, -1, dtype=np.int16)
        distB = np.full(N, -1, dtype=np.int16)
        (distA if src_side == 0 else distB)[e] = 0
        front, side, lev = np.array([e]), src_side, 0
        mark = np.zeros(N, dtype=bool)
        while len(front):
            lev += 1
            P = perms if side == 0 else inv
            mark[:] = False
            for t in range(d):
                mark[P[t][front]] = True
            tgt = distB if side == 0 else distA
            nb = np.flatnonzero(mark & (tgt < 0))
            tgt[nb] = lev
            front, side = nb, side ^ 1
        ecc = int(max(distA.max(), distB.max()))
        unreached = int((distA < 0).sum() + (distB < 0).sum())
        print("ecc from", "A" if src_side == 0 else "B", "=", ecc, "unreached", unreached)
        ok &= unreached == 0 and ecc <= D
        del distA, distB, mark
    nv = 2 * N
    # degrees: every A vertex g has the d listed edges (g, s g); B vertex degrees counted per generator
    degB = np.zeros(N, dtype=np.int64)
    for t in range(d):
        degB += np.bincount(perms[t], minlength=N)
    maxdeg, mindeg = max(d, int(degB.max())), min(d, int(degB.min()))
    del degB
    # repeated edges: (g, s g) = (g, s' g) for two generators, i.e. equal entries in a column of perms
    dup, step = 0, 1 << 20
    for st in range(0, N, step):
        blk = np.sort(perms[:, st:st + step], axis=0)
        dup += int((blk[1:] == blk[:-1]).sum())
    print("n =", nv, "edges =", N * d, "max degree =", maxdeg, "min degree =", mindeg, "duplicate edges =", dup)
    ok &= maxdeg == d and dup == 0
    h = hashlib.sha256()
    f = open(out, "w") if out else None
    chunk = f"{nv}\n"
    h.update(chunk.encode())
    if f:
        f.write(chunk)
    gstep = max(1, (1 << 20) // d)
    for st in range(0, N, gstep):
        blk = perms[:, st:st + gstep]
        u = np.repeat(np.arange(st, st + blk.shape[1], dtype=np.int64), d)
        v = N + blk.T.ravel().astype(np.int64)
        txt = "\n".join(f"{a} {b}" for a, b in zip(u.tolist(), v.tolist())) + "\n"
        h.update(txt.encode())
        if f:
            f.write(txt)
    if f:
        f.close()
    print("edge list sha256 =", h.hexdigest())
    print("VALID" if ok else "INVALID", f"d={d} D={D} group={Q.spec} x Z_{n} N={N} vertices={nv}")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
