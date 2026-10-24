"""Parse every Haar record (research/frontier/sols/*.txt, haar_gen3 format) into explicit group elements, and compute
normal-form invariants of the connection set S.

Haar graph H(G,S): vertices G x {A,B}, (g,A) ~ (s g, B).  H(G,S) = H(G, aSb) for a, b in G (relabel the sides), so the
invariants of S are the conjugacy classes of the quotients s_i^-1 s_j and s_i s_j^-1 (i != j), not the s_i themselves.
In SL(2,q) a non-central class is fixed by its trace (tr != +-2), so we record traces and element orders.

Groups (as in build_haar2.py): sl/psl/pgl q (q a prime power, field GF(p)[x]/(f)), meta m k r, agl1 q, prod G1 G2,
cyc, each times Z_n.  Elements are tuples; G = Q x Z_n elements are (qpart, z).
"""
import re, os, sys, glob
from math import gcd
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'frontier'))
from build_haar2 import Field  # field tables only (add/mul/neg/inv)

SOLS = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'frontier', 'sols')


class MatG:
    def __init__(self, kind, q, poly=None):
        self.kind, self.q, self.poly = kind, q, poly
        self.F = Field(q, poly)
        A, M = self.F.add, self.F.mul
        self.A = [[int(x) for x in row] for row in A]
        self.M = [[int(x) for x in row] for row in M]
        self.neg = [int(x) for x in self.F.neg]
        self.inv_ = [int(x) for x in self.F.inv]
        self.p = self.F.p
        self.order = q * (q * q - 1) // (2 if (kind == 'psl' and q % 2) else 1)
        if kind == 'pgl':
            self.order = q * (q * q - 1)
        self.e = self.canon((1, 0, 0, 1))
        self.name = f"{kind}({q})"

    def canon(self, m):
        a, b, c, d = m
        if self.kind == 'psl' and self.q % 2:
            n = tuple(self.neg[x] for x in m)
            return min(m, n)
        if self.kind == 'pgl':
            f = a if a else b
            iv = self.inv_[f]
            return tuple(self.M[x][iv] for x in m)
        return m

    def mul(self, x, y):
        A, M = self.A, self.M
        a, b, c, d = x
        e, f, g, h = y
        return self.canon((A[M[a][e]][M[b][g]], A[M[a][f]][M[b][h]], A[M[c][e]][M[d][g]], A[M[c][f]][M[d][h]]))

    def inv(self, x):
        a, b, c, d = x
        det = self.A[self.M[a][d]][self.neg[self.M[b][c]]]
        idet = self.inv_[det]
        M = self.M
        return self.canon((M[d][idet], M[self.neg[b]][idet], M[self.neg[c]][idet], M[a][idet]))

    def det(self, x):
        a, b, c, d = x
        return self.A[self.M[a][d]][self.neg[self.M[b][c]]]

    def trace(self, x):
        """trace; for psl the class of +-trace (we return the smaller encoding); for pgl tr^2/det (projective)"""
        a, b, c, d = x
        t = self.A[a][d]
        if self.kind == 'psl' and self.q % 2:
            return min(t, self.neg[t])
        if self.kind == 'pgl':
            return self.M[self.M[t][t]][self.inv_[self.det(x)]]
        return t

    def is_e(self, x):
        return x == self.e

    def parse(self, desc):
        vals = tuple(int(t) for t in re.fullmatch(r"mat\(([^)]*)\)", desc).group(1).split(","))
        return self.canon(vals)


class MetaG:
    def __init__(self, m, k, r):
        self.m, self.k, self.r = m, k, r
        self.order = m * k
        self.e = (0, 0)
        self.name = f"Z{m}x|{r}Z{k}"

    def mul(self, x, y):
        a, j = x
        b, l = y
        return ((a + pow(self.r, j, self.m) * b) % self.m, (j + l) % self.k)

    def inv(self, x):
        a, j = x
        jj = (-j) % self.k
        return ((-pow(self.r, jj, self.m) * a) % self.m, jj)

    def parse(self, desc):
        a, j = map(int, re.fullmatch(r"meta\(a=(\d+),j=(\d+)\)", desc).groups())
        return (a, j)

    def trace(self, x):
        return None


class AGL1G:
    def __init__(self, q, poly=None):
        self.F = Field(q, poly)
        self.q = q
        self.A = [[int(x) for x in row] for row in self.F.add]
        self.M = [[int(x) for x in row] for row in self.F.mul]
        self.neg = [int(x) for x in self.F.neg]
        self.inv_ = [int(x) for x in self.F.inv]
        self.order = q * (q - 1)
        self.e = (1, 0)
        self.name = f"AGL1({q})"

    def mul(self, x, y):  # (s g)(t) = s(g(t)), s = (a1,b1): t -> a1 t + b1
        a1, b1 = x
        a2, b2 = y
        return (self.M[a1][a2], self.A[self.M[a1][b2]][b1])

    def inv(self, x):
        a, b = x
        ia = self.inv_[a]
        return (ia, self.neg[self.M[ia][b]])

    def parse(self, desc):
        a, b = map(int, re.fullmatch(r"aff\((\d+),(\d+)\)", desc).groups())
        return (a, b)

    def trace(self, x):
        return None


class TrivG:
    order, e, name = 1, (), "1"

    def mul(self, x, y): return ()
    def inv(self, x): return ()
    def parse(self, desc): return ()
    def trace(self, x): return None


class ProdG:
    def __init__(self, g1, g2):
        self.g1, self.g2 = g1, g2
        self.order = g1.order * g2.order
        self.e = (g1.e, g2.e)
        self.name = f"{g1.name}x{g2.name}"

    def mul(self, x, y): return (self.g1.mul(x[0], y[0]), self.g2.mul(x[1], y[1]))
    def inv(self, x): return (self.g1.inv(x[0]), self.g2.inv(x[1]))

    def parse(self, desc):
        inner, depth = re.fullmatch(r"prod\[(.*)\]", desc).group(1), 0
        for i, ch in enumerate(inner):
            depth += ch in "[(" and 1 or 0
            depth -= ch in "])" and 1 or 0
            if ch == ";" and depth == 0:
                return (self.g1.parse(inner[:i]), self.g2.parse(inner[i + 1:]))
        raise ValueError(desc)

    def trace(self, x):
        return (self.g1.trace(x[0]), self.g2.trace(x[1]))


def parse_group(tok, i):
    t = tok[i]
    if t == 'meta':
        return MetaG(int(tok[i + 1]), int(tok[i + 2]), int(tok[i + 3])), i + 4
    if t in ('sl', 'psl', 'pgl', 'agl1'):
        q = int(tok[i + 1]); poly, j = None, i + 2
        if j < len(tok) and tok[j] == 'poly':
            poly, j = tok[j + 1], j + 2
        return (AGL1G(q, poly) if t == 'agl1' else MatG(t, q, poly)), j
    if t == 'prod':
        g1, j = parse_group(tok, i + 1)
        g2, j = parse_group(tok, j)
        return ProdG(g1, g2), j
    if t == 'cyc':
        return TrivG(), i + 1
    raise ValueError("unsupported group " + t)


class G:
    """Q x Z_n"""
    def __init__(self, Q, n):
        self.Q, self.n = Q, n
        self.order = Q.order * n
        self.e = (Q.e, 0)

    def mul(self, x, y): return (self.Q.mul(x[0], y[0]), (x[1] + y[1]) % self.n)
    def inv(self, x): return (self.Q.inv(x[0]), (-x[1]) % self.n)

    def order_of(self, x, cap=None):
        """element order by repeated multiplication (cap = give up beyond)"""
        y, k = x, 1
        cap = cap or 4 * self.order
        while y != self.e:
            y = self.mul(y, x); k += 1
            if k > cap: return None
        return k


def load(path):
    lines = [ln for ln in open(path).read().split("\n") if ln.strip()]
    head = lines[0].split()
    d, D = int(head[0]), int(head[1])
    ni = head.index('n')
    Q, j = parse_group(head[2:ni], 0)
    n = int(head[ni + 1])
    grp = G(Q, n)
    S = []
    for ln in lines[1:1 + d]:
        body = ln.split(None, 1)[1].strip()
        m = re.fullmatch(r"(.*?)\s*z=(\d+)", body)
        S.append((Q.parse(m.group(1)), int(m.group(2))))
    tag = os.path.basename(path)[:-4]
    return dict(path=path, tag=tag, d=d, D=D, spec=' '.join(head[2:ni]), Q=Q, n=n, G=grp, N=grp.order, S=S)


def all_records():
    return [load(p) for p in sorted(glob.glob(os.path.join(SOLS, '*.txt')))]


def orbit_type(tag, d):
    if 'orb5' in tag: return 'k5'
    if 'orb3f0' in tag: return 'k3f0'
    if 'orb3' in tag: return 'k3f%d' % ({1: 1, 2: 2, 0: 3}[d % 3])
    return 'rand'
