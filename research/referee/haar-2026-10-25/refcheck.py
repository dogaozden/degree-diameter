"""Referee's own checker: H(G,S), G = Q1 [x Q2] x Z_n, Qi = SL/PSL(2,q) (q prime or q = p^k via the header poly),
(g,A) ~ (s g, B).  BFS from (e,A), (e,B) (Cor. 2.3).  Written from scratch for the referee report."""
import sys, re, numpy as np, time

def field(q, p, poly):
    if poly is None:
        a = np.arange(q)
        return (a[:, None] + a[None, :]) % q, (a[:, None] * a[None, :]) % q
    k = len(poly) - 1                       # poly: coefficient list low->high, monic
    digs = [[(x // p**i) % p for i in range(k)] for x in range(q)]
    enc = lambda v: sum(int(c) * p**i for i, c in enumerate(v))
    add = np.array([[enc([(u + v) % p for u, v in zip(digs[x], digs[y])]) for y in range(q)] for x in range(q)])
    mul = np.zeros((q, q), dtype=np.int64)
    for x in range(q):
        for y in range(q):
            pr = [0] * (2 * k - 1)
            for i, u in enumerate(digs[x]):
                for j, v in enumerate(digs[y]):
                    pr[i + j] = (pr[i + j] + u * v) % p
            for d in range(len(pr) - 1, k - 1, -1):       # reduce mod poly
                c = pr[d]
                if c:
                    for i in range(k + 1):
                        pr[d - k + i] = (pr[d - k + i] - c * poly[i]) % p
            mul[x, y] = enc(pr[:k])
    return add, mul

class Mat:
    def __init__(self, kind, q, p, poly):
        self.q, self.kind = q, kind
        A, M = field(q, p, poly)
        self.A, self.M = A, M
        self.neg = np.array([int(np.where(A[x] == 0)[0][0]) for x in range(q)])
        self.inv = np.zeros(q, dtype=np.int64)
        for x in range(1, q):
            self.inv[x] = int(np.where(M[x] == 1)[0][0])
        one = 1
        # enumerate SL(2,q): all (a,b,c,d) with ad - bc = 1, by brute force over (a,b,c) then solving for d when a != 0,
        # and over (b,c,d) with a = 0 (then -bc = 1)
        els = []
        a, b, c = np.meshgrid(np.arange(q), np.arange(q), np.arange(q), indexing='ij')
        a, b, c = a.ravel(), b.ravel(), c.ravel()
        nz = a != 0
        aa, bb, cc = a[nz], b[nz], c[nz]
        dd = M[self.inv[aa], A[one, M[bb, cc]]]           # d = (1 + bc)/a
        els.append(np.stack([aa, bb, cc, dd], 1))
        b2, c2, d2 = np.meshgrid(np.arange(q), np.arange(q), np.arange(q), indexing='ij')
        b2, c2, d2 = b2.ravel(), c2.ravel(), d2.ravel()
        ok = self.neg[M[b2, c2]] == 1                      # a = 0: det = -bc
        els.append(np.stack([np.zeros(ok.sum(), dtype=np.int64), b2[ok], c2[ok], d2[ok]], 1))
        E = np.concatenate(els)
        det = A[M[E[:, 0], E[:, 3]], self.neg[M[E[:, 1], E[:, 2]]]]
        assert (det == 1).all()
        keys = self.canon(E)
        self.keys = np.unique(keys)
        exp = q * (q * q - 1) // (2 if (kind == 'psl' and q % 2) else 1)
        assert len(self.keys) == exp, (len(self.keys), exp)
        self.size = exp
        self.E = self.unkey(self.keys)
    def key(self, E):
        q = self.q
        return ((E[:, 0] * q + E[:, 1]) * q + E[:, 2]) * q + E[:, 3]
    def canon(self, E):
        k1 = self.key(E)
        if self.kind == 'psl' and self.q % 2:
            return np.minimum(k1, self.key(self.neg[E]))
        return k1
    def unkey(self, K):
        q = self.q
        return np.stack([K // q**3, K // q**2 % q, K // q % q, K % q], 1)
    def idx(self, E):
        K = self.canon(E)
        i = np.searchsorted(self.keys, K)
        assert (self.keys[np.minimum(i, len(self.keys) - 1)] == K).all(), "not in group"
        return i
    def lmul_perm(self, m):
        A, M, X = self.A, self.M, self.E
        a, b, c, d = m
        Y = np.stack([A[M[a, X[:, 0]], M[b, X[:, 2]]], A[M[a, X[:, 1]], M[b, X[:, 3]]],
                      A[M[c, X[:, 0]], M[d, X[:, 2]]], A[M[c, X[:, 1]], M[d, X[:, 3]]]], 1)
        P = self.idx(Y)
        assert len(np.unique(P)) == self.size
        return P
    def inverse(self, m):
        a, b, c, d = m
        return (d, self.neg[b], self.neg[c], a)

def parse_poly(s, p):
    # "x^2+2" -> coefficients low->high
    s = s.replace(' ', '')
    co = {}
    for t in s.split('+'):
        if 'x' in t:
            c, _, e = t.partition('x')
            c = int(c) if c else 1
            e = int(e[1:]) if e.startswith('^') else 1
        else:
            c, e = int(t), 0
        co[e] = co.get(e, 0) + c
    k = max(co)
    return [co.get(i, 0) % p for i in range(k + 1)]

def factor_of(kind, q, poly_str):
    p = q
    for t in range(2, q + 1):
        if q % t == 0:
            p = t; break
    poly = parse_poly(poly_str, p) if poly_str else None
    return Mat(kind, q, p, poly)

def main(path):
    t0 = time.time()
    lines = open(path).read().splitlines()
    h = lines[0].split()
    d, D = int(h[0]), int(h[1])
    i = 2; facs = []
    if h[i] == 'prod':
        i += 1
        for _ in range(2):
            kind, q = h[i], int(h[i + 1]); i += 2
            poly = None
            if h[i] == 'poly':
                poly = h[i + 1]; i += 2
            facs.append(factor_of(kind, q, poly))
    else:
        kind, q = h[i], int(h[i + 1]); i += 2
        poly = None
        if h[i] == 'poly':
            poly = h[i + 1]; i += 2
        facs.append(factor_of(kind, q, poly))
    assert h[i] == 'n'; n = int(h[i + 1])
    sizes = [f.size for f in facs]
    Qn = int(np.prod(sizes)); N = Qn * n
    gens = []
    for ln in lines[1:]:
        mats = re.findall(r'mat\((\d+),(\d+),(\d+),(\d+)\)', ln)
        z = re.search(r'z=(\d+)', ln)
        if mats:
            gens.append(([tuple(map(int, m)) for m in mats], int(z.group(1))))
    assert len(gens) == d, (len(gens), d)
    # forward/backward perms on Q (product index), and z shifts
    fw, bw, ts = [], [], []
    for mats, t in gens:
        Pf = [f.lmul_perm(m) for f, m in zip(facs, mats)]
        Pb = [f.lmul_perm(f.inverse(m)) for f, m in zip(facs, mats)]
        if len(facs) == 1:
            fw.append(Pf[0]); bw.append(Pb[0])
        else:
            s2 = sizes[1]
            I = np.arange(Qn)
            fw.append(Pf[0][I // s2] * s2 + Pf[1][I % s2]); bw.append(Pb[0][I // s2] * s2 + Pb[1][I % s2])
        ts.append(t)
    # distinct generators
    gid = []
    for mats, t in gens:
        ii = [int(f.idx(np.array([m]))[0]) for f, m in zip(facs, mats)]
        gi = ii[0] if len(ii) == 1 else ii[0] * sizes[1] + ii[1]
        gid.append(gi * n + t)
    assert len(set(gid)) == d, "repeated generator"
    eidx = [int(f.idx(np.array([[1, 0, 0, 1]]))[0]) for f in facs]
    e = (eidx[0] if len(eidx) == 1 else eidx[0] * sizes[1] + eidx[1]) * n
    ok = True
    for start in (0, 1):
        vis = [np.zeros(N, bool), np.zeros(N, bool)]
        vis[start][e] = True
        front = np.array([e], dtype=np.int64); side = start; ecc = 0
        for step in range(1, D + 1):
            x, z = front // n, front % n
            nb = []
            for P, B, t in zip(fw, bw, ts):
                if side == 0:
                    nb.append(P[x].astype(np.int64) * n + (z + t) % n)
                else:
                    nb.append(B[x].astype(np.int64) * n + (z - t) % n)
            nb = np.unique(np.concatenate(nb))
            ns = 1 - side
            nb = nb[~vis[ns][nb]]
            vis[ns][nb] = True
            if len(nb): ecc = step
            front = nb; side = ns
        ra, rb = int(vis[0].sum()), int(vis[1].sum())
        print(f"  from (e,{'AB'[start]}): A {ra}/{N}  B {rb}/{N}  ecc {ecc}")
        ok &= (ra == N and rb == N)
    print(('VALID' if ok else 'INVALID'), path.split('/')[-1], 'd', d, 'D', D, '|G|', N, 'vertices', 2 * N, '%.0fs' % (time.time() - t0))
    sys.stdout.flush()

if __name__ == "__main__":
  for pth in sys.argv[1:]:
    main(pth)
