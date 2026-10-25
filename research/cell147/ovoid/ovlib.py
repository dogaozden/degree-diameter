"""ovlib.py: explicit isometry groups of Q(6,q), q odd prime, for orbit-union searches (orbclq.c).

Standard form (hexgen / Tits coordinates): Q(x) = x0x4 + x1x5 + x2x6 - x3^2, polar form
B(x,y) = x^T G y with G[0,4]=G[1,5]=G[2,6]=1 (symmetric), G[3,3] = -2.  Matrices act on column vectors.

Blocks of an orthogonal decomposition (each with its maximal torus, a cyclic group):
  'H'  hyperbolic plane,                 torus order q-1   (diag(l, 1/l))
  'E'  elliptic plane  = F_{q^2}, Q = N,  torus order q+1   (multiplication by norm-1 elements)
  'H4' W + W*, W = F_{q^2},               torus order q^2-1 (l on W, l^-T on W*)
  'E4' F_{q^4}, Q = Tr_{q^2/q}(d N),      torus order q^2+1
  'H6' W + W*, W = F_{q^3},               torus order q^3-1
  'E6' F_{q^6}, Q = Tr_{q^3/q}(d N),      torus order q^3+1
  'L'  one-dimensional, Q = c x^2         (only +-1)
torus(types, q) returns (gens, orders, P): one generator matrix per block (7x7, standard coordinates, an isometry of G),
of the given cyclic orders, all commuting.  Any element of the torus is prod gens[i]^e_i.
"""
import itertools, random

def inv(a, q): return pow(a % q, q - 2, q)

def mat_mul(A, B, q):
    n, m, p = len(A), len(B), len(B[0])
    return [[sum(A[i][k] * B[k][j] for k in range(m)) % q for j in range(p)] for i in range(n)]

def mat_T(A): return [list(r) for r in zip(*A)]

def mat_id(n): return [[int(i == j) for j in range(n)] for i in range(n)]

def mat_inv(A, q):
    n = len(A); M = [list(r) + mat_id(n)[i] for i, r in enumerate(A)]
    for c in range(n):
        p = next(i for i in range(c, n) if M[i][c] % q)
        M[c], M[p] = M[p], M[c]
        s = inv(M[c][c], q); M[c] = [x * s % q for x in M[c]]
        for i in range(n):
            if i != c and M[i][c]:
                f = M[i][c]; M[i] = [(x - f * y) % q for x, y in zip(M[i], M[c])]
    return [r[n:] for r in M]

def mat_pow(A, e, q):
    R = mat_id(len(A)); X = A
    while e:
        if e & 1: R = mat_mul(R, X, q)
        X = mat_mul(X, X, q); e >>= 1
    return R

def mat_order(A, q, limit=10**7):
    I = mat_id(len(A)); X = A; k = 1
    while X != I:
        X = mat_mul(X, A, q); k += 1
        if k > limit: return None
    return k

def std_gram(q):
    G = [[0] * 7 for _ in range(7)]
    for i, j in ((0, 4), (1, 5), (2, 6)): G[i][j] = G[j][i] = 1
    G[3][3] = (-2) % q
    return G

def is_isometry(M, G, q):
    return mat_mul(mat_mul(mat_T(M), G, q), M, q) == [[x % q for x in r] for r in G]

# ---------------- finite fields F_{q^k} as F_q[t]/(f) ----------------
class GF:
    def __init__(self, q, k):
        self.q, self.k = q, k
        self.f = self._irreducible() if k > 1 else [0, 1]
    def _irreducible(self):
        q, k = self.q, self.k
        for coeffs in itertools.product(range(q), repeat=k):
            f = list(coeffs) + [1]           # monic, degree k
            if f[0] == 0: continue
            if self._is_irred(f): return f
    def _is_irred(self, f):
        q, k = self.q, self.k
        # no roots in subfields: check gcd(x^(q^i) - x, f) = 1 for i <= k/2
        x = [0, 1]
        xp = x
        for i in range(1, k // 2 + 1):
            xp = self._polypowmod(xp, q, f)
            d = self._polysub(xp, x)
            if self._deg(self._polygcd(d, f)) > 0: return False
        return True
    def _deg(self, a):
        a = self._trim(a); return len(a) - 1
    def _trim(self, a):
        a = list(a)
        while len(a) > 1 and a[-1] % self.q == 0: a.pop()
        return a
    def _polysub(self, a, b):
        n = max(len(a), len(b)); return self._trim([((a[i] if i < len(a) else 0) - (b[i] if i < len(b) else 0)) % self.q for i in range(n)])
    def _polymulmod(self, a, b, f):
        q = self.q; r = [0] * (len(a) + len(b) - 1)
        for i, x in enumerate(a):
            if x:
                for j, y in enumerate(b): r[i + j] = (r[i + j] + x * y) % q
        return self._polymod(r, f)
    def _polymod(self, a, f):
        q = self.q; a = list(a); df = len(f) - 1
        for i in range(len(a) - 1, df - 1, -1):
            c = a[i] % q
            if c:
                for j in range(df + 1): a[i - df + j] = (a[i - df + j] - c * f[j]) % q
        a = a[:df] if len(a) > df else a + [0] * (df - len(a))
        return a
    def _polypowmod(self, a, e, f):
        r = [1] + [0] * (len(f) - 2); x = self._polymod(a, f)
        while e:
            if e & 1: r = self._polymulmod(r, x, f)
            x = self._polymulmod(x, x, f); e >>= 1
        return r
    def _polygcd(self, a, b):
        a, b = self._trim(a), self._trim(b)
        while self._deg(b) >= 0 and any(b):
            # a mod b
            q = self.q; a = list(a); db = self._deg(b); lb = inv(b[db], q)
            while self._deg(a) >= db and any(a):
                da = self._deg(a); c = a[da] * lb % q
                for j in range(db + 1): a[da - db + j] = (a[da - db + j] - c * b[j]) % q
                a = self._trim(a)
            a, b = b, a
        return a
    # elements: lists of k coefficients
    def mul(self, a, b): return self._polymulmod(a, b, self.f)
    def add(self, a, b): return [(x + y) % self.q for x, y in zip(a, b)]
    def pow(self, a, e): return self._polypowmod(a, e, self.f)
    def one(self): return [1] + [0] * (self.k - 1)
    def elem(self, i):  # i-th element in lexicographic order
        out = []
        for _ in range(self.k): out.append(i % self.q); i //= self.q
        return out
    def all_elems(self):
        for i in range(self.q ** self.k): yield self.elem(i)
    def mulmat(self, a):
        """k x k matrix of x -> a x (columns = images of basis t^j)."""
        cols = [self.mul(a, [int(i == j) for i in range(self.k)]) for j in range(self.k)]
        return [[cols[j][i] for j in range(self.k)] for i in range(self.k)]
    def primitive(self):
        q, k = self.q, self.k; n = q ** k - 1
        ps = [p for p in range(2, n + 1) if n % p == 0 and all(p % r for r in range(2, int(p ** 0.5) + 1))]
        for i in range(1, q ** k):
            a = self.elem(i)
            if all(self.pow(a, n // p) != self.one() for p in ps): return a
    def trace_to(self, a, sub):
        """Tr_{q^k / q^sub}(a) = sum a^(q^(sub*i)), i < k/sub."""
        r = [0] * self.k; x = a
        for i in range(self.k // sub):
            r = self.add(r, x); x = self.pow(x, self.q ** sub)
        return r

def _is_square(a, q): return a % q == 0 or pow(a % q, (q - 1) // 2, q) == 1

def _nonsquare(q): return next(a for a in range(2, q) if not _is_square(a, q))

def block(kind, q):
    """returns (gram, torus_generator, order) in block coordinates."""
    if kind == 'H':
        g = next(x for x in range(2, q) if mat_order([[x]], q) == q - 1) if q > 2 else 1
        return [[0, 1], [1, 0]], [[g, 0], [0, inv(g, q)]], q - 1
    if kind == 'L':
        return [[2]], [[q - 1]], 2
    if kind in ('E', 'E4', 'E6'):
        k = {'E': 2, 'E4': 4, 'E6': 6}[kind]; F = GF(q, k); h = k // 2
        # Q(x) = Tr_{q^h/q}(d * x^(q^h + 1)); for E (h=1) d = 1
        def Qf(x):
            nx = F.pow(x, q ** h + 1)
            return F.trace_to(F.mul(d, nx), 1)[0] % q
        # choose d in F_{q^h} (embedded in F_{q^k}) so that Q is nondegenerate; d = 1 works generically
        d = F.one()
        basis = [[int(i == j) for i in range(k)] for j in range(k)]
        def Bf(x, y): return (Qf(F.add(x, y)) - Qf(x) - Qf(y)) % q
        gram = [[Bf(basis[i], basis[j]) for j in range(k)] for i in range(k)]
        # torus: mu = prim^((q^k - 1)/(q^h + 1)) has order q^h + 1 and norm 1
        pr = F.primitive(); mu = F.pow(pr, (q ** k - 1) // (q ** h + 1))
        t = F.mulmat(mu)
        assert is_isometry(t, gram, q)
        return gram, t, q ** h + 1
    if kind in ('H4', 'H6'):
        k = {'H4': 2, 'H6': 3}[kind]; F = GF(q, k)
        pr = F.primitive(); m = F.mulmat(pr); mT = mat_T(mat_inv(m, q))
        n = 2 * k
        gram = [[0] * n for _ in range(n)]
        for i in range(k): gram[i][k + i] = gram[k + i][i] = 1
        t = [[0] * n for _ in range(n)]
        for i in range(k):
            for j in range(k): t[i][j] = m[i][j]; t[k + i][k + j] = mT[i][j]
        assert is_isometry(t, gram, q)
        return gram, t, q ** k - 1
    raise ValueError(kind)

def _diagonalize(S, q):
    """columns C with C^T S C = diag(1, ..., 1, d); returns (C, d)."""
    n = len(S)
    def Bv(x, y): return sum(x[i] * S[i][j] * y[j] for i in range(n) for j in range(n)) % q
    # orthogonal basis by Gram-Schmidt with non-isotropic pivots
    vecs = [[int(i == j) for i in range(n)] for j in range(n)]
    ortho = []
    rem = vecs
    while rem:
        piv = next((v for v in rem if Bv(v, v)), None)
        if piv is None:
            # all isotropic: use v + w with B(v, w) != 0
            found = False
            for a, b in itertools.combinations(range(len(rem)), 2):
                if Bv(rem[a], rem[b]):
                    piv = [(x + y) % q for x, y in zip(rem[a], rem[b])]; found = True; break
            assert found
        ortho.append(piv); dp = Bv(piv, piv); idp = inv(dp, q)
        new = []
        for v in rem:
            c = Bv(v, piv) * idp % q
            w = [(x - c * y) % q for x, y in zip(v, piv)]
            if any(w): new.append(w)
        # keep a basis of the complement: remove dependent vectors
        basis = []
        for w in new:
            M = basis + [w]
            if _rank(M, q) == len(M): basis.append(w)
        rem = basis
    # now ortho is an orthogonal basis with values d_i; combine pairs to make them 1
    vals = [Bv(v, v) for v in ortho]
    out = []
    i = 0
    while i < n - 1:
        v, w = ortho[i], ortho[i + 1]; a, b = vals[i], vals[i + 1]
        # find x, y with a x^2 + b y^2 = 1
        x, y = next((x, y) for x in range(q) for y in range(q) if (a * x * x + b * y * y) % q == 1)
        u = [(x * s + y * t) % q for s, t in zip(v, w)]
        # orthogonal complement of u in span(v, w): (-b y, a x) direction
        u2 = [(-b * y * s + a * x * t) % q for s, t in zip(v, w)]
        out.append(u)
        ortho[i + 1] = u2; vals[i + 1] = Bv(u2, u2)
        i += 1
    out.append(ortho[-1]); d = vals[-1]
    C = [[out[j][i] for j in range(n)] for i in range(n)]
    return C, d

def _rank(M, q):
    M = [list(r) for r in M]; r = 0; cols = len(M[0]) if M else 0
    for c in range(cols):
        p = next((i for i in range(r, len(M)) if M[i][c] % q), None)
        if p is None: continue
        M[r], M[p] = M[p], M[r]; s = inv(M[r][c], q); M[r] = [x * s % q for x in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c]: f = M[i][c]; M[i] = [(x - f * y) % q for x, y in zip(M[i], M[r])]
        r += 1
    return r

def _sqrt(a, q): return next(x for x in range(q) if x * x % q == a % q)

def torus(types, q=11):
    """types: list of block kinds whose dimensions sum to 7, e.g. ['E', 'H', 'H', 'L'] or ['E6', 'L'].
    Returns (gens, orders, P) with gens[i] the 7x7 torus generator of block i (identity elsewhere), as
    isometries of the standard form; P maps block coordinates to standard coordinates (P^T G P = mu G')."""
    blocks = [block(t, q) for t in types]
    dims = [len(b[0]) for b in blocks]; assert sum(dims) == 7, dims
    Gp = [[0] * 7 for _ in range(7)]; off = 0; offs = []
    for (g, t, o), d in zip(blocks, dims):
        offs.append(off)
        for i in range(d):
            for j in range(d): Gp[off + i][off + j] = g[i][j] % q
        off += d
    G = std_gram(q)
    C1, d1 = _diagonalize(G, q)
    # scale Gp by mu so that the discriminants agree
    C2, d2 = _diagonalize(Gp, q)
    mu = d1 * inv(d2, q) % q   # mu^7 ~ mu mod squares
    Gpm = [[x * mu % q for x in r] for r in Gp]
    C2, d2 = _diagonalize(Gpm, q)
    ratio = d1 * inv(d2, q) % q
    assert _is_square(ratio, q), 'discriminant mismatch'
    s = _sqrt(ratio, q)
    for i in range(7): C2[i][6] = C2[i][6] * s % q
    P = mat_mul(C1, mat_inv(C2, q), q)
    assert mat_mul(mat_mul(mat_T(P), G, q), P, q) == Gpm
    Pi = mat_inv(P, q)
    gens, orders = [], []
    for (g, t, o), d, off in zip(blocks, dims, offs):
        T = mat_id(7)
        for i in range(d):
            for j in range(d): T[off + i][off + j] = t[i][j] % q
        M = mat_mul(mat_mul(P, T, q), Pi, q)
        assert is_isometry(M, G, q)
        gens.append(M); orders.append(o)
    return gens, orders, P

def elem(gens, exps, q=11):
    M = mat_id(7)
    for g, e in zip(gens, exps):
        if e: M = mat_mul(M, mat_pow(g, e, q), q)
    return M

def write_gens(path, mats, comment=''):
    with open(path, 'w') as f:
        if comment: f.write('# ' + comment.replace('\n', '\n# ') + '\n')
        for k, M in enumerate(mats):
            f.write(f'# generator {k}\n')
            for r in M: f.write(' '.join(str(x) for x in r) + '\n')

def random_isometry(q=11, nref=8, rng=random):
    """product of nref random reflections of the standard form."""
    G = std_gram(q); M = mat_id(7)
    for _ in range(nref):
        while True:
            v = [rng.randrange(q) for _ in range(7)]
            Gv = [sum(G[i][j] * v[j] for j in range(7)) % q for i in range(7)]
            qv = sum(v[i] * Gv[i] for i in range(7)) % q   # = B(v, v) = 2 Q(v)
            if qv: break
        # reflection x -> x - 2 B(x,v)/B(v,v) v = x - (2/qv) v (Gv . x)
        c = 2 * inv(qv, q) % q
        R = [[(int(i == j) - c * v[i] * Gv[j]) % q for j in range(7)] for i in range(7)]
        M = mat_mul(M, R, q)
    return M

if __name__ == '__main__':
    q = 11
    for types in (['H', 'H', 'H', 'L'], ['E', 'H', 'H', 'L'], ['E', 'E', 'H', 'L'], ['E', 'E', 'E', 'L'],
                  ['H4', 'H', 'L'], ['H4', 'E', 'L'], ['E4', 'H', 'L'], ['E4', 'E', 'L'], ['H6', 'L'], ['E6', 'L']):
        gens, orders, P = torus(types, q)
        ok = all(mat_order(g, q) == o for g, o in zip(gens, orders))
        comm = all(mat_mul(a, b, q) == mat_mul(b, a, q) for a in gens for b in gens)
        print(types, orders, 'orders ok' if ok else 'ORDER MISMATCH', 'commute' if comm else 'NOT COMMUTING')

# ---------------- helpers for groups given in other coordinates ----------------
def invariant_forms(mats, q=11):
    """basis of the symmetric matrices S with M^T S M = S for every M in mats (solves a linear system)."""
    n = len(mats[0]); idx = [(i, j) for i in range(n) for j in range(i, n)]; nv = len(idx)
    rows = []
    for M in mats:
        MT = mat_T(M)
        for a in range(n):
            for b in range(a, n):
                # (M^T S M)[a][b] - S[a][b] = 0, linear in the S entries
                row = [0] * nv
                for k, (i, j) in enumerate(idx):
                    c = M[i][a] * M[j][b] + (M[j][a] * M[i][b] if i != j else 0)
                    row[k] = c % q
                row[idx.index((a, b))] = (row[idx.index((a, b))] - 1) % q
                rows.append(row)
    # null space
    Mx = [list(r) for r in rows]; piv = []; r = 0
    for c in range(nv):
        p = next((i for i in range(r, len(Mx)) if Mx[i][c] % q), None)
        if p is None: continue
        Mx[r], Mx[p] = Mx[p], Mx[r]; s = inv(Mx[r][c], q); Mx[r] = [x * s % q for x in Mx[r]]
        for i in range(len(Mx)):
            if i != r and Mx[i][c]: f = Mx[i][c]; Mx[i] = [(x - f * y) % q for x, y in zip(Mx[i], Mx[r])]
        piv.append(c); r += 1
    out = []
    for fc in [c for c in range(nv) if c not in piv]:
        v = [0] * nv; v[fc] = 1
        for i, c in enumerate(piv): v[c] = (-Mx[i][fc]) % q
        S = [[0] * n for _ in range(n)]
        for k, (i, j) in enumerate(idx): S[i][j] = S[j][i] = v[k]
        out.append(S)
    return out

def conjugate_to_standard(mats, gram, q=11):
    """mats preserve the nondegenerate symmetric 7x7 matrix gram (M^T gram M = gram, or a multiple of it).
    Returns (mats2, P) with mats2 = P M P^-1 preserving the standard form std_gram(q) (up to the same multiple)."""
    G = std_gram(q)
    C1, d1 = _diagonalize(G, q)
    C2, d2 = _diagonalize(gram, q)
    mu = d1 * inv(d2, q) % q
    gm = [[x * mu % q for x in r] for r in gram]
    C2, d2 = _diagonalize(gm, q)
    ratio = d1 * inv(d2, q) % q
    assert _is_square(ratio, q)
    s = _sqrt(ratio, q)
    for i in range(7): C2[i][6] = C2[i][6] * s % q
    P = mat_mul(C1, mat_inv(C2, q), q)
    assert mat_mul(mat_mul(mat_T(P), G, q), P, q) == gm
    Pi = mat_inv(P, q)
    return [mat_mul(mat_mul(P, M, q), Pi, q) for M in mats], P

def read_gens(path):
    vals = []
    for line in open(path):
        line = line.split('#')[0]
        vals += [int(x) for x in line.split()]
    assert len(vals) % 49 == 0
    return [[vals[49 * k + 7 * i: 49 * k + 7 * i + 7] for i in range(7)] for k in range(len(vals) // 49)]

def group_order(mats, q=11, limit=2 * 10 ** 6):
    """order of the group generated by mats (as matrices; projective order may be half), by closure. Small groups only."""
    I = tuple(map(tuple, mat_id(7)))
    seen = {I}; frontier = [I]
    while frontier:
        nf = []
        for X in frontier:
            for M in mats:
                Y = tuple(map(tuple, mat_mul([list(r) for r in X], M, q)))
                if Y not in seen:
                    seen.add(Y); nf.append(Y)
                    if len(seen) > limit: return None
        frontier = nf
    return len(seen)
