"""Universal 4-letter charts over F_q^4 (no singular nonbacktracking 4-pattern on either side) for prime powers
q in [LO, HI].  Random charts with A_0 = I; for q >= 128 a random chart is universal with probability >~ 1/6.
Each found chart is re-verified with the walk rules (Lemma 1), independently of the Lemma 2 shortcut used in the
search.  Field: prime fields mod p; prime powers with base-p digit vectors and log/exp tables.
usage: python3 universal_large.py LO HI outdir"""
import sys, random, itertools, os
from gf import find_irreducible, IRRED

def factor_pp(q):
    for p in range(2, q + 1):
        if q % p == 0:
            e, r = 0, q
            while r % p == 0: r //= p; e += 1
            return (p, e) if r == 1 else None
def prime_factors(n):
    out, d = set(), 2
    while d * d <= n:
        while n % d == 0: out.add(d); n //= d
        d += 1
    if n > 1: out.add(n)
    return out

class Field:
    def __init__(self, q):
        self.q = q; p, e = factor_pp(q); self.p, self.e = p, e
        if e == 1:
            self.add = lambda a, b: (a + b) % p; self.sub = lambda a, b: (a - b) % p
            self.mul = lambda a, b: (a * b) % p; self.inv = lambda a: pow(a, p - 2, p)
            return
        f = IRRED[q] if q in IRRED else find_irreducible(p, e)   # same polynomial as gf.py and the C tables
        dig = lambda a: [(a // p ** i) % p for i in range(e)]
        code = lambda d: sum(c * p ** i for i, c in enumerate(d))
        def pmul(a, b):
            da, db = dig(a), dig(b); r = [0] * (2 * e - 1)
            for i, x in enumerate(da):
                if x:
                    for j, y in enumerate(db): r[i + j] = (r[i + j] + x * y) % p
            for d in range(2 * e - 2, e - 1, -1):
                c = r[d]
                if c:
                    for t in range(e + 1): r[d - e + t] = (r[d - e + t] - c * f[t]) % p
            return code(r[:e])
        # primitive element and log tables
        pf = prime_factors(q - 1)
        def order_ok(g):
            for r in pf:
                x, n, base = 1, (q - 1) // r, g
                while n:
                    if n & 1: x = pmul(x, base)
                    base = pmul(base, base); n >>= 1
                if x == 1: return False
            return True
        g = next(c for c in range(2, q) if order_ok(c))
        exp = [1] * (2 * q); x = 1
        for i in range(q - 1): exp[i] = x; x = pmul(x, g)
        for i in range(q - 1, 2 * q): exp[i] = exp[i - (q - 1)]
        log = [0] * q
        for i in range(q - 1): log[exp[i]] = i
        self.exp, self.log = exp, log
        self.digits = [dig(a) for a in range(q)]
        self.add = lambda a, b: code([(x + y) % p for x, y in zip(self.digits[a], self.digits[b])])
        self.sub = lambda a, b: code([(x - y) % p for x, y in zip(self.digits[a], self.digits[b])])
        self.mul = lambda a, b: 0 if a == 0 or b == 0 else exp[log[a] + log[b]]
        self.inv = lambda a: exp[(q - 1 - log[a]) % (q - 1)]

def rank(F, vecs):
    rows = [list(v) for v in vecs]; r = 0; n = len(rows[0])
    for c in range(n):
        piv = next((i for i in range(r, len(rows)) if rows[i][c]), None)
        if piv is None: continue
        rows[r], rows[piv] = rows[piv], rows[r]
        iv = F.inv(rows[r][c]); rows[r] = [F.mul(iv, x) for x in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][c]:
                fct = rows[i][c]; rows[i] = [F.sub(x, F.mul(fct, y)) for x, y in zip(rows[i], rows[r])]
        r += 1
    return r
def matvec(F, M, v):
    out = []
    for row in M:
        s = 0
        for a, b in zip(row, v): s = F.add(s, F.mul(a, b))
        out.append(s)
    return out
def matmul(F, M, N):
    return [[matvec(F, M, [N[t][c] for t in range(len(N))])[r] for c in range(len(N[0]))] for r in range(len(M))]
def matinv(F, M):
    n = len(M); A = [list(M[r]) + [int(r == c) for c in range(n)] for r in range(n)]
    for c in range(n):
        piv = next((i for i in range(c, n) if A[i][c]), None)
        if piv is None: return None
        A[c], A[piv] = A[piv], A[c]; iv = F.inv(A[c][c]); A[c] = [F.mul(iv, x) for x in A[c]]
        for i in range(n):
            if i != c and A[i][c]:
                fct = A[i][c]; A[i] = [F.sub(x, F.mul(fct, y)) for x, y in zip(A[i], A[c])]
    return [row[n:] for row in A]

K = 4
PATS = [p for p in itertools.product(range(K), repeat=4) if p[0] != p[1] and p[1] != p[2] and p[2] != p[3]]
def singular_shortcut(F, A, Ai, b):
    """Lemma 2: side A pattern (i1..i4) nonsingular iff A_i2^-1 b_i1, A_i2^-1 b_i2, A_i3^-1 b_i3, A_i3^-1 b_i4 independent;
       side B iff A_i2 A_i1^-1 b_i1, b_i2, b_i3, A_i3 A_i4^-1 b_i4 independent"""
    w = [matvec(F, Ai[c], b[c]) for c in range(K)]
    Aib = {(j, i): matvec(F, Ai[j], b[i]) for j in range(K) for i in range(K)}
    Aw = {(j, i): matvec(F, A[j], w[i]) for j in range(K) for i in range(K)}
    bad = 0
    for i1, i2, i3, i4 in PATS:
        if rank(F, [Aib[(i2, i1)], Aib[(i2, i2)], Aib[(i3, i3)], Aib[(i3, i4)]]) < 4: bad += 1
        if rank(F, [Aw[(i2, i1)], b[i2], b[i3], Aw[(i3, i4)]]) < 4: bad += 1
    return bad
def singular_walk(F, A, Ai, b):
    """independent check from the walk rules: A->B: S -> A_c S + <b_c>; B->A: S -> A_c^-1 S + <w_c>"""
    w = [matvec(F, Ai[c], b[c]) for c in range(K)]; bad = 0
    for side in 'AB':
        for pat in PATS:
            S = []; s = side
            for c in pat:
                if s == 'A': S = [matvec(F, A[c], v) for v in S] + [b[c]]; s = 'B'
                else: S = [matvec(F, Ai[c], v) for v in S] + [w[c]]; s = 'A'
            if rank(F, S) < 4: bad += 1
    return bad
def search(q, rng, tries=4000):
    F = Field(q); I = [[int(r == c) for c in range(4)] for r in range(4)]
    for t in range(tries):
        A = [I]
        while len(A) < K:
            M = [[rng.randrange(q) for _ in range(4)] for _ in range(4)]
            if matinv(F, M) is not None: A.append(M)
        b = [[rng.randrange(q) for _ in range(4)] for _ in range(K)]
        if any(not any(v) for v in b): continue
        Ai = [matinv(F, M) for M in A]
        if singular_shortcut(F, A, Ai, b) == 0:
            assert singular_walk(F, A, Ai, b) == 0, 'shortcut and walk rules disagree'
            return A, b, t + 1
    return None
if __name__ == '__main__':
    lo, hi, outdir = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]; os.makedirs(outdir, exist_ok=True)
    rng = random.Random(lo * 7919 + hi)
    for q in range(lo, hi + 1):
        if factor_pp(q) is None: continue
        path = os.path.join(outdir, 'k4_q%d.txt' % q)
        if os.path.exists(path): print('q=%d exists' % q); continue
        res = search(q, rng)
        if res is None: print('q=%d NOT FOUND' % q, flush=True); continue
        A, b, t = res
        with open(path, 'w') as f:
            for M in A: f.write(' '.join(str(x) for row in M for x in row) + '\n')
            for v in b: f.write(' '.join(map(str, v)) + '\n')
        print('q=%d universal chart after %d random tries (walk-rule check: 0 singular)' % (q, t), flush=True)
