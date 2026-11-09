"""Independent check of a haar_sym solution for G = SL(2,q1) x SL(2,q2) x Z_n (q1, q2 prime powers).
usage: python3 haarcheck_prod.py SOL.txt [WORKDIR]
Reads the solution header "d D prod sl q1 [poly P] sl q2 [poly P] n NCYC N NTOT" and the lines "<idx> prod[mat(a,b,c,d);mat(..)] z=Z"
(field elements as integers sum c_i p^i, matrices [[a,b],[c,d]], the same convention as haar_sym).  It builds the factor
groups from the definitions (all 2x2 matrices of determinant 1 over GF(q)), the left-multiplication tables of the d
generators (and their inverses) and calls ./haarcheck_prod (C BFS) on them.  Nothing is taken from haar_sym's own code.
Output: the C program's verdict line (VALID / INVALID), and the generator table file next to the solution."""
import sys, os, re, subprocess

def smallest_irreducible(p, k):
    """monic irreducible polynomial of degree k over GF(p), coefficients low->high (k=1 not needed)."""
    import itertools
    for tail in itertools.product(range(p), repeat=k):
        poly = list(tail) + [1]
        if poly[0] == 0 and k > 0: continue
        if is_irreducible(poly, p): return poly
    raise ValueError

def is_irreducible(poly, p):
    k = len(poly) - 1
    for dd in range(1, k // 2 + 1):
        import itertools
        for g in itertools.product(range(p), repeat=dd):
            g = list(g) + [1]
            if polymod(poly, g, p) == [0] * (dd + 1) or all(c == 0 for c in polymod(poly, g, p)):
                return False
    return True

def polymod(a, m, p):
    a = list(a)
    while len(a) >= len(m):
        c = a[-1] * pow(m[-1], -1, p) % p
        sh = len(a) - len(m)
        for i, mc in enumerate(m): a[sh + i] = (a[sh + i] - c * mc) % p
        a.pop()
    return a + [0] * (len(m) - 1 - len(a))

class GF:
    def __init__(self, q, poly=None):
        p = next(x for x in range(2, q + 1) if q % x == 0)
        k = 0; t = q
        while t > 1: t //= p; k += 1
        assert p ** k == q, "q must be a prime power"
        self.p, self.k, self.q = p, k, q
        if k == 1: self.poly = None
        else:
            self.poly = [int(c) for c in poly] if poly is not None else smallest_irreducible(p, k)
        self.digits = lambda x: [(x // p ** i) % p for i in range(k)]
        self.undigits = lambda v: sum(c * p ** i for i, c in enumerate(v))
        self.ADD = [[self.undigits([(u + v) % p for u, v in zip(self.digits(a), self.digits(b))]) for b in range(q)] for a in range(q)]
        self.MUL = [[self._mul(a, b) for b in range(q)] for a in range(q)]
        self.NEG = [self.undigits([(-u) % p for u in self.digits(a)]) for a in range(q)]

    def _mul(self, a, b):
        p, k = self.p, self.k
        if k == 1: return a * b % p
        prod = [0] * (2 * k - 1)
        da, db = self.digits(a), self.digits(b)
        for i, u in enumerate(da):
            for j, v in enumerate(db): prod[i + j] = (prod[i + j] + u * v) % p
        return self.undigits(polymod(prod, self.poly, p))

def parse_poly(s):
    """'x^4+x+1' -> coefficients low->high"""
    coeffs = {}
    for term in s.split('+'):
        m = re.fullmatch(r'(\d*)x(?:\^(\d+))?|(\d+)', term)
        if not m: raise ValueError(term)
        if m.group(3) is not None: e, c = 0, int(m.group(3))
        else: e, c = int(m.group(2) or 1), int(m.group(1) or 1)
        coeffs[e] = coeffs.get(e, 0) + c
    deg = max(coeffs)
    return [coeffs.get(i, 0) for i in range(deg + 1)]

def sl_elements(F):
    q = F.q; els = []
    for a in range(q):
        for b in range(q):
            for c in range(q):
                for d in range(q):
                    if F.ADD[F.MUL[a][d]][F.NEG[F.MUL[b][c]]] == 1: els.append((a, b, c, d))
    return els

def mat_mul(F, x, y):
    a, b, c, d = x; e, f, g, h = y; A, M, Ad = F.ADD, F.MUL, F.NEG
    return (A[M[a][e]][M[b][g]], A[M[a][f]][M[b][h]], A[M[c][e]][M[d][g]], A[M[c][f]][M[d][h]])

def mat_inv(F, x):
    a, b, c, d = x
    return (d, F.NEG[b], F.NEG[c], a)

def main():
    sol = sys.argv[1]
    lines = open(sol).read().strip().split('\n')
    head = lines[0].split()
    d, D = int(head[0]), int(head[1])
    assert head[2] == 'prod', 'not a prod solution'
    i = 3; facs = []
    while head[i] != 'n':
        assert head[i] == 'sl', 'only sl factors supported'
        q = int(head[i + 1]); i += 2; poly = None
        if head[i] == 'poly': poly = parse_poly(head[i + 1]); i += 2
        facs.append((q, poly))
    assert len(facs) == 2
    n = int(head[i + 1])
    FA = GF(facs[0][0], facs[0][1]); FB = GF(facs[1][0], facs[1][1])
    EA = sl_elements(FA); EB = sl_elements(FB)
    IA = {x: t for t, x in enumerate(EA)}; IB = {x: t for t, x in enumerate(EB)}
    idA = IA[(1, 0, 0, 1)]; idB = IB[(1, 0, 0, 1)]
    gens = []
    for line in lines[1:1 + d]:
        m = re.fullmatch(r'\s*\d+\s+prod\[mat\((\d+),(\d+),(\d+),(\d+)\);mat\((\d+),(\d+),(\d+),(\d+)\)\]\s+z=(\d+)\s*', line)
        if not m: raise ValueError('cannot parse generator line: ' + line)
        v = [int(t) for t in m.groups()]
        ga = tuple(v[0:4]); gb = tuple(v[4:8]); z = v[8]
        assert ga in IA and gb in IB, 'generator not in SL(2,q): ' + line
        gens.append((ga, gb, z))
    assert len(gens) == d and len(set(gens)) == d, 'generators not distinct'
    NA, NB = len(EA), len(EB)
    out = []
    out.append('%d %d %d %d %d' % (NA, NB, n, d, D))
    for ga, gb, z in gens:
        out.append(str(z))
        ta = [IA[mat_mul(FA, ga, x)] for x in EA]; out.append(' '.join(map(str, ta)))
        tai = [IA[mat_mul(FA, mat_inv(FA, ga), x)] for x in EA]; out.append(' '.join(map(str, tai)))
        tb = [IB[mat_mul(FB, gb, y)] for y in EB]; out.append(' '.join(map(str, tb)))
        tbi = [IB[mat_mul(FB, mat_inv(FB, gb), y)] for y in EB]; out.append(' '.join(map(str, tbi)))
    out.append('%d %d' % (idA, idB))
    base = os.path.splitext(sol)[0]
    tab = base + '.prodtable.txt'
    open(tab, 'w').write('\n'.join(out) + '\n')
    here = os.path.dirname(os.path.abspath(__file__))
    exe = os.path.join(here, 'haarcheck_prod')
    res = subprocess.run([exe, tab], capture_output=True, text=True)
    print(res.stdout.strip()); print(res.stderr.strip()) if res.stderr.strip() else None
    print('table', tab)
    return res.returncode

if __name__ == '__main__':
    sys.exit(main())
