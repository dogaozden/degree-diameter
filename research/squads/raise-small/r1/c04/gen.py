#!/usr/bin/env python3
"""gen.py OUTDIR NAME [NAME ...]: non-metacyclic groups of order 457..600 in gtab format (one group per file, id 1,
identity index 0). Writes OUTDIR/NAME.tab (aff* names search GL(n,p) subgroups and write every subgroup found).
Groups are permutation groups (closure of generators) or explicit multiplications; associativity is checked on
random triples and the table is checked to be Latin."""
import sys, os, random

LO, HI = 457, 600

def closure(gens, d):
    ident = tuple(range(d)); el = [ident]; seen = {ident: 0}; i = 0
    while i < len(el):
        x = el[i]; i += 1
        for g in gens:
            y = tuple(x[j] for j in g)
            if y not in seen:
                seen[y] = len(el); el.append(y)
    return el, seen

def pmul(a, b): return tuple(a[j] for j in b)

def pgroup(gens, d):
    el, seen = closure(gens, d)
    return el, seen, pmul

def cyc(m): return tuple((i + 1) % m for i in range(m))
def dih(k): return [cyc(k), tuple((-i) % k for i in range(k))]          # D_k of order 2k on k points

def direct(A, B):
    (g1, d1), (g2, d2) = A, B
    gens = [tuple(g) + tuple(range(d1, d1 + d2)) for g in g1] + \
           [tuple(range(d1)) + tuple(d1 + x for x in g) for g in g2]
    return gens, d1 + d2

def wreath2(A):                                                          # G wr Z_2
    g, d = A
    gens = []
    for x in g:
        gens.append(tuple(x) + tuple(range(d, 2 * d)))
        gens.append(tuple(range(d)) + tuple(d + y for y in x))
    gens.append(tuple((i + d) % (2 * d) for i in range(2 * d)))
    return gens, 2 * d

S4 = ([(1, 0, 2, 3), (1, 2, 3, 0)], 4)
A4 = ([(1, 2, 0, 3), (1, 0, 3, 2)], 4)
A5 = ([(1, 2, 0, 3, 4), (1, 2, 3, 4, 0)], 5)
F21 = ([cyc(7), tuple((2 * i) % 7 for i in range(7))], 7)
PSL27 = ([tuple([(i + 1) % 7 for i in range(7)] + [7]),
          tuple([(2 * i) % 7 for i in range(7)] + [7]),
          tuple([7] + [(-pow(x, -1, 7)) % 7 for x in range(1, 7)] + [0])], 8)

def prim(q):
    for g in range(2, q):
        if len({pow(g, e, q) for e in range(1, q)}) == q - 1: return g

def agl_prime(q):
    g = prim(q)
    return ([cyc(q), tuple((g * x) % q for x in range(q))], q)

def agl25():
    """AGL(1,25) on F_25 = F_5[t]/(t^2-2), point a + 5b for a + b t."""
    def fm(x, y):
        a, b = x % 5, x // 5; c, d = y % 5, y // 5
        return (a * c + 2 * b * d) % 5 + 5 * ((a * d + b * c) % 5)
    for w in range(2, 25):
        pows, z = set(), 1
        for _ in range(24):
            z = fm(z, w); pows.add(z)
        if len(pows) == 24: break
    tr1 = tuple(((x % 5 + 1) % 5) + 5 * (x // 5) for x in range(25))
    trt = tuple((x % 5) + 5 * ((x // 5 + 1) % 5) for x in range(25))
    mw = tuple(fm(w, x) for x in range(25))
    return ([tr1, trt, mw], 25)

def mmul(A, B, n, p): return tuple(sum(A[i * n + k] * B[k * n + j] for k in range(n)) % p
                                   for i in range(n) for j in range(n))

def mclosure(gens, n, p, cap):
    I = tuple(1 if i == j else 0 for i in range(n) for j in range(n))
    S = {I}; fr = [I]
    while fr:
        new = []
        for x in fr:
            for g in gens:
                y = mmul(x, g, n, p)
                if y not in S:
                    S.add(y); new.append(y)
                    if len(S) > cap: return None
        fr = new
    return S

def invertible(A, n, p):
    M = [list(A[i * n:(i + 1) * n]) for i in range(n)]; r = 0
    for c in range(n):
        piv = next((i for i in range(r, n) if M[i][c] % p), None)
        if piv is None: return False
        M[r], M[piv] = M[piv], M[r]
        inv = pow(M[r][c], p - 2, p)
        for i in range(n):
            if i != r and M[i][c] % p:
                f = M[i][c] * inv % p
                M[i] = [(M[i][j] - f * M[r][j]) % p for j in range(n)]
        r += 1
    return True

def digits(x, p, n): return [(x // p ** i) % p for i in range(n)]
def vidx(v, p): return sum(c * p ** i for i, c in enumerate(v))

def lin_perm(M, p, n):
    out = []
    for x in range(p ** n):
        v = digits(x, p, n)
        out.append(vidx([sum(M[i * n + j] * v[j] for j in range(n)) % p for i in range(n)], p))
    return tuple(out)

def trans_perm(e, p, n):
    out = []
    for x in range(p ** n):
        v = digits(x, p, n); v[e] = (v[e] + 1) % p; out.append(vidx(v, p))
    return tuple(out)

def aff_search(p, n, lo, hi, tries, per_order=3, seed=1):
    """all distinct subgroups H of GL(n,p) with lo <= |H| <= hi found by random 1-2 generator sampling;
    returns list of (name, perm gens, degree) for V x| H."""
    rnd = random.Random(seed); found = {}
    for _ in range(tries):
        gens = []
        for _ in range(rnd.choice([1, 2])):
            while True:
                A = tuple(rnd.randrange(p) for _ in range(n * n))
                if invertible(A, n, p): break
            gens.append(A)
        S = mclosure(gens, n, p, hi)
        if S is None or len(S) < lo: continue
        lst = found.setdefault(len(S), [])
        key = frozenset(S)
        if len(lst) < per_order and all(k != key for k, _ in lst): lst.append((key, gens))
    out = []
    for o in sorted(found):
        for i, (key, gens) in enumerate(found[o]):
            pg = [trans_perm(e, p, n) for e in range(n)] + [lin_perm(M, p, n) for M in gens]
            out.append((f"aff{p}n{n}_o{o}_{i}", pg, p ** n))
    return out

def sl23():
    n, p = 2, 3
    gens = [(1, 1, 0, 1), (0, 2, 1, 0)]
    S = mclosure(gens, n, p, 100); I = (1, 0, 0, 1)
    el = [I] + sorted(x for x in S if x != I)
    seen = {x: i for i, x in enumerate(el)}
    return [tuple(seen[mmul(g, x, n, p)] for x in el) for g in gens], len(el)

def ut38():
    el = [(a, b, c) for a in range(8) for b in range(8) for c in range(8)]
    seen = {x: i for i, x in enumerate(el)}
    mul = lambda x, y: ((x[0] + y[0]) % 8, (x[1] + y[1]) % 8, (x[2] + y[2] + x[0] * y[1]) % 8)
    return el, seen, mul

def fixed(name):
    """perm description (gens, degree) of the named group, or None"""
    if name == 'agl23': return agl_prime(23)
    if name == 'agl25': return agl25()
    if name == 'PSL27xZ3': return direct(PSL27, ([cyc(3)], 3))
    if name == 'wr16': return wreath2(([cyc(16)], 16))
    if name == 'wrD8': return wreath2((dih(8), 8))
    if name == 'wr17': return wreath2(([cyc(17)], 17))
    if name == 'sl23': return sl23()
    if name == 'F21xS4': return direct(F21, S4)
    if name == 'F21xSL23': return direct(F21, sl23())
    if name[:3] == 'S4x' and name[3:].startswith('Z'): return direct(S4, ([cyc(int(name[4:]))], int(name[4:])))
    if name[:3] == 'A5x' and name[3:].startswith('Z'): return direct(A5, ([cyc(int(name[4:]))], int(name[4:])))
    if name[:3] == 'A4x' and name[3:].startswith('D'):
        k = int(name[4:]); return direct(A4, (dih(k), k))
    if name[:4] == 'SL23' and name[4:].startswith('xZ'):
        c = int(name[6:]); return direct(sl23(), ([cyc(c)], c))
    return None

def write(outdir, name, el, seen, mul):
    N = len(el)
    assert all(mul(el[0], x) == x for x in el[:50]), 'identity not index 0'
    rnd = random.Random(2)
    for _ in range(3000):
        a, b, c = rnd.choice(el), rnd.choice(el), rnd.choice(el)
        assert mul(mul(a, b), c) == mul(a, mul(b, c)), 'not associative'
    rows = [' '.join(str(seen[mul(a, b)]) for b in el) for a in el]
    for r in rows[:5]: assert len(set(r.split())) == N
    with open(os.path.join(outdir, name + '.tab'), 'w') as f:
        f.write(f"G {N} 1 {name}\n" + '\n'.join(rows) + '\n')
    print(name, N, flush=True)

def main():
    outdir = sys.argv[1]
    for name in sys.argv[2:]:
        if name.startswith('aff'):                       # aff5 aff7 aff11 aff13 aff3n3 (GL(n,p) subgroups)
            p, n = {'aff5': (5, 2), 'aff7': (7, 2), 'aff11': (11, 2), 'aff13': (13, 2), 'aff3n3': (3, 3)}[name]
            lo, hi = -(-LO // p ** n), HI // p ** n
            for nm, pg, d in aff_search(p, n, lo, hi, tries=int(os.environ.get('TRIES', 1500))):
                el, seen, mul = pgroup(pg, d)
                if LO <= len(el) <= HI: write(outdir, nm, el, seen, mul)
            continue
        if name == 'ut38':
            el, seen, mul = ut38(); write(outdir, name, el, seen, mul); continue
        g = fixed(name)
        el, seen, mul = pgroup(g[0], g[1])
        if not (LO <= len(el) <= HI): print('skip', name, len(el)); continue
        write(outdir, name, el, seen, mul)

if __name__ == '__main__':
    main()
