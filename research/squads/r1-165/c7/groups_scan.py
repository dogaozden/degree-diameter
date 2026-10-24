#!/usr/bin/env python3
"""C7 wildcard: exact-NB-4 Haar controllers H(G,S), |S| = 4, on NON-metacyclic groups of order 62..108.

The squad's metacyclic scan (research/theorems/squad165/meta_scan.log) covered only 2-generated groups.
Here we build many other groups (direct products, affine groups F_p^k : H, abelian groups of rank >= 3)
as permutation groups by closure, write each multiplication table, and run ctrl_exh (exhaustive over
S = {e, a, b, c}; covering of G by the 108 NB-4 words s1 s2^-1 s3 s4^-1, both sides).

usage: python3 -B groups_scan.py  (writes tables under /tmp/claude-0/c7/tables, prints one line per group)
"""
import os, random, subprocess, sys

random.seed(7)
TAB = '/tmp/claude-0/c7/tables'
CTRL = '/tmp/claude-0/c7/ctrl_exh'
MAXO = 108

# ---------- permutation-group helpers ----------
def ident(n):
    return tuple(range(n))

def pmul(p, q):
    return tuple(p[i] for i in q)  # (p*q)(i) = p(q(i))

def closure(gens, maxo=MAXO):
    n = len(gens[0])
    e = ident(n)
    elems = [e]; idx = {e: 0}; stack = [e]
    while stack:
        g = stack.pop()
        for s in gens:
            h = pmul(g, s)
            if h not in idx:
                idx[h] = len(elems); elems.append(h); stack.append(h)
                if len(elems) > maxo:
                    return None
    return elems, idx

def pad(gens, n_before, n_after):
    """embed permutations on disjoint support: identity on the first n_before and last n_after points"""
    out = []
    for g in gens:
        out.append(tuple(list(range(n_before)) + [n_before + x for x in g] + list(range(n_before + len(g), n_before + len(g) + n_after))))
    return out

def product(G1, G2):
    """direct product of two perm groups given as (gens, N)"""
    g1, n1 = G1; g2, n2 = G2
    a = [tuple(list(p) + list(range(n1, n1 + n2))) for p in g1]
    b = [tuple(list(range(n1)) + [n1 + x for x in p]) for p in g2]
    return a + b, n1 + n2

def cycle(n):
    return ([tuple(list(range(1, n)) + [0])] if n > 1 else [tuple(range(max(n, 1)))], max(n, 1))

def S3():
    return [(1, 2, 0), (1, 0, 2)], 3

def A4():
    return [(1, 2, 0, 3), (1, 0, 3, 2)], 4

def S4():
    return [(1, 2, 3, 0), (1, 0, 2, 3)], 4

def D(n):
    """dihedral group of order 2n on n points"""
    r = tuple((i + 1) % n for i in range(n))
    s = tuple((-i) % n for i in range(n))
    return [r, s], n

def Zc(n):
    return [tuple(list(range(1, n)) + [0])], n

def P(G):
    return G

# ---------- affine groups F_p^k : H ----------
def vec(x, p, k):
    return [(x // p ** i) % p for i in range(k)]

def enc(v, p):
    return sum((c % p) * p ** i for i, c in enumerate(v))

def affine(p, k, Ms):
    N = p ** k
    gens = []
    for i in range(k):
        e = [0] * k; e[i] = 1
        gens.append(tuple(enc([a + b for a, b in zip(vec(x, p, k), e)], p) for x in range(N)))
    for M in Ms:
        gens.append(tuple(enc([sum(M[r][c] * vec(x, p, k)[c] for c in range(k)) for r in range(k)], p) for x in range(N)))
    return gens, N

def mat_order(M, p, lim=200):
    k = len(M)
    I = [[int(i == j) for j in range(k)] for i in range(k)]
    X = [row[:] for row in M]
    for o in range(1, lim):
        if X == I:
            return o
        X = [[sum(X[i][t] * M[t][j] for t in range(k)) % p for j in range(k)] for i in range(k)]
    return None

def find_mat(p, k, order, tries=200000):
    for _ in range(tries):
        M = [[random.randrange(p) for _ in range(k)] for _ in range(k)]
        if mat_order(M, p) == order:
            return M
    raise RuntimeError('no matrix of order %d over F_%d^%d' % (order, p, k))

def block(*Bs):
    n = sum(len(B) for B in Bs)
    M = [[0] * n for _ in range(n)]
    o = 0
    for B in Bs:
        k = len(B)
        for i in range(k):
            for j in range(k):
                M[o + i][o + j] = B[i][j]
        o += k
    return M

# ---------- build the list ----------
groups = []

def add(name, G):
    groups.append((name, G))

# abelian and products with cyclic groups
add('Z2xZ2xZ16', product(product(Zc(2), Zc(2)), Zc(16)))
add('Z4xZ4xZ4', product(product(Zc(4), Zc(4)), Zc(4)))
add('Z2xZ4xZ8', product(product(Zc(2), Zc(4)), Zc(8)))
add('Z2^3xZ8', product(product(product(Zc(2), Zc(2)), Zc(2)), Zc(8)))
add('Z3^4', product(product(Zc(3), Zc(3)), product(Zc(3), Zc(3))))
add('Z3xZ3xZ12', product(product(Zc(3), Zc(3)), Zc(12)))
add('Z2xZ2xZ18', product(product(Zc(2), Zc(2)), Zc(18)))
add('Z2^3xZ12', product(product(product(Zc(2), Zc(2)), Zc(2)), Zc(12)))
add('Z3xZ3xZ8xZ... (Z3^2xZ2xZ4)', product(product(Zc(3), Zc(3)), product(Zc(2), Zc(4))))

# direct products of small non-abelian groups with cyclic / other factors
add('A4xZ6', product(A4(), Zc(6)))
add('A4xZ7', product(A4(), Zc(7)))
add('A4xZ8', product(A4(), Zc(8)))
add('A4xZ9', product(A4(), Zc(9)))
add('A4xZ2xZ4', product(A4(), product(Zc(2), Zc(4))))
add('A4xZ3xZ3', product(A4(), product(Zc(3), Zc(3))))
add('A4xZ2^3', product(A4(), product(product(Zc(2), Zc(2)), Zc(2))))
add('S4xZ3', product(S4(), Zc(3)))
add('S4xZ4', product(S4(), Zc(4)))
add('S4xZ2xZ2', product(S4(), product(Zc(2), Zc(2))))
add('D4xD4', product(D(4), D(4)))
add('D4xZ8', product(D(4), Zc(8)))
add('D4xZ2xZ4', product(D(4), product(Zc(2), Zc(4))))
add('D4xZ3xZ3', product(D(4), product(Zc(3), Zc(3))))
add('D8(16)xZ4', product(D(8), Zc(4)))
add('S3xS3xZ2', product(S3(), product(S3(), Zc(2))))
add('S3xS3xZ3', product(S3(), product(S3(), Zc(3))))
add('S3xZ12', product(S3(), Zc(12)))
add('S3xZ2xZ6', product(S3(), product(Zc(2), Zc(6))))
add('S3xZ2xZ2xZ3', product(S3(), product(product(Zc(2), Zc(2)), Zc(3))))
add('D5xD5', product(D(5), D(5)))
add('D5xZ2xZ5', product(D(5), product(Zc(2), Zc(5))))
add('D6xZ6', product(D(6), Zc(6)))
add('D6xZ7', product(D(6), Zc(7)))
add('D6xZ8', product(D(6), Zc(8)))
add('D6xZ9', product(D(6), Zc(9)))
add('D7xZ6', product(D(7), Zc(6)))
add('D7xZ4xZ2', product(D(7), product(Zc(4), Zc(2))))
add('D9xZ4', product(D(9), Zc(4)))
add('D9xZ2xZ2', product(D(9), product(Zc(2), Zc(2))))
add('D9xZ6', product(D(9), Zc(6)))
add('D18xZ2', product(D(18), Zc(2)))
add('D12xZ3', product(D(12), Zc(3)))
add('D12xZ6', product(D(12), Zc(6)))  # order 144, pruned below if too big

# SL(2,3), GL(2,3) acting on the 8 nonzero vectors of F_3^2 (faithful permutation action)
def mat_action_group(mats, p=3, k=2):
    vs = [v for v in range(p ** k) if v != 0]
    perms = []
    for M in mats:
        perms.append(tuple(vs.index(enc([sum(M[r][c] * vec(v, p, k)[c] for c in range(k)) for r in range(k)], p)) for v in vs))
    return perms, len(vs)

SL23 = mat_action_group([[[1, 1], [0, 1]], [[0, 2], [1, 0]]])
GL23 = mat_action_group([[[1, 1], [0, 1]], [[0, 2], [1, 0]], [[1, 0], [0, 2]]])
add('SL(2,3)xZ3', product(SL23, Zc(3)))
add('SL(2,3)xZ4', product(SL23, Zc(4)))
add('GL(2,3)xZ2', product(GL23, Zc(2)))

# affine groups F_p^k : H
# F_3^2 : H, H of order 8 in GL(2,3) (cyclic, quaternion, dihedral types found by search)
def subgroups_of_order(p, k, h, n_pairs=3000):
    """distinct subgroups of GL(k,p) of order h generated by at most two random elements (by closure)"""
    found = {}
    I = tuple(tuple(int(i == j) for j in range(k)) for i in range(k))
    def mm(A, B):
        return tuple(tuple(sum(A[i][t] * B[t][j] for t in range(k)) % p for j in range(k)) for i in range(k))
    pool = []
    while len(pool) < 400:
        M = tuple(tuple(random.randrange(p) for _ in range(k)) for _ in range(k))
        if mat_order([list(r) for r in M], p) is not None:
            pool.append(M)
    for _ in range(n_pairs):
        a = random.choice(pool); b = random.choice(pool)
        el = {I}; frontier = [I]
        ok = True
        while frontier and ok:
            X = frontier.pop()
            for g in (a, b):
                Y = mm(X, g)
                if Y not in el:
                    el.add(Y); frontier.append(Y)
                    if len(el) > h:
                        ok = False; break
        if ok and len(el) == h:
            key = frozenset(el)
            if key not in found:
                found[key] = (a, b)
    return list(found.values())

for (a, b) in subgroups_of_order(3, 2, 8)[:6]:
    add('F3^2:H8(%s,%s)' % (a, b), affine(3, 2, [[list(r) for r in a], [list(r) for r in b]]))

# F_5^2 : Z3 and Z4
add('F5^2:Z3', affine(5, 2, [[[0, 4], [1, 4]]]))
add('F5^2:Z4', affine(5, 2, [[[0, 4], [1, 0]]]))
# F_7^2 : Z2 (generalized dihedral, and Z7 x D7 type)
add('F7^2:-I', affine(7, 2, [[[6, 0], [0, 6]]]))
add('F7^2:diag(1,-1)', affine(7, 2, [[[1, 0], [0, 6]]]))
# F_2^4 : H
M5 = find_mat(2, 4, 5); add('F2^4:Z5', affine(2, 4, [M5]))
A3 = [[0, 1], [1, 1]]; U2 = [[1, 1], [0, 1]]
add('F2^4:S3(diag)', affine(2, 4, [block(A3, A3), block([[0, 1], [1, 0]], [[0, 1], [1, 0]])]))
add('F2^4:Z6', affine(2, 4, [block(A3, U2)]))
add('F2^4:Z4(J4)', affine(2, 4, [block([[1, 1, 0, 0], [0, 1, 1, 0], [0, 0, 1, 1], [0, 0, 0, 1]])]))
add('F2^4:Z4(J3+1)', affine(2, 4, [block([[1, 1, 0], [0, 1, 1], [0, 0, 1]], [[1]])]))
add('F2^4:Z3(A+A)', affine(2, 4, [block(A3, A3)]))
# F_2^5 : Z3
add('F2^5:Z3(I3+A)', affine(2, 5, [block([[1, 0, 0], [0, 1, 0], [0, 0, 1]], A3)]))
add('F2^5:Z3(A+A+1)', affine(2, 5, [block(A3, A3, [[1]])]))
# F_3^3 : H
add('F3^3:Z4', affine(3, 3, [block([[0, 2], [1, 0]], [[1]])]))
add('F3^3:Z2xZ2', affine(3, 3, [block([[2]], [[1]], [[1]]), block([[1]], [[2]], [[1]])]))
add('F3^3:Z3(unip)', affine(3, 3, [block([[1, 1, 0], [0, 1, 1], [0, 0, 1]])]))
add('F3^3:Z2xZ2(c)', affine(3, 3, [block([[2]], [[2]], [[1]]), block([[1]], [[2]], [[2]])]))

# ---------- tables and scan ----------
def build_table(name, G):
    gens, N = G
    cl = closure([tuple(g) for g in gens])
    if cl is None:
        return None
    elems, idx = cl
    m = len(elems)
    T = [[idx[pmul(elems[i], elems[j])] for j in range(m)] for i in range(m)]
    return m, T

def write_table(path, m, T):
    with open(path, 'w') as f:
        f.write('%d\n' % m)
        for row in T:
            f.write(' '.join(map(str, row)) + '\n')

def scan(name, G):
    res = build_table(name, G)
    if res is None:
        return None
    m, T = res
    if m < 62 or m > 108:
        return ('skip', m)
    safe = name.replace('/', '_').replace(' ', '').replace('(', '').replace(')', '').replace(',', '_').replace('*', '')
    path = os.path.join(TAB, safe + '.tab')
    write_table(path, m, T)
    out = subprocess.run([CTRL, path, '2'], capture_output=True, text=True, timeout=900).stdout
    best = None; nsol = 0; sols = []
    for line in out.splitlines():
        if line.startswith('SOL'):
            sols.append(line)
        if line.startswith('m='):
            # m=.. tried=.. best_cost=.. solutions=.. bestS=..
            parts = dict(p.split('=') for p in line.split() if '=' in p)
            best = int(parts['best_cost']); nsol = int(parts['solutions'])
    return ('ok', m, best, nsol, sols, path)

if __name__ == '__main__':
    os.makedirs(TAB, exist_ok=True)
    seen = set()
    for name, G in groups:
        try:
            r = scan(name, G)
        except Exception as ex:
            print('%-32s ERROR %s' % (name, ex)); continue
        if r is None:
            print('%-32s closure too big or failed' % name); continue
        if r[0] == 'skip':
            print('%-32s order %d (outside 62..108)' % (name, r[1])); continue
        _, m, best, nsol, sols, path = r
        print('%-32s m=%-4d best_uncovered(sum A+B)=%-4d solutions=%d  %s' % (name, m, best, nsol, ' | '.join(sols[:3])))
        sys.stdout.flush()
