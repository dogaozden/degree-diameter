#!/usr/bin/env python3
"""gen_groups.py: multiplication tables of nonabelian groups of order 12..64 for lift3 (GROUP="file <path>").

File format (lift3 make_group): line 1 = m, then m rows of m ints; row x, column y = index of x*y.
Element 0 is the identity.  groups/index.tsv lists name, order, and nonidentity central elements
(usable as MCONST voltages via T="z1 z2").
"""
import os
from collections import deque

HERE = os.path.dirname(os.path.abspath(__file__))
OUTDIR = os.path.join(HERE, 'groups')


def bfs_elems(gens, mul, e):
    elems, idx, dq = [e], {e: 0}, deque([e])
    while dq:
        x = dq.popleft()
        for g in gens:
            y = mul(g, x)
            if y not in idx:
                idx[y] = len(elems)
                elems.append(y)
                dq.append(y)
    return elems, idx


def table(gens, mul, e):
    elems, idx = bfs_elems(gens, mul, e)
    return [[idx[mul(x, y)] for y in elems] for x in elems]


def perm_mul(p, q):
    return tuple(p[i] for i in q)


def perm_group(gens):
    return table(gens, perm_mul, tuple(range(len(gens[0]))))


def dihedral(n):
    r = tuple((i + 1) % n for i in range(n))
    s = tuple((-i) % n for i in range(n))
    return perm_group([r, s])


def meta(m, k, s):
    """Z_m x| Z_k, (a1,b1)(a2,b2) = (a1 + s^b1 a2, b1 + b2); needs s^k = 1 mod m."""
    assert pow(s, k, m) == 1 % m, (m, k, s)
    def mul(x, y):
        return ((x[0] + pow(s, x[1], m) * y[0]) % m, (x[1] + y[1]) % k)
    return table([(1, 0), (0, 1)], mul, (0, 0))


def dicyclic(n):
    """Dic_n = <x,y | x^{2n}=1, y^2=x^n, y x y^-1 = x^-1>, order 4n (Q_{4n} when n is a power of 2)."""
    N2 = 2 * n
    def mul(u, v):
        a, b = u
        c, d = v
        e = a + (c if b == 0 else -c) + (n if b + d == 2 else 0)
        return (e % N2, (b + d) % 2)
    return table([(1, 0), (0, 1)], mul, (0, 0))


def direct(A, B):
    ma, mb = len(A), len(B)
    T = [[0] * (ma * mb) for _ in range(ma * mb)]
    for a in range(ma):
        for b in range(mb):
            x = a * mb + b
            for c in range(ma):
                for d in range(mb):
                    T[x][c * mb + d] = A[a][c] * mb + B[b][d]
    return T


def matmul(A, B, p):
    n = len(A)
    return [[sum(A[i][t] * B[t][j] for t in range(n)) % p for j in range(n)] for i in range(n)]


def mv(M, v, p):
    return tuple(sum(M[i][j] * v[j] for j in range(len(v))) % p for i in range(len(M)))


def vc(p, dim, A, k):
    """F_p^dim x| Z_k, Z_k acting by the matrix A (A^k = I)."""
    I = [[int(i == j) for j in range(dim)] for i in range(dim)]
    powers, P = [], I
    for _ in range(k):
        powers.append(P)
        P = matmul(P, A, p)
    assert P == I, "A^k != I"
    zero = tuple([0] * dim)
    def mul(x, y):
        return (tuple((a + b) % p for a, b in zip(x[0], mv(powers[x[1]], y[0], p))), (x[1] + y[1]) % k)
    gens = [(tuple(int(i == j) for j in range(dim)), 0) for i in range(dim)] + [(zero, 1)]
    return table(gens, mul, (zero, 0))


def matgroup(gens, p):
    n = len(gens[0])
    def mul(X, Y):
        return tuple(tuple(sum(X[i][t] * Y[t][j] for t in range(n)) % p for j in range(n)) for i in range(n))
    I = tuple(tuple(int(i == j) for j in range(n)) for i in range(n))
    return table(gens, mul, I)


def analyse(T):
    m = len(T)
    for x in range(m):
        for y in range(m):
            for z in range(m):
                assert T[T[x][y]][z] == T[x][T[y][z]], "not associative"
    commutative = all(T[x][y] == T[y][x] for x in range(m) for y in range(m))
    center = [z for z in range(1, m) if all(T[z][g] == T[g][z] for g in range(m))]
    return m, commutative, center


def groups():
    A = [[0, 1], [1, 1]]
    g = {}
    # order 12..64, a curated spread of families
    g['dih6'] = dihedral(6)
    g['Dic3'] = dicyclic(3)
    g['A4'] = perm_group([(1, 2, 0, 3), (1, 0, 3, 2)])
    g['dih7'] = dihedral(7)
    g['dih8'] = dihedral(8)
    g['Dic4_Q16'] = dicyclic(4)
    g['SD16'] = meta(8, 2, 3)
    g['M16'] = meta(8, 2, 5)
    g['Z4xZ4s'] = meta(4, 4, 3)
    g['D4xZ2'] = direct(dihedral(4), [[0, 1], [1, 0]])
    g['Q8xZ2'] = direct(dicyclic(2), [[0, 1], [1, 0]])
    g['dih9'] = dihedral(9)
    g['S3xZ3'] = direct(dihedral(3), [[(i + j) % 3 for j in range(3)] for i in range(3)])
    g['gendih_Z3^2'] = vc(3, 2, [[2, 0], [0, 2]], 2)
    g['dih10'] = dihedral(10)
    g['Dic5'] = dicyclic(5)
    g['F20'] = meta(5, 4, 2)
    g['D5xZ2'] = direct(dihedral(5), [[0, 1], [1, 0]])
    g['Z7x|Z3'] = meta(7, 3, 2)
    g['dih11'] = dihedral(11)
    g['dih12'] = dihedral(12)
    g['S3xZ4'] = direct(dihedral(3), [[(i + j) % 4 for j in range(4)] for i in range(4)])
    g['D6xZ2'] = direct(dihedral(6), [[0, 1], [1, 0]])
    g['A4xZ2'] = direct(g['A4'], [[0, 1], [1, 0]])
    g['SL23'] = matgroup([((1, 1), (0, 1)), ((0, 2), (1, 0))], 3)
    g['Dic6'] = dicyclic(6)
    g['Z3x|Z8_s2'] = meta(3, 8, 2)
    g['S4'] = perm_group([(1, 2, 3, 0), (1, 0, 2, 3)])
    g['D4xZ3'] = direct(dihedral(4), [[(i + j) % 3 for j in range(3)] for i in range(3)])
    g['Q8xZ3'] = direct(dicyclic(2), [[(i + j) % 3 for j in range(3)] for i in range(3)])
    g['dih13'] = dihedral(13)
    g['Heis27'] = vc(3, 2, [[1, 1], [0, 1]], 3)
    g['Z9x|Z3_s4'] = meta(9, 3, 4)
    g['dih14'] = dihedral(14)
    g['Dic7'] = dicyclic(7)
    g['dih15'] = dihedral(15)
    g['S3xZ5'] = direct(dihedral(3), [[(i + j) % 5 for j in range(5)] for i in range(5)])
    g['D5xZ3'] = direct(dihedral(5), [[(i + j) % 3 for j in range(3)] for i in range(3)])
    g['dih16'] = dihedral(16)
    g['Dic8_Q32'] = dicyclic(8)
    g['M32'] = meta(16, 2, 9)
    g['SD32'] = meta(16, 2, 7)
    g['D8xZ2'] = direct(dihedral(8), [[0, 1], [1, 0]])
    g['Q16xZ2'] = direct(dicyclic(4), [[0, 1], [1, 0]])
    g['dih18'] = dihedral(18)
    g['S3xS3'] = direct(dihedral(3), dihedral(3))
    g['S3xZ6'] = direct(dihedral(3), [[(i + j) % 6 for j in range(6)] for i in range(6)])
    g['A4xZ3'] = direct(g['A4'], [[(i + j) % 3 for j in range(3)] for i in range(3)])
    g['F2^2x|Z9'] = vc(2, 2, A, 9)
    g['F3^2x|Z4'] = vc(3, 2, [[0, 2], [1, 0]], 4)
    g['Z9x|Z4_s8'] = meta(9, 4, 8)
    g['Z13x|Z3'] = meta(13, 3, 3)
    g['dih20'] = dihedral(20)
    g['Dic10'] = dicyclic(10)
    g['Z5x|Z8_s2'] = meta(5, 8, 2)
    g['D5xZ4'] = direct(dihedral(5), [[(i + j) % 4 for j in range(4)] for i in range(4)])
    g['dih21'] = dihedral(21)
    g['F42'] = meta(7, 6, 3)
    g['D7xZ3'] = direct(dihedral(7), [[(i + j) % 3 for j in range(3)] for i in range(3)])
    g['S3xZ7'] = direct(dihedral(3), [[(i + j) % 7 for j in range(7)] for i in range(7)])
    g['dih24'] = dihedral(24)
    g['Dic12'] = dicyclic(12)
    g['GL23'] = matgroup([((1, 1), (0, 1)), ((0, 2), (1, 0)), ((1, 0), (0, 2))], 3)
    g['A4xZ4'] = direct(g['A4'], [[(i + j) % 4 for j in range(4)] for i in range(4)])
    g['S4xZ2'] = direct(g['S4'], [[0, 1], [1, 0]])
    g['SL23xZ2'] = direct(g['SL23'], [[0, 1], [1, 0]])
    g['F2^4x|Z3'] = vc(2, 4, [[0, 1, 0, 0], [1, 1, 0, 0], [0, 0, 0, 1], [0, 0, 1, 1]], 3)
    g['dih27'] = dihedral(27)
    g['S3xZ9'] = direct(dihedral(3), [[(i + j) % 9 for j in range(9)] for i in range(9)])
    g['F2^3x|Z7'] = vc(2, 3, [[0, 0, 1], [1, 0, 1], [0, 1, 0]], 7)
    g['dih28'] = dihedral(28)
    g['Dic14'] = dicyclic(14)
    g['dih30'] = dihedral(30)
    g['A5'] = perm_group([(1, 2, 3, 4, 0), (1, 2, 0, 3, 4)])
    g['A4xZ5'] = direct(g['A4'], [[(i + j) % 5 for j in range(5)] for i in range(5)])
    g['S3xZ10'] = direct(dihedral(3), [[(i + j) % 10 for j in range(10)] for i in range(10)])
    g['dih32'] = dihedral(32)
    g['Dic16_Q64'] = dicyclic(16)
    g['M64'] = meta(32, 2, 17)
    return g


A = [[0, 1], [1, 1]]  # used by F2^2 x| Z9 (order-3 matrix over F_2)

EXPECT = {}  # name -> expected order (filled by main from the name's trailing number when present)


def main():
    os.makedirs(OUTDIR, exist_ok=True)
    rows = []
    for name, T in groups().items():
        m, comm, center = analyse(T)
        if comm:
            print('SKIP abelian', name)
            continue
        if m < 12 or m > 64:
            print('SKIP order', name, m)
            continue
        with open(os.path.join(OUTDIR, name + '.txt'), 'w') as f:
            f.write('%d\n' % m)
            for row in T:
                f.write(' '.join(map(str, row)) + '\n')
        rows.append((m, name, center[:6]))
    rows.sort()
    with open(os.path.join(OUTDIR, 'index.tsv'), 'w') as f:
        f.write('order\tname\tcenter_indices\n')
        for m, name, center in rows:
            f.write('%d\t%s\t%s\n' % (m, name, ','.join(map(str, center))))
    for m, name, center in rows:
        print(m, name, 'center', center)


if __name__ == '__main__':
    main()
