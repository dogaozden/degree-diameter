#!/usr/bin/env python3
"""Group tables for the C5 controller search, written in the dump_table.py format
(first line n, then n*n ints row-major: entry [i*n+j] = index of i*j).
Groups built here: Q8 x Z2 and SL(2,3); the others come from research/theorems/squad165/dump_table.py.
usage: python3 mk_tables.py OUTDIR"""
import sys, os, itertools

def write(T, path):
    n = len(T)
    with open(path, 'w') as f:
        f.write(f"{n}\n")
        f.write(' '.join(str(T[i][j]) for i in range(n) for j in range(n)) + '\n')

def closure_table(gens, mul, ident):
    els = [ident]; idx = {ident: 0}; k = 0
    while k < len(els):
        g = els[k]
        for s in gens:
            h = mul(g, s)
            if h not in idx:
                idx[h] = len(els); els.append(h)
        k += 1
    T = [[idx[mul(a, b)] for b in els] for a in els]
    return T

def q8():
    # elements (sign, unit) with unit in {1,i,j,k} = {0,1,2,3}
    sgn_tab = {(0,0):1,(0,1):1,(0,2):1,(0,3):1,(1,0):1,(1,1):-1,(1,2):1,(1,3):-1,
               (2,0):1,(2,1):-1,(2,2):-1,(2,3):1,(3,0):1,(3,1):1,(3,2):-1,(3,3):-1}
    # note: i*k = -j, j*i = -k, k*j = -i (see table below)
    prod_tab = {(0,0):0,(0,1):1,(0,2):2,(0,3):3,(1,0):1,(1,1):0,(1,2):3,(1,3):2,
                (2,0):2,(2,1):3,(2,2):0,(2,3):1,(3,0):3,(3,1):2,(3,2):1,(3,3):0}
    sign = {(0,0):1,(0,1):1,(0,2):1,(0,3):1,(1,0):1,(1,1):-1,(1,2):1,(1,3):-1,
            (2,0):1,(2,1):-1,(2,2):-1,(2,3):1,(3,0):1,(3,1):-1,(3,2):-1,(3,3):-1}
    # i*i=-1, i*j=k, i*k=-j, j*i=-k, j*j=-1, j*k=i, k*i=j, k*j=-i, k*k=-1
    sign[(1,2)] = 1; sign[(1,3)] = -1; sign[(2,1)] = -1; sign[(2,3)] = 1; sign[(3,1)] = 1; sign[(3,2)] = -1
    def mul(x, y):
        (s1, a), (s2, b) = x, y
        return ((s1 * s2 * sign[(a, b)]) % 2 if False else (s1 + s2 + (0 if sign[(a,b)] == 1 else 1)) % 2, prod_tab[(a, b)])
    els = [(s, u) for s in (0, 1) for u in range(4)]
    ident = (0, 0)
    gens = [(0, 1), (0, 2)]
    # sanity: i^2 = j^2 = -1 and (ij) = k
    assert mul((0,1),(0,1)) == (1,0) and mul((0,2),(0,2)) == (1,0) and mul((0,1),(0,2)) == (0,3)
    return closure_table(gens, mul, ident)

def z2_table():
    return [[(a + b) % 2 for b in range(2)] for a in range(2)]

def product(T1, T2):
    n1, n2 = len(T1), len(T2)
    n = n1 * n2
    T = [[0] * n for _ in range(n)]
    for i in range(n):
        a1, a2 = divmod(i, n2)
        for j in range(n):
            b1, b2 = divmod(j, n2)
            T[i][j] = T1[a1][b1] * n2 + T2[a2][b2]
    return T

def sl23():
    p = 3
    def mm(A, B):
        return tuple(tuple(sum(A[i][k] * B[k][j] for k in range(2)) % p for j in range(2)) for i in range(2))
    gens = [((1, 1), (0, 1)), ((0, 2), (1, 0))]
    ident = ((1, 0), (0, 1))
    return closure_table(gens, mm, ident)

if __name__ == '__main__':
    out = sys.argv[1]
    os.makedirs(out, exist_ok=True)
    Q = q8()
    write(Q, os.path.join(out, 'q8.txt'))
    write(product(Q, z2_table()), os.path.join(out, 'q8xz2.txt'))
    S = sl23()
    write(S, os.path.join(out, 'sl23.txt'))
    print('q8 n=', len(Q), 'sl23 n=', len(S), 'q8xz2 n=', len(Q) * 2)
