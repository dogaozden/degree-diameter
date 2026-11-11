#!/usr/bin/env python3
"""f16 group tables (mktab format: 'G N id name', N rows, index 0 = identity).
Specs: meta:m:k:r | prod:A/B | sl:p (SL(2,p)) | psl:p (PSL(2,p)) | sym:n (S_n).
Usage: mkgrp.py OUT spec [spec ...]   (id = position on the command line, 1-based)
       mkgrp.py --enum c Nlo Nhi  : list metacyclic candidates Z_m x|_r Z_k of order Nlo/c..Nhi/c (dedup by <r>)"""
import sys, random
from math import gcd

def meta_tab(m, k, r):
    assert r % m and pow(r, k, m) == 1 % m
    R = [pow(r, j, m) for j in range(k)]
    N = m * k
    T = [[0] * N for _ in range(N)]
    for x in range(N):
        a, j = divmod(x, k)
        row = T[x]
        for y in range(N):
            b, l = divmod(y, k)
            row[y] = ((a + R[j] * b) % m) * k + (j + l) % k
    return N, T, f"Z{m}x|{r}Z{k}"

def closure(gens, mul, ident, canon=lambda x: x):
    els = [ident]; idx = {ident: 0}; q = 0
    while q < len(els):
        x = els[q]; q += 1
        for g in gens:
            y = canon(mul(x, g))
            if y not in idx: idx[y] = len(els); els.append(y)
    N = len(els)
    T = [[idx[canon(mul(els[i], els[j]))] for j in range(N)] for i in range(N)]
    return N, T

def mat_group(p, psl):
    def mul(A, B):
        a, b, c, d = A; e, f, g, h = B
        return ((a * e + b * g) % p, (a * f + b * h) % p, (c * e + d * g) % p, (c * f + d * h) % p)
    def canon(A):
        if not psl: return A
        B = tuple((-x) % p for x in A)
        return min(A, B)
    gens = [(1, 1, 0, 1), (0, p - 1, 1, 0)]
    N, T = closure([canon(g) for g in gens], mul, (1, 0, 0, 1), canon)
    return N, T, (f"PSL2_{p}" if psl else f"SL2_{p}")

def sym_group(n):
    def mul(x, y): return tuple(x[y[i]] for i in range(n))
    gens = [tuple([1, 0] + list(range(2, n))), tuple(list(range(1, n)) + [0])]
    N, T = closure(gens, mul, tuple(range(n)))
    return N, T, f"S{n}"

def parse(s):
    if s.startswith('meta:'):
        _, m, k, r = s.split(':'); return meta_tab(int(m), int(k), int(r))
    if s.startswith('prod:'):
        A, B = s[5:].split('/', 1)
        N1, T1, n1 = parse(A); N2, T2, n2 = parse(B)
        N = N1 * N2
        T = [[0] * N for _ in range(N)]
        for x in range(N):
            a, b = divmod(x, N2); row = T[x]; T1a = T1[a]; T2b = T2[b]
            for y in range(N):
                c, d = divmod(y, N2)
                row[y] = T1a[c] * N2 + T2b[d]
        return N, T, f"({n1})x({n2})"
    if s.startswith('psl:'): return mat_group(int(s[4:]), True)
    if s.startswith('sl:'): return mat_group(int(s[3:]), False)
    if s.startswith('sym:'): return sym_group(int(s[4:]))
    raise SystemExit("bad spec " + s)

def check(N, T):
    assert all(T[0][x] == x and T[x][0] == x for x in range(N))
    for x in range(N):
        assert len(set(T[x])) == N
    rnd = random.Random(1)
    for _ in range(20000):
        a, b, c = rnd.randrange(N), rnd.randrange(N), rnd.randrange(N)
        assert T[T[a][b]][c] == T[a][T[b][c]], "not associative"

def order_of(r, m):
    x, o = r % m, 1
    while x != 1 % m: x = x * r % m; o += 1
    return o

def enum(c, Nlo, Nhi):
    for M in range(Nlo // c, Nhi // c + 1):
        if M * c < Nlo or M * c > Nhi: continue
        for k in range(2, M + 1):
            if M % k: continue
            m = M // k
            if m < 3: continue
            seen = set()
            for r in range(2, m):
                if gcd(r, m) != 1: continue
                if pow(r, k, m) != 1 % m: continue
                sub = frozenset(pow(r, j, m) for j in range(order_of(r, m)))
                if sub in seen: continue
                seen.add(sub)
                d = order_of(r, m)
                print(f"N={M*c} M={M} m={m} k={k} r={r} ordr={d} faithful={'y' if d==k else 'n'} k/d={k//d} spec=prod:meta:{c}:1:1/meta:{m}:{k}:{r}")

if __name__ == '__main__':
    if sys.argv[1] == '--enum':
        enum(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])); sys.exit(0)
    out = open(sys.argv[1], 'w')
    for gid, spec in enumerate(sys.argv[2:], 1):
        N, T, name = parse(spec)
        check(N, T)
        out.write(f"G {N} {gid} {name}\n")
        for row in T: out.write(" ".join(map(str, row)) + "\n")
        print(f"G {N} {gid} {name}", flush=True)
    out.close()
