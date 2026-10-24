#!/usr/bin/env python3
"""Group multiplication tables for ctrl5 (job cell-10-5).

usage: gtab.py SPEC > table.txt     SPEC := FACTOR [x FACTOR]...
FACTOR: cyc n | dih n | meta m k r (Z_m x|_r Z_k, (a,j)(b,l) = (a + r^j b, j + l), r^k = 1 mod m)
        | sl p | psl p | pgl p (p prime) | a4 | s4 | a5 | q8 | elab 2 r (Z_2^r) | heis p (order p^3, p odd prime)
Output: "n" then n rows of n integers, T[x][y] = index of x*y.  Elements are enumerated factor by factor
(mixed radix, first factor most significant)."""
import sys, itertools


def cyc(n):
    return list(range(n)), lambda a, b: (a + b) % n


def meta(m, k, r):
    assert pow(r, k, m) == 1 % m, "r^k != 1 mod m"
    els = [(a, j) for a in range(m) for j in range(k)]
    rp = [pow(r, j, m) for j in range(k)]
    return els, lambda x, y: ((x[0] + rp[x[1]] * y[0]) % m, (x[1] + y[1]) % k)


def mats(p, kind):
    def mm(x, y):
        a, b, c, d = x; e, f, g, h = y
        return ((a * e + b * g) % p, (a * f + b * h) % p, (c * e + d * g) % p, (c * f + d * h) % p)
    allm = [(a, b, c, d) for a in range(p) for b in range(p) for c in range(p) for d in range(p)]
    if kind == 'sl':
        els = [x for x in allm if (x[0] * x[3] - x[1] * x[2]) % p == 1]
        return els, mm
    if kind == 'psl':
        sl = [x for x in allm if (x[0] * x[3] - x[1] * x[2]) % p == 1]
        def norm(x):
            y = tuple((-v) % p for v in x)
            return min(x, y)
        els = sorted(set(norm(x) for x in sl))
        return els, lambda x, y: norm(mm(x, y))
    if kind == 'pgl':
        gl = [x for x in allm if (x[0] * x[3] - x[1] * x[2]) % p != 0]
        def norm(x):
            for v in x:
                if v:
                    iv = pow(v, p - 2, p); return tuple(w * iv % p for w in x)
        els = sorted(set(norm(x) for x in gl))
        return els, lambda x, y: norm(mm(x, y))


def perm_group(gens, deg):
    seen = {tuple(range(deg))}; frontier = [tuple(range(deg))]
    while frontier:
        nxt = []
        for x in frontier:
            for g in gens:
                y = tuple(g[x[i]] for i in range(deg))
                if y not in seen: seen.add(y); nxt.append(y)
        frontier = nxt
    els = sorted(seen)
    return els, lambda x, y: tuple(x[y[i]] for i in range(deg))


def factor(tok):
    name = tok[0]
    if name == 'cyc': return cyc(int(tok[1])), 2
    if name == 'dih':
        n = int(tok[1]); return meta(n, 2, n - 1), 2
    if name == 'meta': return meta(int(tok[1]), int(tok[2]), int(tok[3])), 4
    if name in ('sl', 'psl', 'pgl'): return mats(int(tok[1]), name), 2
    if name == 'a4': return perm_group([(1, 2, 0, 3), (0, 2, 3, 1)], 4), 1
    if name == 's4': return perm_group([(1, 0, 2, 3), (1, 2, 3, 0)], 4), 1
    if name == 'a5': return perm_group([(1, 2, 0, 3, 4), (1, 2, 3, 4, 0)], 5), 1
    if name == 'q8':
        # quaternions as 2x2 complex... use the regular representation by permutations of {±1,±i,±j,±k}
        import cmath
        units = ['1', 'i', 'j', 'k']
        tab = {('1', x): (1, x) for x in units}
        tab.update({(x, '1'): (1, x) for x in units})
        tab.update({('i', 'i'): (-1, '1'), ('j', 'j'): (-1, '1'), ('k', 'k'): (-1, '1'),
                    ('i', 'j'): (1, 'k'), ('j', 'k'): (1, 'i'), ('k', 'i'): (1, 'j'),
                    ('j', 'i'): (-1, 'k'), ('k', 'j'): (-1, 'i'), ('i', 'k'): (-1, 'j')})
        els = [(s, u) for s in (1, -1) for u in units]
        def m(x, y):
            s, u = tab[(x[1], y[1])]; return (x[0] * y[0] * s, u)
        return (els, m), 1
    if name == 'elab':
        assert int(tok[1]) == 2; r = int(tok[2])
        return (list(range(1 << r)), lambda a, b: a ^ b), 3
    if name == 'heis':
        p = int(tok[1]); els = [(a, b, c) for a in range(p) for b in range(p) for c in range(p)]
        return (els, lambda x, y: ((x[0] + y[0]) % p, (x[1] + y[1]) % p, (x[2] + y[2] + x[0] * y[1]) % p)), 2
    raise SystemExit('unknown factor ' + name)


def parse(spec):
    toks = spec.split(); facs = []; i = 0
    cur = []
    for t in toks + ['x']:
        if t == 'x':
            if cur: facs.append(cur); cur = []
        else: cur.append(t)
    return facs


def main():
    spec = ' '.join(sys.argv[1:])
    fs = [factor(f)[0] for f in parse(spec)]
    sizes = [len(e) for e, _ in fs]
    idx = [{x: i for i, x in enumerate(e)} for e, _ in fs]
    n = 1
    for s in sizes: n *= s
    # mixed radix decode
    tuples = list(itertools.product(*[range(s) for s in sizes]))
    pos = {t: i for i, t in enumerate(tuples)}
    out = [str(n)]
    for x in tuples:
        row = []
        for y in tuples:
            z = tuple(idx[f][fs[f][1](fs[f][0][x[f]], fs[f][0][y[f]])] for f in range(len(fs)))
            row.append(str(pos[z]))
        out.append(' '.join(row))
    sys.stdout.write('\n'.join(out) + '\n')


if __name__ == '__main__':
    main()
