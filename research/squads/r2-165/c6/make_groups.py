#!/usr/bin/env python3
"""Card C6 (squad165 round 2): all metacyclic groups of order m, as multiplication tables, deduplicated.

Every metacyclic group of order m = a*b has a presentation (Holder)
    G(a,b,r,t) = <x,y | x^a = 1, y^b = x^t, y^-1 x y = x^r>,   r a unit mod a, r^b = 1 mod a, t(r-1) = 0 mod a,
with elements x^i y^j (0 <= i < a, 0 <= j < b).  Using y x y^-1 = x^s (s = r^-1 mod a):
    (x^i y^j)(x^k y^l) = x^(i + k s^j + [j+l>=b] t s^p) y^p,  p = (j+l) mod b.
t = 0 gives the split groups Z_a x| Z_b (meta_scan.py); t != 0 gives the non-split ones (e.g. Q8).
Isomorphism classes are merged by an invariant (m; element orders with centraliser sizes; |Z(G)|; |G'|).  Two
non-isomorphic groups with equal invariants would be merged (reported as the number of merged presentations).

usage: python3 make_groups.py selftest | make LO HI TABLEDIR MANIFEST
"""
import sys, os
from math import gcd
from collections import Counter
import numpy as np

def build(a, b, r, t):
    m = a * b
    s = pow(r, -1, a) if a > 1 else 0
    sp = [pow(s, p, a) if a > 1 else 0 for p in range(b + 1)]
    T = np.empty((m, m), dtype=np.int64)
    for j in range(b):
        for i in range(a):
            P = j * a + i
            for l in range(b):
                for k in range(a):
                    Q = l * a + k
                    c = (i + k * sp[j]) % a if a > 1 else 0
                    p = j + l
                    if p >= b:
                        p -= b
                        c = (c + t * sp[p]) % a if a > 1 else 0
                    T[P, Q] = p * a + c
    return T

def is_group(T):
    m = T.shape[0]
    e = [i for i in range(m) if np.array_equal(T[i], np.arange(m))]
    if len(e) != 1: return False
    e = e[0]
    if not np.all(T[:, e] == np.arange(m)): return False
    # associativity: (xy)z == x(yz)
    # T[x,y] -> w ; T[w,z]
    left = T[T[:, :, None], np.arange(m)[None, None, :]]        # ((x y) z)
    right = T[np.arange(m)[:, None, None], T[None, :, :]]      # (x (y z))
    return bool(np.array_equal(left, right))

def invariant(T):
    m = T.shape[0]
    ar = np.arange(m)
    e = int(np.where((T == ar[None, :]).all(axis=1))[0][0])
    inv = [int(np.where(T[i] == e)[0][0]) for i in range(m)]
    order = []
    for x in range(m):
        y, k = x, 1
        while y != e:
            y = int(T[y, x]); k += 1
        order.append(k)
    C = [int(np.sum(T[x] == T[:, x])) for x in range(m)]
    Z = sum(1 for x in range(m) if C[x] == m)
    comms = set(int(T[T[inv[x], inv[y]], T[x, y]]) for x in range(m) for y in range(m))
    H = {e}; frontier = [e]; gens = list(comms)
    while frontier:
        nf = []
        for h in frontier:
            for g in gens + list(H):
                for w in (int(T[h, g]), int(T[g, h])):
                    if w not in H:
                        H.add(w); nf.append(w)
        frontier = nf
    sig = tuple(sorted(Counter(zip(order, C)).items()))
    return (m, sig, Z, len(H))

def presentations(m):
    out = []
    for a in range(1, m + 1):
        if m % a: continue
        b = m // a
        if a == 1:
            out.append((1, b, 0, 0)); continue
        for r in range(1, a):
            if gcd(r, a) != 1 or pow(r, b, a) != 1 % a: continue
            for t in range(a):
                if (t * (r - 1)) % a != 0: continue
                out.append((a, b, r, t))
    return out

def classes(m, check=True):
    seen = {}
    for (a, b, r, t) in presentations(m):
        T = build(a, b, r, t)
        if check and not is_group(T):
            raise RuntimeError(f'not a group: G({a},{b},{r},{t})')
        key = invariant(T)
        if key in seen:
            seen[key]['merged'] += 1
        else:
            seen[key] = dict(m=m, a=a, b=b, r=r, t=t, T=T, merged=0)
    return list(seen.values())

if __name__ == '__main__':
    if sys.argv[1] == 'selftest':
        for m in (8, 12, 16):
            cl = classes(m)
            print('order', m, 'metacyclic classes', len(cl), [(c['a'], c['b'], c['r'], c['t']) for c in cl])
        sys.exit(0)
    lo, hi, tdir, manifest = int(sys.argv[2]), int(sys.argv[3]), sys.argv[4], sys.argv[5]
    os.makedirs(tdir, exist_ok=True)
    rows = []
    for m in range(lo, hi + 1):
        for c in classes(m):
            name = f"m{m}_a{c['a']}_b{c['b']}_r{c['r']}_t{c['t']}"
            path = os.path.join(tdir, name + '.txt')
            with open(path, 'w') as f:
                f.write(f"{m}\n" + ' '.join(map(str, c['T'].flatten().tolist())) + '\n')
            rows.append((m, c['a'], c['b'], c['r'], c['t'], int(c['t'] == 0 or c['a'] == 1), c['merged'], path))
        print('order', m, 'classes', sum(1 for r in rows if r[0] == m), flush=True)
    with open(manifest, 'w') as f:
        f.write('m\ta\tb\tr\tt\tsplit\tmerged_presentations\ttable\n')
        for row in rows:
            f.write('\t'.join(map(str, row)) + '\n')
    print('total classes', len(rows), 'manifest', manifest)
