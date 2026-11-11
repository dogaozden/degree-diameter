#!/usr/bin/env python3
"""Subgroups of order 625 of U_3(Z/25) (3x3 unitriangular over Z/25, order 15625), random 2- and 3-generated.
element (a,b,c) = [[1,a,c],[0,1,b],[0,0,1]], product (a,b,c)(a',b',c') = (a+a', b+b', c+c'+a*b'). usage: u3z25.py SAMPLES"""
import sys, os
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/handsoff-49/w15')
from mkg15 import *
H = '/home/user/degree-diameter/research/squads/handsoff-49/w15'
rng = np.random.default_rng(int(os.environ.get('SEED', '17')))
M = 25
K = int(os.environ.get('K', '2'))
def mul(x, y):
    return ((x[0] + y[0]) % M, (x[1] + y[1]) % M, (x[2] + y[2] + x[0] * y[1]) % M)
def closure(gens, cap=625):
    I = (0, 0, 0)
    els = [I]; seen = {I: 0}; i = 0
    while i < len(els):
        x = els[i]; i += 1
        for g in gens:
            y = mul(x, g)
            if y not in seen:
                if len(els) >= cap:
                    return None
                seen[y] = len(els); els.append(y)
    return els, seen
def table_of(els, seen):
    N = len(els)
    T = np.empty((N, N), dtype=np.uint16)
    for i, x in enumerate(els):
        T[i] = [seen[mul(x, y)] for y in els]
    return T
if __name__ == '__main__':
    samples = int(sys.argv[1])
    classes = {}; hits = 0; orders = {}
    out = open(f'{H}/u3z25_classes.tsv', 'a')
    for it in range(samples):
        gens = [tuple(int(v) for v in rng.integers(0, M, size=3)) for _ in range(K)]
        r = closure(gens)
        if r is None:
            continue
        els, seen = r
        orders[len(els)] = orders.get(len(els), 0) + 1
        if len(els) != 625:
            continue
        hits += 1
        T = table_of(els, seen).astype(np.int64)
        inv = invariants(T)
        key = (inv['centre'], inv['ab'], tuple(sorted(inv['hist'].items())))
        if key in classes:
            continue
        classes[key] = 1
        name = f'u3z_{len(classes)}'
        write_bin(T, f'{H}/tabs/{name}.bin')
        line = f"{name}\tcentre={inv['centre']}\tab={inv['ab']}\tinvol={inv['invol']}\thist={fmt_hist(inv['hist'])}"
        print(line, flush=True); out.write(line + '\n'); out.flush()
    print('orders seen', sorted(orders.items())[:8], 'hits', hits, 'classes', len(classes))
