#!/usr/bin/env python3
"""Subgroups of order 625 of Z_5 wr Z_5 (Sylow 5-subgroup of S_25), random 2- and 3-generated, classified by invariants.
usage: wr5.py SAMPLES"""
import sys, os
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/handsoff-49/w15')
from mkg15 import *
H = '/home/user/degree-diameter/research/squads/handsoff-49/w15'
rng = np.random.default_rng(int(os.environ.get('SEED', '7')))
n = 25
def base_top(x, y):
    p = np.arange(n)
    for blk in range(5):
        for i in range(5):
            p[5 * blk + i] = 5 * blk + (i + x[blk]) % 5
    # top: block b -> block (b + y) mod 5, element-wise
    q = np.arange(n)
    for blk in range(5):
        for i in range(5):
            q[5 * blk + i] = 5 * ((blk + y) % 5) + i
    return q[p] if False else p[q]
def closure(gens, cap=625):
    I = tuple(range(n))
    els = [I]; seen = {I: 0}; i = 0
    while i < len(els):
        x = els[i]; i += 1
        for g in gens:
            y = tuple(x[g[k]] for k in range(n))
            if y not in seen:
                if len(els) >= cap:
                    return None
                seen[y] = len(els); els.append(y)
    return els, seen
def table_of(els, seen):
    N = len(els)
    T = np.empty((N, N), dtype=np.uint16)
    A = np.array(els)
    for a in range(N):
        comp = A[a][A]          # row b: a o b  -> (a o b)(k) = a(b(k))
        T[a] = [seen[tuple(r)] for r in comp.tolist()]
    return T
if __name__ == '__main__':
    samples = int(sys.argv[1])
    classes = {}; hits = 0; orders = {}
    out = open(f'{H}/wr5_classes.tsv', 'a')
    for it in range(samples):
        k = int(os.environ.get("K", "2"))
        gens = []
        for _ in range(k):
            x = rng.integers(0, 5, size=5); y = int(rng.integers(0, 5))
            gens.append(base_top(x, y))
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
        name = f'wr5_{len(classes)}'
        write_bin(T, f'{H}/tabs/{name}.bin')
        line = f"{name}\tcentre={inv['centre']}\tab={inv['ab']}\tinvol={inv['invol']}\thist={fmt_hist(inv['hist'])}"
        print(line, flush=True); out.write(line + '\n'); out.flush()
    print('orders seen (capped at 625 means abort)', sorted(orders.items())[:10], 'hits', hits, 'classes', len(classes))
