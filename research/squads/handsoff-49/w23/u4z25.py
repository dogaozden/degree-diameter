#!/usr/bin/env python3
"""Subgroups of order 625 of U_4(Z/25) (4x4 unitriangular over Z/25, order 25^6), random 2-generated, classified by
invariants; tables tabs/u4z_K.bin. usage: u4z25.py SAMPLES  (SEED env)"""
import sys, os
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/handsoff-49/w15')
from mkg15 import *
H = '/home/user/degree-diameter/research/squads/handsoff-49/w15'
rng = np.random.default_rng(int(os.environ.get('SEED', '23')))
M = 25
POS = [(0, 1), (1, 2), (2, 3), (0, 2), (1, 3), (0, 3)]
def rand_elem():
    A = np.eye(4, dtype=np.int64)
    for (i, j) in POS:
        if rng.random() < 0.45:
            A[i, j] = rng.integers(0, M) if rng.random() < 0.5 else 5 * rng.integers(0, 5)
    return A
def closure(gens, cap=625):
    I = np.eye(4, dtype=np.int64)
    els = [I]; seen = {I.tobytes(): 0}; i = 0
    while i < len(els):
        x = els[i]; i += 1
        for g in gens:
            y = (x @ g) % M
            k = y.tobytes()
            if k not in seen:
                if len(els) >= cap:
                    return None
                seen[k] = len(els); els.append(y)
    return els, seen
def table_of(els, seen):
    N = len(els)
    A = np.array(els)
    T = np.empty((N, N), dtype=np.uint16)
    for a in range(N):
        prod = np.einsum('ij,njk->nik', A[a], A) % M
        T[a] = [seen[p.tobytes()] for p in prod]
    return T
if __name__ == '__main__':
    samples = int(sys.argv[1])
    classes = {}; hits = 0; orders = {}
    out = open(f'{H}/u4z25_classes.tsv', 'a')
    for it in range(samples):
        gens = [rand_elem() for _ in range(2)]
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
        name = f'u4z_{len(classes)}'
        write_bin(T, f'{H}/tabs/{name}.bin')
        line = f"{name}\tcentre={inv['centre']}\tab={inv['ab']}\tinvol={inv['invol']}\thist={fmt_hist(inv['hist'])}"
        print(line, flush=True); out.write(line + '\n'); out.flush()
    print('orders seen', sorted(orders.items())[:8], 'hits', hits, 'classes', len(classes))
