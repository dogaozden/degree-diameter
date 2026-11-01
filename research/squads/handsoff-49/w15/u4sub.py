#!/usr/bin/env python3
"""Random subgroups of order 625 of the unitriangular group U_4(F_5) (order 5^6): all 5-groups of order 625 that
embed there. Groups are classified by invariants; the first table of each class is written to tabs/u4_KEY.bin and the
generators (as 4x4 matrices) to u4_classes.tsv. usage: u4sub.py SAMPLES"""
import sys, itertools, os
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/handsoff-49/w15')
from mkg15 import *
H = '/home/user/degree-diameter/research/squads/handsoff-49/w15'
rng = np.random.default_rng(int(os.environ.get('SEED', '5')))
p = 5
POS = [(0, 1), (1, 2), (2, 3), (0, 2), (1, 3), (0, 3)]


def rand_elem():
    M = np.eye(4, dtype=np.int64)
    for (i, j) in POS:
        M[i, j] = rng.integers(0, p)
    return M


def key_of(M):
    return M.tobytes()


def closure(gens, cap=625):
    I = np.eye(4, dtype=np.int64)
    els = [I]
    seen = {I.tobytes(): 0}
    i = 0
    while i < len(els):
        x = els[i]; i += 1
        for g in gens:
            y = (x @ g) % p
            k = y.tobytes()
            if k not in seen:
                if len(els) >= cap:
                    return None
                seen[k] = len(els)
                els.append(y)
    return els, seen


def table_from(els, seen):
    N = len(els)
    T = np.empty((N, N), dtype=np.int64)
    A = np.array(els)  # N x 4 x 4
    for a in range(N):
        prod = (np.einsum('ij,njk->nik', A[a], A) % p)
        T[a] = [seen[x.tobytes()] for x in prod]
    return T.astype(np.uint16)


if __name__ == '__main__':
    samples = int(sys.argv[1])
    classes = {}
    out = open(f'{H}/u4_classes.tsv', 'a')
    hits = 0
    for it in range(samples):
        k = int(rng.integers(2, 4))
        gens = [rand_elem() for _ in range(k)]
        r = closure(gens)
        if r is None:
            continue
        els, seen = r
        hits += 1
        T = table_from(els, seen)
        inv = invariants(T.astype(np.int64))
        key = (inv['centre'], inv['ab'], tuple(sorted(inv['hist'].items())))
        if key in classes:
            continue
        classes[key] = gens
        name = f'u4_{len(classes)}'
        write_bin(T, f'{H}/tabs/{name}.bin')
        line = f"{name}\tcentre={inv['centre']}\tab={inv['ab']}\tinvol={inv['invol']}\thist={fmt_hist(inv['hist'])}"
        print(line, flush=True)
        out.write(line + '\n'); out.flush()
    print('subgroups of order 625 found', hits, 'classes', len(classes))
