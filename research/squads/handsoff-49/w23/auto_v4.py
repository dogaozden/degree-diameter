#!/usr/bin/env python3
"""P x| (Z_2 x Z_2) for a P given by a .bin table: commuting involutory automorphisms alpha, beta (random extension
of generator images). usage: auto_v4.py PBIN GENS SAMPLES PREFIX MAXOUT"""
import sys, os, time
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/handsoff-49/w15')
from mkg15 import *
from bfs15 import load_bin
from auto15 import extend, elem_orders
H = '/home/user/degree-diameter/research/squads/handsoff-49/w15'

def semidirect_v4(TP, a, b):
    Pn = len(TP)
    ident = np.arange(Pn)
    phis = {(0, 0): ident, (1, 0): a, (0, 1): b, (1, 1): a[b]}
    idx = {(0, 0): 0, (1, 0): 1, (0, 1): 2, (1, 1): 3}
    names = {v: k for k, v in idx.items()}
    N = 4 * Pn
    T = np.empty((N, N), dtype=np.uint16)
    for c in range(4):
        ci = names[c]
        for d in range(4):
            cd = idx[((ci[0] ^ names[d][0]), (ci[1] ^ names[d][1]))]
            blk = TP[:, phis[ci][np.arange(Pn)]] if False else TP[:, phis[ci]]
            T[c * Pn:(c + 1) * Pn, d * Pn:(d + 1) * Pn] = (blk + Pn * cd).astype(np.uint16)
    return T

if __name__ == '__main__':
    TP = np.array(load_bin(sys.argv[1]).astype(np.uint16))
    gens = [int(x) for x in sys.argv[2].split(',')]
    samples = int(sys.argv[3]); prefix = sys.argv[4]; maxout = int(sys.argv[5])
    N = len(TP)
    rng = np.random.default_rng(3)
    ordsP = elem_orders(TP)
    by_order = {}
    for e in range(N):
        by_order.setdefault(int(ordsP[e]), []).append(e)
    invs = []
    for it in range(samples):
        imgs = [int(rng.choice(by_order[int(ordsP[g])])) for g in gens]
        phi = extend(TP, gens, imgs)
        if phi is None:
            continue
        if not (phi[phi] == np.arange(N)).all() or (phi == np.arange(N)).all():
            continue
        invs.append(phi)
    print('involutory automorphisms', len(invs), flush=True)
    seen = {}; found = 0
    for i, a in enumerate(invs):
        for b in invs:
            if not (a[b] == b[a]).all() or (b == a).all():
                continue
            T = semidirect_v4(TP, a, b)
            inv = invariants(T)
            key = (tuple(sorted(inv['hist'].items())), inv['centre'], inv['ab'])
            if key in seen:
                continue
            seen[key] = 1; found += 1
            write_bin(T, f'{H}/tabs/{prefix}_{found}.bin')
            print(f"{prefix}_{found}\tcentre={inv['centre']}\tab={inv['ab']}\tinvol={inv['invol']}\thist={fmt_hist(inv['hist'])}", flush=True)
            if found >= maxout:
                break
        if found >= maxout:
            break
    print('classes', found)
