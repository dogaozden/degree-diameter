#!/usr/bin/env python3
"""Random automorphisms of a group P given by a table, from images of generators (BFS extension + consistency check).
usage: auto15.py PSPEC GENS_IDX_OR_COORDS SAMPLES OUTPREFIX [MAXOUT]
Writes tabs/OUTPREFIX_k.bin for each automorphism phi of P with phi^4 = id, deduped by invariants of P x| phi Z_4."""
import sys, os, time
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/handsoff-49/w15')
from mkg15 import *
H = '/home/user/degree-diameter/research/squads/handsoff-49/w15'


def elem_orders(T):
    N = len(T)
    X = np.arange(N)
    o = np.zeros(N, dtype=np.int64); o[0] = 1
    pw = np.arange(N); done = np.zeros(N, dtype=bool); done[0] = True
    for k in range(1, 2 * N):
        pw = T[pw, X]
        newly = (pw == 0) & (~done)
        o[newly] = k + 1; done |= newly
        if done.all(): break
    return o


def extend(T, gens, imgs):
    """phi with phi(g_i) = h_i, or None. BFS over the Cayley graph with right multiplication by gens."""
    N = len(T)
    phi = np.full(N, -1, dtype=np.int64)
    phi[0] = 0
    queue = [0]
    qi = 0
    while qi < len(queue):
        x = queue[qi]; qi += 1
        for g, h in zip(gens, imgs):
            y = int(T[x, g])
            val = int(T[phi[x], h])
            if phi[y] < 0:
                phi[y] = val
                queue.append(y)
            elif phi[y] != val:
                return None
    if (phi < 0).any() or len(set(phi.tolist())) != N:
        return None
    return phi


def check_hom(T, phi):
    return (phi[T] == T[phi][:, phi]).all()


if __name__ == '__main__':
    import groups as GRP
    spec = sys.argv[1]
    gens = [int(x) for x in sys.argv[2].split(',')]
    samples = int(sys.argv[3])
    prefix = sys.argv[4]
    maxout = int(sys.argv[5]) if len(sys.argv) > 5 else 40
    TP = GRP.table(spec)
    N = len(TP)
    ordsP = elem_orders(TP)
    print('P', spec, 'N', N, 'gen orders', [int(ordsP[g]) for g in gens], flush=True)
    rng = np.random.default_rng(int(os.environ.get('SEED', '1')))
    by_order = {}
    for e in range(N):
        by_order.setdefault(int(ordsP[e]), []).append(e)
    seen = {}
    found = 0
    t0 = time.time()
    n_ext = 0
    n_ord4 = 0
    for it in range(samples):
        imgs = [int(rng.choice(by_order[int(ordsP[g])])) for g in gens]
        phi = extend(TP, gens, imgs)
        if phi is None:
            continue
        n_ext += 1
        pw = np.arange(N)
        for _ in range(4):
            pw = phi[pw]
        if not (pw == np.arange(N)).all():
            continue
        n_ord4 += 1
        T = semidirect(TP, phi)
        inv = invariants(T)
        key = (tuple(sorted(inv['hist'].items())), inv['centre'], inv['ab'], tuple(sorted(np.bincount(np.array([0]), minlength=1).tolist())))
        # stronger key: element-order histogram of G restricted to each coset of P
        key = (tuple(sorted(inv['hist'].items())), inv['centre'], inv['ab'])
        if key in seen:
            continue
        seen[key] = imgs
        found += 1
        name = f'{prefix}_{found}'
        write_bin(T, f'{H}/tabs/{name}.bin')
        print(f"{name}\timgs={imgs}\tcentre={inv['centre']}\tab={inv['ab']}\tinvol={inv['invol']}\thist={fmt_hist(inv['hist'])}", flush=True)
        if found >= maxout:
            break
    print('extended', n_ext, 'order4', n_ord4, 'classes', found, 'time', round(time.time() - t0, 1))
