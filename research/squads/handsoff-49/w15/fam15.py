#!/usr/bin/env python3
"""Build the w15 family list: P x| Z_4 with |P| = 625 (order 2500), tables in tabs/, manifest in fam_manifest_KIND.tsv.
usage: fam15.py KIND [samples]   KIND = abel (random fixed-point-free automorphisms of abelian P), heis, named"""
import sys, os
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/handsoff-49/w15')
from mkg15 import *

H = '/home/user/degree-diameter/research/squads/handsoff-49/w15'
rng = np.random.default_rng(int(os.environ.get('SEED', '1')))


def fpf_ok(perm, Pn):
    """no nontrivial fixed points of phi, phi^2, phi^3."""
    cur = np.arange(Pn)
    for k in range(1, 4):
        cur = perm[cur]
        if (cur == np.arange(Pn)).sum() != 1:
            return False
    return True


def gen_count(T, trials=40):
    """fraction of random 2- and 3-tuples that generate G (returns [f2, f3])."""
    N = len(T)
    res = []
    for k in (2, 3):
        ok = 0
        for _ in range(trials):
            S = rng.integers(1, N, size=k)
            Hs = {0}
            fr = [0]
            while fr:
                nw = []
                for h in fr:
                    for s in S:
                        x = int(T[h, s])
                        if x not in Hs:
                            Hs.add(x); nw.append(x)
                fr = nw
            if len(Hs) == N:
                ok += 1
        res.append(ok / trials)
    return res


def write_one(name, T, desc, out):
    inv = invariants(T)
    gc = gen_count(T)
    write_bin(T, f'{H}/tabs/{name}.bin')
    line = (f"{name}\t{desc}\tN={inv['N']}\tcentre={inv['centre']}\tab={inv['ab']}\tinvol={inv['invol']}"
            f"\tmaxord={inv['maxord']}\tgen2={gc[0]:.2f}\tgen3={gc[1]:.2f}\thist={fmt_hist(inv['hist'])}")
    print(line, flush=True)
    out.write(line + '\n'); out.flush()


if __name__ == '__main__':
    kind = sys.argv[1]
    nsamp = int(sys.argv[2]) if len(sys.argv) > 2 else 400
    out = open(f'{H}/fam_manifest_{kind}.tsv', 'a')
    if kind == 'named':
        cases = {
            'z5_4_22': ([5, 5, 5, 5], [[0, -1, 0, 0], [1, 0, 0, 0], [0, 0, 0, -1], [0, 0, 1, 0]]),
            'z5_4_31': ([5, 5, 5, 5], [[2, 0, 0, 0], [0, 2, 0, 0], [0, 0, 2, 0], [0, 0, 0, 3]]),
            'z5_4_40': ([5, 5, 5, 5], [[2, 0, 0, 0], [0, 2, 0, 0], [0, 0, 2, 0], [0, 0, 0, 2]]),
            'z125x5_57': ([125, 5], [[57, 0], [0, 2]]),
            'z25x25_7': ([25, 25], [[7, 0], [0, 7]]),
        }
        for name, (mods, A) in cases.items():
            TP, phi = abelian_auto(mods, A)
            if not fpf_ok(phi, len(TP)):
                print('not fixed-point-free', name); continue
            T = semidirect(TP, phi)
            write_one(name, T, f'abelian {mods} A={A}', out)
    if kind == 'heis':
        # Heis(5) x Z_5 with phi = conjugation by diag on the Heisenberg part, w -> lam w
        TPh = GR.table('heis 5 x cyc 5')
        coords = coords_heis(5, 5)
        Pn = len(coords)
        idx = index_of(coords)
        for (al, be, lam) in [(2, 2, 2), (3, 3, 3), (2, 2, 3), (3, 3, 2), (1, 2, 2), (2, 1, 2)]:
            perm = np.empty(Pn, dtype=np.int64)
            for i, (x, y, z, w) in enumerate(coords):
                perm[i] = idx[((al * x) % 5, (be * y) % 5, (al * be * z) % 5, (lam * w) % 5)]
            try:
                check_automorphism(TPh, perm)
            except AssertionError:
                print('not automorphism', al, be, lam); continue
            if not fpf_ok(perm, Pn):
                print('heis not fpf', al, be, lam)
            T = semidirect(TPh, perm)
            write_one(f'heis5x5_{al}{be}{lam}', T, f'Heis(5) x Z_5 phi=diag({al},{be}), w->{lam}w', out)
    if kind == 'abel':
        specs = [[625], [125, 5], [25, 25], [25, 5, 5], [5, 5, 5, 5]]
        seen = {}
        for mods in specs:
            r = len(mods)
            mx = max(mods)
            cnt = 0
            tries = 0
            while cnt < nsamp and tries < 40 * nsamp:
                tries += 1
                A = rng.integers(0, mx, size=(r, r))
                try:
                    TP, phi = abelian_auto(mods, A.tolist())
                except AssertionError:
                    continue
                Pn = len(TP)
                pw = np.arange(Pn)
                for _ in range(4):
                    pw = phi[pw]
                if not (pw == np.arange(Pn)).all():
                    continue
                if not fpf_ok(phi, Pn):
                    continue
                cnt += 1
                T = semidirect(TP, phi)
                inv = invariants(T)
                key = (tuple(sorted(inv['hist'].items())), inv['centre'], inv['ab'])
                if key in seen:
                    continue
                seen[key] = 1
                gc = gen_count(T, trials=10)
                if gc[1] < 0.5:
                    continue
                name = 'ab_' + 'x'.join(map(str, mods)) + '_' + str(len(seen))
                write_one(name, T, f'abelian {mods} A={A.tolist()}', out)
        print('distinct', len(seen))
    out.close()
